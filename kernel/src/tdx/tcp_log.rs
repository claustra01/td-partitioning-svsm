// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2024 Intel Corporation.

extern crate alloc;

use super::gctx::GuestCpuContext;
use super::gmem::{accept_guest_mem, gva2gpa, GuestMemAccessCode};
use super::guest_symbols::tcp_hashinfo_gva;
use super::percpu::this_vcpu;
use super::utils::TdpVmId;
use crate::address::{Address, GuestVirtAddr};
use crate::cpu::cpuid::cpuid;
use crate::cpu::msr::rdtsc;
use crate::locking::SpinLock;
use crate::mm::guestmem::GuestMemMap;
use crate::types::PAGE_SIZE;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::min;
use core::sync::atomic::{AtomicU64, Ordering};

// Offsets derived from memo/pahole.log (Linux 5.14.0-620.el9.x86_64)
const INET_HASHINFO_EHASH_OFFSET: usize = 0;
const INET_HASHINFO_EHASH_MASK_OFFSET: usize = 16;
const INET_EHASH_BUCKET_SIZE: usize = 8;
const INET_EHASH_BUCKET_CHAIN_OFFSET: usize = 0;

const HLIST_NULLS_NODE_NEXT_OFFSET: usize = 0;
const SOCK_COMMON_DADDR_OFFSET: usize = 0;
const SOCK_COMMON_RCV_SADDR_OFFSET: usize = 4;
const SOCK_COMMON_DPORT_OFFSET: usize = 12;
const SOCK_COMMON_NUM_OFFSET: usize = 14;
const SOCK_COMMON_FAMILY_OFFSET: usize = 16;
const SOCK_COMMON_STATE_OFFSET: usize = 18;
const SOCK_COMMON_NULLS_NODE_OFFSET: usize = 104;

const AF_INET: u16 = 2;
const TCP_ESTABLISHED: u8 = 1;
const TCP_TIME_WAIT: u8 = 6;

const HLIST_NULLS_MARKER_BIT: u64 = 0x1;
const MAX_BUCKET_NODES: usize = 64;
const MAX_LOGGED_SOCKS: usize = 1024;
const TCP_SCAN_INTERVAL_SECS: u64 = 10;

static LAST_TCP_SCAN_TSC: AtomicU64 = AtomicU64::new(0);
static TCP_TSC_HZ_CACHE: AtomicU64 = AtomicU64::new(0);
static LOGGED_SOCKS: SpinLock<LoggedSockCache> = SpinLock::new(LoggedSockCache::new());

struct LoggedSockCache {
    entries: Vec<u64>,
    next: usize,
}

impl LoggedSockCache {
    const fn new() -> Self {
        Self {
            entries: Vec::new(),
            next: 0,
        }
    }

    fn contains(&self, sock_ptr: u64) -> bool {
        self.entries.iter().any(|entry| *entry == sock_ptr)
    }

    fn insert(&mut self, sock_ptr: u64) {
        if self.entries.len() < MAX_LOGGED_SOCKS {
            self.entries.push(sock_ptr);
            return;
        }

        if self.next >= self.entries.len() {
            self.next = 0;
        }
        self.entries[self.next] = sock_ptr;
        self.next = (self.next + 1) % MAX_LOGGED_SOCKS;
    }
}

fn tsc_hz() -> u64 {
    let cached = TCP_TSC_HZ_CACHE.load(Ordering::Relaxed);
    if cached != 0 {
        return cached;
    }

    let max_leaf = cpuid(0x0).map(|r| r.eax).unwrap_or(0);
    let mut hz = 0;

    if max_leaf >= 0x15 {
        if let Some(leaf) = cpuid(0x15) {
            let denom = leaf.eax as u64;
            let numer = leaf.ebx as u64;
            let crystal = leaf.ecx as u64;
            if denom != 0 && numer != 0 && crystal != 0 {
                hz = crystal.saturating_mul(numer) / denom;
            }
        }
    }

    if hz == 0 && max_leaf >= 0x16 {
        if let Some(leaf) = cpuid(0x16) {
            let mhz = (leaf.eax & 0xffff) as u64;
            if mhz != 0 {
                hz = mhz.saturating_mul(1_000_000);
            }
        }
    }

    if hz != 0 {
        TCP_TSC_HZ_CACHE.store(hz, Ordering::Relaxed);
    }

    hz
}

pub fn maybe_log_tcp_connections(vm_id: TdpVmId) {
    let hz = tsc_hz();
    if hz == 0 {
        return;
    }

    let now = rdtsc();
    let last = LAST_TCP_SCAN_TSC.load(Ordering::Relaxed);
    if now.wrapping_sub(last) < hz.saturating_mul(TCP_SCAN_INTERVAL_SECS) {
        return;
    }
    if LAST_TCP_SCAN_TSC
        .compare_exchange(last, now, Ordering::Relaxed, Ordering::Relaxed)
        .is_err()
    {
        return;
    }

    let tcp_hashinfo = match tcp_hashinfo_gva() {
        Some(gva) => gva,
        None => return,
    };

    let vcpu = this_vcpu(vm_id);
    if vcpu.get_ctx().get_cr3() == 0 {
        return;
    }
    let ctx = vcpu.get_ctx();

    let ehash_ptr = match read_guest_u64(ctx, tcp_hashinfo + INET_HASHINFO_EHASH_OFFSET) {
        Some(ptr) => ptr,
        None => return,
    };
    if ehash_ptr == 0 {
        return;
    }
    let ehash_mask = match read_guest_u32(ctx, tcp_hashinfo + INET_HASHINFO_EHASH_MASK_OFFSET) {
        Some(mask) => mask,
        None => return,
    };
    let ehash_size = ehash_mask.wrapping_add(1);
    if ehash_size == 0 {
        return;
    }

    for bucket_index in 0..ehash_size {
        scan_bucket(ctx, ehash_ptr, bucket_index);
    }
}

fn scan_bucket(ctx: &GuestCpuContext, ehash_ptr: u64, bucket_index: u32) {
    let bucket_gva =
        GuestVirtAddr::from(ehash_ptr + (bucket_index as u64) * INET_EHASH_BUCKET_SIZE as u64);
    let mut node_ptr = match read_guest_u64(ctx, bucket_gva + INET_EHASH_BUCKET_CHAIN_OFFSET) {
        Some(ptr) => ptr,
        None => return,
    };

    let mut scanned = 0;
    while node_ptr != 0
        && (node_ptr & HLIST_NULLS_MARKER_BIT) == 0
        && scanned < MAX_BUCKET_NODES
    {
        let sock_ptr = match node_ptr.checked_sub(SOCK_COMMON_NULLS_NODE_OFFSET as u64) {
            Some(ptr) => ptr,
            None => break,
        };
        let sock_gva = GuestVirtAddr::from(sock_ptr);
        try_log_sock(ctx, bucket_index, sock_ptr, sock_gva);

        let node_gva = GuestVirtAddr::from(node_ptr);
        node_ptr = match read_guest_u64(ctx, node_gva + HLIST_NULLS_NODE_NEXT_OFFSET) {
            Some(ptr) => ptr,
            None => break,
        };
        scanned += 1;
    }
}

fn try_log_sock(ctx: &GuestCpuContext, bucket_index: u32, sock_ptr: u64, sock_gva: GuestVirtAddr) {
    if sock_already_logged(sock_ptr) {
        return;
    }

    let family = match read_guest_u16(ctx, sock_gva + SOCK_COMMON_FAMILY_OFFSET) {
        Some(val) => val,
        None => return,
    };
    if family != AF_INET {
        return;
    }

    let state = match read_guest_u8(ctx, sock_gva + SOCK_COMMON_STATE_OFFSET) {
        Some(val) => val,
        None => return,
    };
    if state != TCP_ESTABLISHED && state != TCP_TIME_WAIT {
        return;
    }

    let daddr = match read_guest_be32(ctx, sock_gva + SOCK_COMMON_DADDR_OFFSET) {
        Some(val) => val,
        None => return,
    };
    let saddr = match read_guest_be32(ctx, sock_gva + SOCK_COMMON_RCV_SADDR_OFFSET) {
        Some(val) => val,
        None => return,
    };
    let dport = match read_guest_be16(ctx, sock_gva + SOCK_COMMON_DPORT_OFFSET) {
        Some(val) => val,
        None => return,
    };
    let sport = match read_guest_u16(ctx, sock_gva + SOCK_COMMON_NUM_OFFSET) {
        Some(val) => val,
        None => return,
    };

    log_sock_tuple(bucket_index, sock_ptr, state, saddr, sport, daddr, dport);
    mark_sock_logged(sock_ptr);
}

fn log_sock_tuple(
    bucket_index: u32,
    sock_ptr: u64,
    state: u8,
    saddr: u32,
    sport: u16,
    daddr: u32,
    dport: u16,
) {
    let src_ip = ipv4_to_string(saddr);
    let dst_ip = ipv4_to_string(daddr);
    log::info!(
        "L2VM TCP: bucket={} sock=0x{:x} state={} {}:{} -> {}:{}",
        bucket_index,
        sock_ptr,
        state,
        src_ip,
        sport,
        dst_ip,
        dport
    );
}

fn ipv4_to_string(addr_be: u32) -> String {
    let bytes = addr_be.to_be_bytes();
    format!("{}.{}.{}.{}", bytes[0], bytes[1], bytes[2], bytes[3])
}

fn sock_already_logged(sock_ptr: u64) -> bool {
    let cache = LOGGED_SOCKS.lock();
    cache.contains(sock_ptr)
}

fn mark_sock_logged(sock_ptr: u64) {
    let mut cache = LOGGED_SOCKS.lock();
    if cache.contains(sock_ptr) {
        return;
    }
    cache.insert(sock_ptr);
}

fn read_guest_u64(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u64> {
    let mut buf = [0u8; 8];
    read_guest_slice(ctx, gva, &mut buf)?;
    Some(u64::from_le_bytes(buf))
}

fn read_guest_u32(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u32> {
    let mut buf = [0u8; 4];
    read_guest_slice(ctx, gva, &mut buf)?;
    Some(u32::from_le_bytes(buf))
}

fn read_guest_u16(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u16> {
    let mut buf = [0u8; 2];
    read_guest_slice(ctx, gva, &mut buf)?;
    Some(u16::from_le_bytes(buf))
}

fn read_guest_u8(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u8> {
    let mut buf = [0u8; 1];
    read_guest_slice(ctx, gva, &mut buf)?;
    Some(buf[0])
}

fn read_guest_be16(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u16> {
    let mut buf = [0u8; 2];
    read_guest_slice(ctx, gva, &mut buf)?;
    Some(u16::from_be_bytes(buf))
}

fn read_guest_be32(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u32> {
    let mut buf = [0u8; 4];
    read_guest_slice(ctx, gva, &mut buf)?;
    Some(u32::from_be_bytes(buf))
}

fn read_guest_slice(ctx: &GuestCpuContext, gva: GuestVirtAddr, buf: &mut [u8]) -> Option<()> {
    let mut remaining = buf.len();
    let mut current_gva = gva;
    let mut offset = 0;

    while remaining > 0 {
        let gpa = match gva2gpa(ctx, current_gva, GuestMemAccessCode::empty()) {
            Ok(Some(gpa)) => gpa,
            _ => return None,
        };

        let chunk = min(remaining, PAGE_SIZE - current_gva.page_offset());
        let aligned_start = gpa.page_align();
        let aligned_end = (gpa + chunk).page_align_up();
        if accept_guest_mem(aligned_start, aligned_end).is_err() {
            return None;
        }

        let map = GuestMemMap::<u8>::new(gpa, chunk).ok()?;
        let ptr = map.virt_addr().as_ptr::<u8>();
        let slice = unsafe { core::slice::from_raw_parts(ptr, chunk) };
        buf[offset..offset + chunk].copy_from_slice(slice);

        remaining -= chunk;
        offset += chunk;
        current_gva = current_gva + chunk;
    }

    Some(())
}
