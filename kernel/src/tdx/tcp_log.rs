// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2024 Intel Corporation.

use super::gctx::GuestCpuContext;
use super::guest_symbols::{read_guest_virt_slice, tcp_hashinfo_gva};
use super::percpu::this_vcpu;
use super::utils::TdpVmId;
use crate::address::GuestVirtAddr;
use crate::locking::SpinLock;
use core::sync::atomic::{AtomicBool, Ordering};

// Offsets derived from memo/pahole.log (Linux 6.12.0-233.el10.x86_64)
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

static TCP_HASHINFO_LOGGED: AtomicBool = AtomicBool::new(false);
static LOGGED_SOCKS: SpinLock<LoggedSockCache> = SpinLock::new(LoggedSockCache::new());

struct LoggedSockCache {
    entries: [u64; MAX_LOGGED_SOCKS],
    len: usize,
    next: usize,
}

impl LoggedSockCache {
    const fn new() -> Self {
        Self {
            entries: [0; MAX_LOGGED_SOCKS],
            len: 0,
            next: 0,
        }
    }

    fn contains(&self, sock_ptr: u64) -> bool {
        self.entries[..self.len].contains(&sock_ptr)
    }

    fn insert_if_new(&mut self, sock_ptr: u64) -> bool {
        if self.contains(sock_ptr) {
            return false;
        }

        if self.len < MAX_LOGGED_SOCKS {
            self.entries[self.len] = sock_ptr;
            self.len += 1;
            return true;
        }

        self.entries[self.next] = sock_ptr;
        self.next = (self.next + 1) % MAX_LOGGED_SOCKS;
        true
    }
}

pub fn maybe_log_tcp_connections(vm_id: TdpVmId) {
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
        Some(ptr) if ptr != 0 => ptr,
        _ => return,
    };
    let ehash_mask = match read_guest_u32(ctx, tcp_hashinfo + INET_HASHINFO_EHASH_MASK_OFFSET) {
        Some(mask) => mask,
        None => return,
    };
    let ehash_size = match ehash_mask.checked_add(1) {
        Some(size) if size != 0 => size,
        _ => return,
    };

    if !TCP_HASHINFO_LOGGED.swap(true, Ordering::AcqRel) {
        // log::info!(
        //     "guest tcp hashinfo: tcp_hashinfo_gva={:#x} ehash={:#x} ehash_mask={:#x} ehash_size={}",
        //     u64::from(tcp_hashinfo),
        //     ehash_ptr,
        //     ehash_mask,
        //     ehash_size
        // );
    }

    for bucket_index in 0..ehash_size {
        scan_bucket(ctx, ehash_ptr, bucket_index);
    }
}

fn scan_bucket(ctx: &GuestCpuContext, ehash_ptr: u64, bucket_index: u32) {
    let bucket_offset = match (bucket_index as u64).checked_mul(INET_EHASH_BUCKET_SIZE as u64) {
        Some(offset) => offset,
        None => return,
    };
    let bucket_gva = match ehash_ptr
        .checked_add(bucket_offset)
        .and_then(|addr| addr.checked_add(INET_EHASH_BUCKET_CHAIN_OFFSET as u64))
    {
        Some(addr) => GuestVirtAddr::from(addr),
        None => return,
    };
    let mut node_ptr = match read_guest_u64(ctx, bucket_gva) {
        Some(ptr) => ptr,
        None => return,
    };

    let mut scanned = 0;
    while node_ptr != 0 && (node_ptr & HLIST_NULLS_MARKER_BIT) == 0 && scanned < MAX_BUCKET_NODES {
        let sock_ptr = match node_ptr.checked_sub(SOCK_COMMON_NULLS_NODE_OFFSET as u64) {
            Some(ptr) => ptr,
            None => break,
        };
        try_log_sock(ctx, bucket_index, sock_ptr);

        node_ptr = match read_guest_u64(
            ctx,
            GuestVirtAddr::from(node_ptr + HLIST_NULLS_NODE_NEXT_OFFSET as u64),
        ) {
            Some(ptr) => ptr,
            None => break,
        };
        scanned += 1;
    }
}

fn try_log_sock(ctx: &GuestCpuContext, _bucket_index: u32, sock_ptr: u64) {
    let sock_gva = GuestVirtAddr::from(sock_ptr);

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
    let _dport = match read_guest_be16(ctx, sock_gva + SOCK_COMMON_DPORT_OFFSET) {
        Some(val) => val,
        None => return,
    };
    let _sport = match read_guest_u16(ctx, sock_gva + SOCK_COMMON_NUM_OFFSET) {
        Some(val) => val,
        None => return,
    };

    if !remember_sock(sock_ptr) {
        return;
    }

    let _src = saddr.to_be_bytes();
    let _dst = daddr.to_be_bytes();
    // log::info!(
    //     "guest tcp: bucket={} sock={:#x} state={} {}.{}.{}.{}:{} -> {}.{}.{}.{}:{}",
    //     _bucket_index,
    //     sock_ptr,
    //     state,
    //     _src[0],
    //     _src[1],
    //     _src[2],
    //     _src[3],
    //     _sport,
    //     _dst[0],
    //     _dst[1],
    //     _dst[2],
    //     _dst[3],
    //     _dport
    // );
}

fn remember_sock(sock_ptr: u64) -> bool {
    let mut cache = LOGGED_SOCKS.lock();
    cache.insert_if_new(sock_ptr)
}

fn read_guest_u64(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u64> {
    let mut buf = [0u8; 8];
    read_guest_virt_slice(ctx, gva, &mut buf)?;
    Some(u64::from_le_bytes(buf))
}

fn read_guest_u32(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u32> {
    let mut buf = [0u8; 4];
    read_guest_virt_slice(ctx, gva, &mut buf)?;
    Some(u32::from_le_bytes(buf))
}

fn read_guest_u16(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u16> {
    let mut buf = [0u8; 2];
    read_guest_virt_slice(ctx, gva, &mut buf)?;
    Some(u16::from_le_bytes(buf))
}

fn read_guest_u8(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u8> {
    let mut buf = [0u8; 1];
    read_guest_virt_slice(ctx, gva, &mut buf)?;
    Some(buf[0])
}

fn read_guest_be16(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u16> {
    let mut buf = [0u8; 2];
    read_guest_virt_slice(ctx, gva, &mut buf)?;
    Some(u16::from_be_bytes(buf))
}

fn read_guest_be32(ctx: &GuestCpuContext, gva: GuestVirtAddr) -> Option<u32> {
    let mut buf = [0u8; 4];
    read_guest_virt_slice(ctx, gva, &mut buf)?;
    Some(u32::from_be_bytes(buf))
}
