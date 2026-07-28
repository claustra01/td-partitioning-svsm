// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2024 Intel Corporation.

use super::gctx::GuestCpuContext;
use super::gmem::{accept_guest_mem, gva2gpa, GuestMemAccessCode};
use super::percpu::this_vcpu;
use super::utils::TdpVmId;
use crate::address::{Address, GuestVirtAddr};
use crate::locking::SpinLock;
use crate::mm::guestmem::GuestMemMap;
use crate::types::PAGE_SIZE;
use core::cmp::min;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

const LINUX_BANNER_PREFIX: &[u8] = b"Linux version";
const LINUX_BANNER_MAX_LEN: usize = 256;
// Pattern: ffffffff***5a0c0 where *** ranges 0x000..0xfff (KASLRオフセット想定)
const LINUX_BANNER_PATTERN_BASE: u64 = 0xffffffff0005a0c0;
const LINUX_BANNER_PATTERN_STEP: u64 = 1 << 20;
const LINUX_BANNER_PATTERN_MAX: u16 = 0x0fff;
pub const TCP_HASHINFO_OFFSET: u64 = 0x204C940; // tcp_hashinfo - linux banner @Linux version 6.12.0-233.el10.x86_64

static LINUX_BANNER_SCAN_IN_PROGRESS: AtomicBool = AtomicBool::new(false);
static LINUX_BANNER_GVA: AtomicU64 = AtomicU64::new(0);
static LINUX_BANNER_GPA: AtomicU64 = AtomicU64::new(0);
static TCP_HASHINFO_GVA: AtomicU64 = AtomicU64::new(0);
static TCP_HASHINFO_GPA: AtomicU64 = AtomicU64::new(0);
static LINUX_BANNER_CACHE: SpinLock<BannerCache> = SpinLock::new(BannerCache::new());

struct BannerCache {
    bytes: [u8; LINUX_BANNER_MAX_LEN],
    len: usize,
}

impl BannerCache {
    const fn new() -> Self {
        Self {
            bytes: [0; LINUX_BANNER_MAX_LEN],
            len: 0,
        }
    }

    fn set(&mut self, src: &[u8]) {
        let len = min(src.len(), LINUX_BANNER_MAX_LEN);
        self.bytes[..len].copy_from_slice(&src[..len]);
        self.len = len;
    }
}

#[derive(Clone, Copy)]
pub struct BannerSnapshot {
    pub banner_gva: u64,
    pub banner_gpa: u64,
    pub tcp_hashinfo_gva: u64,
    pub tcp_hashinfo_gpa: u64,
    bytes: [u8; LINUX_BANNER_MAX_LEN],
    len: usize,
}

impl BannerSnapshot {
    pub fn banner_str(&self) -> &str {
        if self.len == 0 {
            "<unknown>"
        } else {
            core::str::from_utf8(&self.bytes[..self.len]).unwrap_or("<non-utf8>")
        }
    }
}

fn is_printable_ascii(byte: u8) -> bool {
    matches!(byte, 0x20..=0x7e | b'\n' | b'\r' | b'\t')
}

fn linux_banner_len(buf: &[u8]) -> Option<usize> {
    if !buf.starts_with(LINUX_BANNER_PREFIX) {
        return None;
    }

    let mut len = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
    if len == 0 {
        return None;
    }

    if !buf[..len].iter().all(|&b| is_printable_ascii(b)) {
        return None;
    }

    while len > 0 && matches!(buf[len - 1], b'\n' | b'\r') {
        len -= 1;
    }

    if len == 0 {
        None
    } else {
        Some(len)
    }
}

pub fn read_guest_virt_slice(
    ctx: &GuestCpuContext,
    gva: GuestVirtAddr,
    buf: &mut [u8],
) -> Option<()> {
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

pub fn maybe_resolve_linux_banner(vm_id: TdpVmId) {
    if LINUX_BANNER_GVA.load(Ordering::Acquire) != 0 {
        return;
    }

    if LINUX_BANNER_SCAN_IN_PROGRESS.swap(true, Ordering::AcqRel) {
        return;
    }

    let vcpu = this_vcpu(vm_id);
    if vcpu.get_ctx().get_cr3() != 0 {
        let ctx = vcpu.get_ctx();
        for idx in 0..=LINUX_BANNER_PATTERN_MAX {
            let gva_val = LINUX_BANNER_PATTERN_BASE + (u64::from(idx) * LINUX_BANNER_PATTERN_STEP);
            let gva = GuestVirtAddr::from(gva_val);
            let gpa = match gva2gpa(ctx, gva, GuestMemAccessCode::empty()) {
                Ok(Some(gpa)) => gpa,
                _ => continue,
            };

            let mut buf = [0u8; LINUX_BANNER_MAX_LEN];
            if read_guest_virt_slice(ctx, gva, &mut buf).is_none() {
                continue;
            }

            if let Some(len) = linux_banner_len(&buf) {
                let mut tcp_hashinfo_gva = 0;
                let mut tcp_hashinfo_gpa = 0;
                if let Some(tcp_gva_val) = gva_val.checked_add(TCP_HASHINFO_OFFSET) {
                    tcp_hashinfo_gva = tcp_gva_val;
                    if let Ok(Some(tcp_gpa)) = gva2gpa(
                        ctx,
                        GuestVirtAddr::from(tcp_gva_val),
                        GuestMemAccessCode::empty(),
                    ) {
                        tcp_hashinfo_gpa = u64::from(tcp_gpa);
                    }
                }

                {
                    let mut cache = LINUX_BANNER_CACHE.lock();
                    cache.set(&buf[..len]);
                }

                TCP_HASHINFO_GVA.store(tcp_hashinfo_gva, Ordering::Relaxed);
                TCP_HASHINFO_GPA.store(tcp_hashinfo_gpa, Ordering::Relaxed);
                LINUX_BANNER_GPA.store(u64::from(gpa), Ordering::Relaxed);
                LINUX_BANNER_GVA.store(gva_val, Ordering::Release);

                let snapshot = banner_snapshot();
                log::info!(
                    "guest symbols: linux_banner_gva={:#x} linux_banner_gpa={:#x} tcp_hashinfo_gva={:#x} tcp_hashinfo_gpa={:#x} linux_banner=\"{}\"",
                    snapshot.banner_gva,
                    snapshot.banner_gpa,
                    snapshot.tcp_hashinfo_gva,
                    snapshot.tcp_hashinfo_gpa,
                    snapshot.banner_str()
                );
                break;
            }
        }
    }

    LINUX_BANNER_SCAN_IN_PROGRESS.store(false, Ordering::Release);
}

pub fn banner_snapshot() -> BannerSnapshot {
    let cache = LINUX_BANNER_CACHE.lock();
    BannerSnapshot {
        banner_gva: LINUX_BANNER_GVA.load(Ordering::Relaxed),
        banner_gpa: LINUX_BANNER_GPA.load(Ordering::Relaxed),
        tcp_hashinfo_gva: TCP_HASHINFO_GVA.load(Ordering::Relaxed),
        tcp_hashinfo_gpa: TCP_HASHINFO_GPA.load(Ordering::Relaxed),
        bytes: cache.bytes,
        len: cache.len,
    }
}

pub fn tcp_hashinfo_gva() -> Option<GuestVirtAddr> {
    let gva = TCP_HASHINFO_GVA.load(Ordering::Acquire);
    if gva == 0 {
        None
    } else {
        Some(GuestVirtAddr::from(gva))
    }
}
