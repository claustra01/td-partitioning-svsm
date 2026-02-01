// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2024 Intel Corporation.

use super::gmem::{copy_from_gpa, gva2gpa, GuestMemAccessCode};
use super::percpu::this_vcpu;
use super::utils::TdpVmId;
use crate::address::GuestVirtAddr;
use crate::locking::SpinLock;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

const LINUX_BANNER_PREFIX: &[u8] = b"Linux version";
const LINUX_BANNER_MAX_LEN: usize = 256;
// Pattern: ffffffff***00a20 where *** ranges 0x000..0xfff (KASLRオフセット想定)
const LINUX_BANNER_PATTERN_BASE: u64 = 0xffffffff00000a20;
const LINUX_BANNER_PATTERN_STEP: u64 = 1 << 20;
const LINUX_BANNER_PATTERN_MAX: u16 = 0x0fff;
pub const TCP_HASHINFO_OFFSET: u64 = 0x2016540; // tcp_hashinfo - linux banner @Linux version 5.14.0-620.el9.x86_64

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
        let len = core::cmp::min(src.len(), LINUX_BANNER_MAX_LEN);
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

pub fn maybe_resolve_linux_banner(vm_id: TdpVmId) {
    if LINUX_BANNER_GVA.load(Ordering::Acquire) != 0 {
        return;
    }

    if LINUX_BANNER_SCAN_IN_PROGRESS.swap(true, Ordering::AcqRel) {
        return;
    }

    let mut found = false;
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

            let buf = match copy_from_gpa::<[u8; LINUX_BANNER_MAX_LEN]>(gpa) {
                Ok(buf) => buf,
                Err(_) => continue,
            };

            if let Some(len) = linux_banner_len(&buf) {
                LINUX_BANNER_GVA.store(gva_val, Ordering::Relaxed);
                LINUX_BANNER_GPA.store(u64::from(gpa), Ordering::Relaxed);

                let mut cache = LINUX_BANNER_CACHE.lock();
                cache.set(&buf[..len]);

                if let Some(tcp_gva_val) = gva_val.checked_add(TCP_HASHINFO_OFFSET) {
                    TCP_HASHINFO_GVA.store(tcp_gva_val, Ordering::Relaxed);
                    if let Ok(Some(tcp_gpa)) =
                        gva2gpa(ctx, GuestVirtAddr::from(tcp_gva_val), GuestMemAccessCode::empty())
                    {
                        TCP_HASHINFO_GPA.store(u64::from(tcp_gpa), Ordering::Relaxed);
                    }
                }

                found = true;
                break;
            }
        }
    }

    if !found {
        LINUX_BANNER_GVA.store(0, Ordering::Relaxed);
        LINUX_BANNER_GPA.store(0, Ordering::Relaxed);
        TCP_HASHINFO_GVA.store(0, Ordering::Relaxed);
        TCP_HASHINFO_GPA.store(0, Ordering::Relaxed);
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
