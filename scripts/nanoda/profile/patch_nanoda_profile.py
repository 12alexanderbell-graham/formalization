#!/usr/bin/env python3
"""Measurement only (run 2026-11-20T1228Z; never used by the judge): patch a nanoda_lib checkout so that each
worker prints the wall time of every declaration it checks that took at least NANODA_PROFILE_MIN_US microseconds
(default 20000), as `ndprof <microseconds> <name>` on stderr. The check itself is unchanged: the same
`check_declar` call, timed. Used by .github/workflows/nanoda-profile.yml to find which modules make a nanoda
shard slow, so that nanoda can get its own shard assignment (scripts/nanoda/shard_assignment.txt is balanced on
leanchecker times, while nanoda shard 1 took 3837 s against 1878 s for shard 0 at equal declaration counts).
Usage: patch_nanoda_profile.py <nanoda_lib dir>
"""
import pathlib, sys

tc = pathlib.Path(sys.argv[1]) / "src" / "tc.rs"
s = tc.read_text()
old = """                                    if let Some((_, declar)) = self.declars.get_index(idx) {
                                        self.check_declar(declar);
                                    } else {"""
new = """                                    if let Some((_, declar)) = self.declars.get_index(idx) {
                                        let ndprof_t0 = std::time::Instant::now();
                                        self.check_declar(declar);
                                        let ndprof_us = ndprof_t0.elapsed().as_micros();
                                        let ndprof_min: u128 = std::env::var("NANODA_PROFILE_MIN_US").ok().and_then(|v| v.parse().ok()).unwrap_or(20000);
                                        if ndprof_us >= ndprof_min {
                                            let ndprof_name = self.with_ctx(|ctx| format!("{:?}", ctx.debug_print(declar.info().name)));
                                            eprintln!("ndprof {} {}", ndprof_us, ndprof_name);
                                        }
                                    } else {"""
if s.count(old) != 1:
    sys.exit("patch_nanoda_profile: the worker loop of src/tc.rs is not the pinned one; refusing to patch")
tc.write_text(s.replace(old, new))
print("patched", tc)
