"""Disk-cached local angles theta_p per curve, built once at C speed.

The profiled bottleneck of every large-NMAX bank build was ap_general's O(p)
point count per prime (~1e11 element-ops at NMAX 1.5e6), recomputed per bank.
This module replaces it: PARI ellaplist computes all a_p to NMAX in seconds;
theta_p = acos(clamp(a_p/sqrt(p))/2) is stored as a float64 array indexed by
p (O(1) lookup, ~16 MB at 2e6, memory-mapped-friendly .npy on disk).

Build (once):   sage -python theta_cache.py build 2000000
Use (anywhere): from theta_cache import theta_table; TH = theta_table("11a1")
                then TH[p] is theta_p (NaN at bad primes / p > nmax).
"""
import os, sys
import numpy as np

DIR = os.path.dirname(os.path.abspath(__file__))
CURVES = {"11a1": [0, -1, 1, -10, -20], "37a1": [0, 0, 1, -1, 0],
          "53a1": [1, -1, 1, 0, 0], "61a1": [1, 0, 0, -2, 1]}
LEVELS = {"11a1": 11, "37a1": 37, "53a1": 53, "61a1": 61}


def _path(lab):
    return os.path.join(DIR, f"theta_{lab}.npy")


def build(nmax):
    from sage.all import EllipticCurve
    sieve = np.ones(nmax + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(nmax ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    ps = np.nonzero(sieve)[0].astype(np.int64)
    for lab, ainv in CURVES.items():
        E = EllipticCurve(ainv)
        ap = np.array(E.aplist(nmax), dtype=np.float64)
        assert len(ap) == len(ps), (len(ap), len(ps))
        th = np.full(nmax + 1, np.nan)
        b = np.clip(ap / np.sqrt(ps.astype(np.float64)), -2.0, 2.0)
        th[ps] = np.arccos(b / 2.0)
        th[LEVELS[lab]] = np.nan
        np.save(_path(lab), th)
        print(f"{lab}: {len(ps)} primes to {nmax} -> {_path(lab)} "
              f"({th.nbytes / 1e6:.0f} MB)", flush=True)


def theta_table(lab):
    return np.load(_path(lab), mmap_mode="r")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "build":
        build(int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000)
