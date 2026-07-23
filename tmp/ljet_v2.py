"""Chunked L-jet v2: segment-local a_n (no big array, no disk), arbitrary B.

Per segment [s, e): rem = n; for each prime p <= sqrt(B): extract the full
p-power from rem by vectorized division, multiply c by a_{p^v} (Hecke recurrence
per p).  Afterwards rem is 1 or the unique prime factor > sqrt(B): multiply by
a_p via vectorized searchsorted into the parallel-ellap table.  Weighted sums
per segment as in v1 (incomplete-Gamma Taylor splines).  Order-independent,
segment-local: RAM ~ 8GB at B = 6.3e9.

Gates: identical formula to v1 (validated to 2.5e-11 against PARI at rank 8);
v2 must reproduce v1 on 389a and r8 with forced multi-segmenting before r10.
Usage: sage -python ljet_v2.py {389a|r8|r9|r10} [segsize_log2]
"""
import math
import os
import sys
import time

import numpy as np
from scipy.interpolate import splev, splrep

CACHE = "/Users/samuellavery/.claude/jobs/18a3f704/tmp"
JMAX = 12
UGRID_N = 1 << 20
ULO, UHI = math.log(1e-10), math.log(120.0)

CURVES = {
    "389a": dict(ainvs=[0, 1, 1, -2, 0], N=389, eps=1, B=4000),
    "r8": dict(ainvs=[1, -1, 0, -106384, 13075804], N=249649566346838,
               eps=1, B=155_000_000),
    "r9": dict(ainvs=[1, -1, 0, -135004, 97151644], N=32107342006814614,
               eps=-1, B=1_600_000_000),
    # r10 preset appended after the arithmetic-side job reports
}
R10_FILE = f"{CACHE}/r10_preset.py"
if os.path.exists(R10_FILE):
    exec(open(R10_FILE).read())


def build_gk_splines():
    u = np.linspace(ULO, UHI, UGRID_N + 1)
    h = u[1] - u[0]
    splines = []
    for k in range(JMAX):
        hk = u ** k * np.exp(u - np.exp(u)) / math.factorial(k)
        f = hk[::-1]
        cs = np.zeros_like(f)
        cs[2::2] = (f[0:-2:2] + 4.0 * f[1:-1:2] + f[2::2]) * (h / 3.0)
        cs[2::2] = np.cumsum(cs[2::2])
        cs[1::2] = cs[0:-1:2] + (f[0:-1:2] + f[1::2]) * (h / 2.0)
        splines.append(splrep(u, cs[::-1], k=3, s=0))
    return splines


def primes_upto(B):
    sieve = np.ones(B // 2 + 1, dtype=bool)
    sieve[0] = False
    for i in range(1, int(B ** 0.5) // 2 + 1):
        if sieve[i]:
            p = 2 * i + 1
            sieve[(p * p) // 2::p] = False
    return np.concatenate(([2], 2 * np.nonzero(sieve)[0] + 1)).astype(np.int64)


def _ap_worker(args):
    ainvs, lo, hi, wid = args
    from cypari2 import Pari
    pari = Pari()
    pari.allocatemem(500_000_000)
    E = pari.ellinit(ainvs)
    base = primes_upto(int(hi ** 0.5) + 1)
    seg = np.ones(hi - lo, dtype=bool)
    for p in base:
        start = max(p * p, ((lo + p - 1) // p) * p)
        if start < hi:
            seg[start - lo::p] = False
    if lo <= 2:
        seg[: 2 - lo] = False
    ps = np.nonzero(seg)[0] + lo
    ap = np.empty(len(ps), dtype=np.int32)
    ellap = pari.ellap
    for i, p in enumerate(ps):
        ap[i] = int(ellap(E, int(p)))
    return wid, ps.astype(np.int64), ap


def get_ap(tag, ainvs, B, nproc=8):
    fp, fa = f"{CACHE}/ps_{tag}.npy", f"{CACHE}/ap_{tag}.npy"
    if os.path.exists(fa):
        return np.load(fp), np.load(fa)
    t0 = time.time()
    bounds = np.linspace(2, B + 1, nproc + 1).astype(np.int64)
    jobs = [(ainvs, int(bounds[i]), int(bounds[i + 1]), i) for i in range(nproc)]
    if B < 10 ** 6:
        results = [_ap_worker(j) for j in jobs]
    else:
        import multiprocessing as mp_
        with mp_.get_context("fork").Pool(nproc) as pool:
            results = pool.map(_ap_worker, jobs)
    results.sort()
    ps = np.concatenate([r[1] for r in results])
    ap = np.concatenate([r[2] for r in results])
    np.save(fp, ps)
    np.save(fa, ap)
    print(f"a_p: {len(ps)} primes in {time.time()-t0:.0f}s", flush=True)
    return ps, ap


def apow_table(p, apv, N, B):
    """[a_{p^1}, a_{p^2}, ...] for p^k <= B."""
    out = []
    q, prev, cur = p, 1, apv
    while q <= B:
        out.append(cur)
        q *= p
        if q <= B:
            nxt = apv * cur if N % p == 0 else apv * cur - p * prev
            prev, cur = cur, nxt
    return out


def run(tag, seglog=27):
    cfg = CURVES[tag]
    N, eps, B = cfg["N"], cfg["eps"], cfg["B"]
    A = math.sqrt(N) / (2 * math.pi)
    print(f"== v2 {tag}: N={N} eps={eps} B={B} seg=2^{seglog}", flush=True)
    splines = build_gk_splines()
    ps, ap = get_ap(tag, cfg["ainvs"], B)
    sqB = int(B ** 0.5) + 1
    nsmall = int(np.searchsorted(ps, sqB))
    small_p = ps[:nsmall]
    small_ap = ap[:nsmall]
    apows = {int(p): apow_table(int(p), int(a), N, B)
             for p, a in zip(small_p, small_ap)}
    inv_fact = [1.0 / math.factorial(i) for i in range(JMAX)]
    S = 1 << seglog
    partial = [[] for _ in range(JMAX)]
    t0 = time.time()
    nseg = 0
    for s in range(1, B + 1, S):
        e = min(s + S, B + 1)
        if s / A > 75.0:
            break
        nseg += 1
        L = e - s
        c = np.ones(L, dtype=np.float64)
        rem = np.arange(s, e, dtype=np.int64)
        for pi in range(nsmall):
            p = int(small_p[pi])
            first = ((s + p - 1) // p) * p - s
            if first >= L:
                continue
            tab = apows[p]
            idx = np.arange(first, L, p)
            r = rem[idx] // p
            v = np.ones(len(idx), dtype=np.int64)
            mask = r % p == 0
            while mask.any():
                w = np.nonzero(mask)[0]
                r[w] //= p
                v[w] += 1
                mask = np.zeros(len(idx), dtype=bool)
                mask[w] = r[w] % p == 0
            rem[idx] = r
            tabarr = np.array(tab, dtype=np.float64)
            c[idx] *= tabarr[v - 1]
        big = rem > 1
        if big.any():
            loc = np.searchsorted(ps, rem[big])
            c[big] *= ap[loc].astype(np.float64)
        # weighted sums
        n = np.arange(s, e, dtype=np.float64)
        x = n / A
        keep = x < 75.0
        an, x = c[keep], x[keep]
        u = np.log(x)
        pref = an / x
        gk = [splev(u, splines[k]) for k in range(JMAX)]
        lp = [np.ones_like(u)]
        for i in range(1, JMAX):
            lp.append(lp[-1] * u)
        for j in range(JMAX):
            acc = np.zeros_like(u)
            for i in range(j + 1):
                k = j - i
                coef = ((-1) ** i + eps * (-1) ** k)
                if coef:
                    acc += coef * inv_fact[i] * lp[i] * gk[k]
            partial[j].append(float(np.sum(pref * acc)))
        if nseg % 8 == 0:
            print(f"  seg {nseg} (n<{e}) {time.time()-t0:.0f}s", flush=True)
    lam = [math.fsum(pj) for pj in partial]
    import mpmath as mp
    mp.mp.dps = 40
    invgam = [float(cc) for cc in mp.taylor(lambda w: 1 / mp.gamma(1 + w), 0, JMAX)]
    lnA = math.log(A)
    Fs = [(-lnA) ** i / math.factorial(i) / A for i in range(JMAX)]
    F = [math.fsum(Fs[i] * invgam[j - i] for i in range(j + 1)) for j in range(JMAX)]
    Ljet = [math.fsum(lam[i] * F[j - i] for i in range(j + 1)) for j in range(JMAX)]
    print(f"total {time.time()-t0:.0f}s over {nseg} segments", flush=True)
    for j, cc in enumerate(Ljet):
        print(f"c_{j} = {cc:.12g}", flush=True)


if __name__ == "__main__":
    run(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 27)
