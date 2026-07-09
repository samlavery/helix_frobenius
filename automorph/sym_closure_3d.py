#!/usr/bin/env python3
"""
sym_closure_3d.py -- Sym^r vanishing measured in the 3D PHASOR REPRESENTATION.

The productivity degradation with Sym^r rank was seen in the 1D Altug transform.  This
asks the right question in the right dimension: build the phasor bank of L(Sym^r Delta),
project by the head readout (focal_closure), and measure whether the harmonic CLOSURE
c(Z)=|sum u R|/max|R| (lane balance / rank-drop) still VANISHES at the zeros as r grows.

If the 3D closure stays deep (~1e-6..1e-12) across r while the 1D deep-dip count thins,
the "productivity degradation" is a projection artifact and the carrier retains exact
cancellation at every rank.  If the 3D closure also degrades, it is a real limit.

lambda_{Sym^r}(n): multiplicative; at prime p with Delta-Satake angle theta_p
(lambda_Delta(p)=2 cos theta_p), lambda(p^k)=h_k = complete homogeneous symmetric of the
r+1 Satake weights {e^{i(r-2j)theta_p}} (real, self-dual), via Newton recurrence with the
elementary symmetric e_i.  Lanes = sign(lambda), as focal_closure's cusp families.

Live output: tmp/sym_closure_3d_results.txt (flushed per rank).
Run: python3 tmp/sym_closure_3d.py
"""
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
import focal_closure as FC

OUT = os.path.join(HERE, "sym_closure_3d_results.txt")
NMAX = 60000            # bank ceiling; y up to ~11 (N=e^11~60000)


def spf_sieve(n):
    spf = np.zeros(n + 1, dtype=np.int64)
    for i in range(2, n + 1):
        if spf[i] == 0:
            spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])
    return spf


def sym_r_lambda(r, theta_p, spf, NMAX):
    """lambda_{Sym^r}(n) for n<=NMAX from per-prime Satake angles theta_p (dict)."""
    # per prime: elementary symmetric e_i of {e^{i(r-2j)theta}} -> h_k recurrence
    pk_cache = {}

    def hk_at_prime(p, kmax):
        th = theta_p[p]
        alphas = np.array([np.exp(1j * (r - 2 * j) * th) for j in range(r + 1)])
        poly = np.poly(alphas)              # [1, p1, ..., p_{r+1}], p_i=(-1)^i e_i
        e = [((-1) ** i) * poly[i].real for i in range(len(poly))]  # e[0]=1, e[i]=e_i
        h = [1.0]
        for k in range(1, kmax + 1):
            s = 0.0
            for i in range(1, min(k, r + 1) + 1):
                s += ((-1) ** (i - 1)) * e[i] * h[k - i]
            h.append(s)
        return h

    lam = np.zeros(NMAX + 1, dtype=np.float64)
    lam[1] = 1.0
    for n in range(2, NMAX + 1):
        p = int(spf[n])
        k = 0
        m = n
        while m % p == 0:
            m //= p
            k += 1
        if p not in pk_cache:
            kmax = int(math.log(NMAX) / math.log(p)) + 1
            pk_cache[p] = hk_at_prime(p, kmax)
        lam[n] = pk_cache[p][k] * lam[m]
    return lam


def make_family(r, lam):
    sign = np.sign(lam).astype(np.int64)

    def make(N):
        return lam[:N + 1].astype(np.complex128), sign[:N + 1]
    return FC.Family(f"sym{r}", "cusp", make, max_N=NMAX)


def closure_events(fam, y0, y1, npts, scale):
    ys = np.linspace(y0, y1, npts)
    c = np.array([FC.closure(fam, y, arrow_scale=scale) for y in ys])
    loc = np.where((c[1:-1] < c[:-2]) & (c[1:-1] <= c[2:]))[0] + 1
    ev = [(ys[i], c[i]) for i in loc if c[i] < 5e-2]
    return ev, float(np.min(c))


def main():
    t0 = time.time()
    f = open(OUT, "w")

    def emit(s=""):
        print(s, flush=True)
        f.write(s + "\n")
        f.flush()

    emit("Sym^r vanishing in the 3D phasor bank of L(Sym^r Delta) -- closure depth at zeros")
    emit("=" * 74)
    spf = spf_sieve(NMAX)
    lam_d, _ = FC.FAMILIES["delta"].coeff(NMAX)
    theta_p = {}
    for p in range(2, NMAX + 1):
        if spf[p] == p:                     # p prime
            theta_p[p] = math.acos(max(-1.0, min(1.0, lam_d[p].real / 2.0)))
    emit(f"[setup] Delta Satake angles for {len(theta_p)} primes, NMAX={NMAX} ({time.time()-t0:.0f}s)")
    emit(f"\n{'r':>3} {'#zeros in [8,11]':>16} {'deepest closure c*':>20} {'median c* at zeros':>20}")

    for r in (0, 1, 2, 3, 4, 5, 6, 8, 10, 13):
        tr = time.time()
        lam = sym_r_lambda(r, theta_p, spf, NMAX)
        fam = make_family(r, lam)
        ev, cmin = closure_events(fam, 8.0, 11.0, 900, FC.PI3)
        depths = sorted(c for _, c in ev)
        med = depths[len(depths) // 2] if depths else float("nan")
        emit(f"{r:>3} {len(ev):>16} {cmin:>20.2e} {med:>20.2e}"
             f"   ({time.time()-tr:.0f}s)")
    emit(f"\n[done] {time.time()-t0:.0f}s -- results in {OUT}")
    f.close()


if __name__ == "__main__":
    main()
