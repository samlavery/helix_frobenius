#!/usr/bin/env python3
"""
dwell_retard.py -- dwell + phasor-spin-rate RETARDATION at high Sym^r rank.

Dwell alone degrades with rank (k: 0.95@r=1 -> 0.44@r=13): the outer Sym^r channels spin at
(r-2j)theta and over-rotate within a dwell period, smearing the crossing.  A UNIFORM spin-slow
is a smooth reparametrization -> cannot change the local exponent k.  So we test a NON-UNIFORM
retardation R that de-chirps the fast end (compresses the high-log n frequencies), plus an
N-scaling control (does resolution alone recover k?), to separate spin-smear from resolution.

carrier: F_r(y) = sum_n lambda_{Sym^r Delta}(n) w(n) n^{-1/2} e^{-i y L(log n)}, two chi-sign lanes,
closure c=|P-M|/max(|P|,|M|).  L = identity (baseline) or a retardation map of log n.
Retardations tried (frozen, not fit):
  R_none : L(x)=x
  R_sqrt : L(x)=x + b*(x-x0)^2  local de-chirp (b<0 slows the fast far end)
  bigN   : same L=x but larger bank (resolution control)
Report median k over crossings for r=8,13 under each.
Run: python3 tmp/dwell_retard.py   (writes tmp/dwell_retard_results.txt)
"""
import math, os
import numpy as np
import sym_closure_3d as S

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dwell_retard_results.txt")

def clo(ys, lneff, a, chunk=1500):
    P = a > 0; M = a < 0
    c = np.empty(len(ys))
    for s in range(0, len(ys), chunk):
        E = np.exp(-1j * np.outer(ys[s:s+chunk], lneff))
        Fp = E[:, P] @ a[P]; Fm = E[:, M] @ a[M]
        c[s:s+chunk] = np.abs(Fp + Fm) / np.maximum(np.maximum(np.abs(Fp), np.abs(Fm)), 1e-300)
    return c

def kstats(ys, c, cut=0.08):
    loc = np.where((c[1:-1] < c[:-2]) & (c[1:-1] <= c[2:]))[0] + 1
    xs = [i for i in loc if c[i] < cut]
    ks, cs = [], []
    for i0 in xs:
        jj = np.arange(i0+2, i0+30)
        if jj[-1] < len(ys):
            ks.append(np.polyfit(np.log(ys[jj]-ys[i0]), np.log(np.maximum(c[jj],1e-300)), 1)[0])
            cs.append(c[i0])
    return (len(xs), float(np.median(cs)) if cs else float('nan'),
            float(np.mean(ks)) if ks else float('nan'))

def run(N, r, theta, spf, L, y0=4.0, y1=30.0, npts=22000):
    lam = S.sym_r_lambda(r, theta, spf, N)[1:N+1]
    n = np.arange(1, N+1, dtype=float); u = n/N
    w = np.exp(1 - 1/np.clip(1 - u*u, 1e-300, None))
    a = lam * w * n**-0.5
    lneff = L(np.log(n))
    ys = np.linspace(y0, y1, npts)
    return kstats(ys, clo(ys, lneff, a))

def main():
    f = open(OUT, "w")
    def emit(s=""): print(s, flush=True); f.write(s+"\n"); f.flush()
    N = 8000
    spf = S.spf_sieve(64000)
    lam_d, _ = S.FC.FAMILIES["delta"].coeff(64000)
    theta = {p: math.acos(max(-1, min(1, lam_d[p].real/2))) for p in range(2, 64000+1) if spf[p]==p}

    x0 = math.log(N)/2
    L_none = lambda x: x
    # local de-chirp: slow the fast far end (x>x0), b<0 compresses high frequencies
    def L_dechirp(b):
        return lambda x: x + b*(x - x0)**2
    emit("dwell + phasor-spin retardation at high Sym^r rank; k should climb toward 1 if it works")
    emit("="*80)
    emit(f"{'r':>3} {'method':>18} {'N':>7} {'#cross':>7} {'med c':>10} {'k mean':>8}")
    for r in (8, 13):
        nc, mc, k = run(N, r, theta, spf, L_none); emit(f"{r:>3} {'dwell only':>18} {N:>7} {nc:>7} {mc:>10.2e} {k:>8.2f}")
        for b in (-0.02, -0.05, -0.1):
            nc, mc, k = run(N, r, theta, spf, L_dechirp(b)); emit(f"{r:>3} {'+retard b='+format(b,'.2f'):>18} {N:>7} {nc:>7} {mc:>10.2e} {k:>8.2f}")
        nc, mc, k = run(4*N, r, theta, spf, L_none); emit(f"{r:>3} {'bigN (control)':>18} {4*N:>7} {nc:>7} {mc:>10.2e} {k:>8.2f}")
        emit("")
    emit("[read] if +retard raises k where bigN does not -> spin-smear, retardation is the fix;")
    emit("       if only bigN raises k -> resolution limit, retardation (coordinate) cannot help.")
    f.close()

if __name__ == "__main__":
    main()
