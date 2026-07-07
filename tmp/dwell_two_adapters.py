#!/usr/bin/env python3
"""
dwell_two_adapters.py -- DERIVED (non-fitted) clock-sensitive adapter adjuster + reverb-
dissipation retardation, at high Sym^r rank.

Adapter 1 (clock-sensitive adjuster, APPROACH / symmetric de-chirp):
  b_derived = -1/x0^2 with x0=log(N)/2  (the swept optimum -0.05 at N=8000 satisfies b*x0^2~-1,
  i.e. it is fixed by the readout log-densification -- rank-independent, NOT fit).
Adapter 2 (reverb-dissipation retardation, DEPARTURE / odd, breaks approach/departure symmetry):
  odd cubic term  c*(x-x0)^3 ; c_derived scaled by the DEGREE d=r+1 (the reverb reopening rate
  scales with degree): c = -g*(r+1)/x0^3 for a single universal g (no per-rank tuning).
Frequencies: L(log n) = log n + b(log n-x0)^2 + c(log n-x0)^3.
Report k at r=8,13 for: dwell-only / +adj(derived) / +adj+reverb(derived), and a small g-scan
so we can SEE whether the derived reverb term moves k past the ~0.69 the de-chirp alone gave.
Run: python3 tmp/dwell_two_adapters.py   (writes tmp/dwell_two_adapters_results.txt)
"""
import math, os
import numpy as np
import sym_closure_3d as S

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dwell_two_adapters_results.txt")

def clo(ys, lneff, a, chunk=1500):
    P = a > 0; M = a < 0; c = np.empty(len(ys))
    for s in range(0, len(ys), chunk):
        E = np.exp(-1j * np.outer(ys[s:s+chunk], lneff))
        Fp = E[:, P] @ a[P]; Fm = E[:, M] @ a[M]
        c[s:s+chunk] = np.abs(Fp+Fm)/np.maximum(np.maximum(np.abs(Fp), np.abs(Fm)), 1e-300)
    return c

def kstat(ys, c, cut=0.08):
    loc = np.where((c[1:-1] < c[:-2]) & (c[1:-1] <= c[2:]))[0]+1
    ks = []
    for i0 in [i for i in loc if c[i] < cut]:
        jj = np.arange(i0+2, i0+30)
        if jj[-1] < len(ys):
            ks.append(np.polyfit(np.log(ys[jj]-ys[i0]), np.log(np.maximum(c[jj],1e-300)), 1)[0])
    return (len([1 for i in loc if c[i]<cut]), float(np.mean(ks)) if ks else float('nan'))

def run(N, r, theta, spf, b, c):
    lam = S.sym_r_lambda(r, theta, spf, N)[1:N+1]
    n = np.arange(1, N+1, dtype=float); u = n/N
    w = np.exp(1 - 1/np.clip(1-u*u, 1e-300, None)); a = lam*w*n**-0.5
    x = np.log(n); x0 = math.log(N)/2.0
    lneff = x + b*(x-x0)**2 + c*(x-x0)**3
    ys = np.linspace(4.0, 30.0, 22000)
    return kstat(ys, clo(ys, lneff, a))

def main():
    f = open(OUT, "w")
    def emit(s=""): print(s, flush=True); f.write(s+"\n"); f.flush()
    N = 8000; x0 = math.log(N)/2.0
    b_d = -1.0/x0**2
    spf = S.spf_sieve(N)
    lam_d, _ = S.FC.FAMILIES["delta"].coeff(N)
    theta = {p: math.acos(max(-1, min(1, lam_d[p].real/2))) for p in range(2, N+1) if spf[p]==p}
    emit(f"derived adapters: b=-1/x0^2={b_d:.4f} (x0={x0:.3f}); reverb c=-g*(r+1)/x0^3, g universal")
    emit("="*76)
    emit(f"{'r':>3} {'config':>26} {'#cross':>7} {'k mean':>8}")
    for r in (8, 13):
        d = r + 1
        nc, k = run(N, r, theta, spf, 0.0, 0.0);  emit(f"{r:>3} {'dwell only':>26} {nc:>7} {k:>8.2f}")
        nc, k = run(N, r, theta, spf, b_d, 0.0);  emit(f"{r:>3} {'+adjuster (derived b)':>26} {nc:>7} {k:>8.2f}")
        for g in (0.02, 0.05, 0.1, 0.2):
            c_d = -g*d/x0**3
            nc, k = run(N, r, theta, spf, b_d, c_d)
            emit(f"{r:>3} {'+reverb g='+format(g,'.2f'):>26} {nc:>7} {k:>8.2f}")
        emit("")
    emit("[read] derived adjuster should match the swept -0.05 result (k~0.68); if the derived")
    emit("       reverb term (odd, degree-scaled) pushes k further toward 1, the 2nd adapter is real.")
    f.close()

if __name__ == "__main__":
    main()
