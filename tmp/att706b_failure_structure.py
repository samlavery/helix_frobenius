#!/usr/bin/env python3
"""att706b — where does the winding's sign fail?  κ(t) = −2ϑ′ + 2Σ w Λ n^{−½} cos(t log n) on a fine grid;
   compare failure intervals (κ>0) with ζ's zeros; check D_{R,x} = ϑ′/π + END_x − clock/π  (568, with the pole term)
   END_x(t) = Re[x^{½−it}/((½−it)² log x)]/π  (Riesz kernel at the pole)  — is D_{R,x} ≥ 0 everywhere (567)?"""
import numpy as np, mpmath as mp
mp.mp.dps = 20
out = open("tmp/att706b_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def vonmangoldt_upto(x):
    N = int(x) + 1; lam = np.zeros(N); sieve = np.ones(N, dtype=bool); sieve[:2] = False
    for p in range(2, N):
        if sieve[p]:
            sieve[p*p::p] = False; q = p
            while q < N: lam[q] = np.log(p); q *= p
    return lam
zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832])
ts = np.arange(10.0, 50.0, 0.002)
thp = np.array([float(mp.diff(mp.siegeltheta, t)) for t in ts[::50]])
thp = np.interp(ts, ts[::50], thp)
for x in (100, 1000, 10000):
    lam = vonmangoldt_upto(x-1); n = np.arange(2, len(lam)); ln = np.log(n)
    w = np.clip(1 - ln/np.log(x), 0, None)
    clock = np.einsum('n,nt->t', w*lam[2:]/np.sqrt(n), np.cos(np.outer(ln, ts)))
    kappa = -2*thp + 2*clock
    END = np.real(x**0.5 * np.exp(-1j*ts*np.log(x)) / ((0.5 - 1j*ts)**2 * np.log(x)))/np.pi
    D = thp/np.pi + END - clock/np.pi
    fail = kappa > 0
    # failure intervals
    idx = np.where(np.diff(fail.astype(int)) != 0)[0]
    edges = ts[idx]
    ivs = []
    if fail[0]: edges = np.concatenate([[ts[0]], edges])
    if fail[-1]: edges = np.concatenate([edges, [ts[-1]]])
    ivs = [(edges[i], edges[i+1]) for i in range(0, len(edges)-1, 2)]
    dist = [min(abs(0.5*(a+b) - zeros)) for a, b in ivs]
    say(f"x={x:6d}: κ>0 on {np.mean(fail):.3f}; {len(ivs)} intervals, mean width {np.mean([b-a for a,b in ivs]) if ivs else 0:.3f}; "
        f"midpoint distance to nearest ζ-zero: min {min(dist) if dist else float('nan'):.3f}, median {np.median(dist) if dist else float('nan'):.3f} "
        f"(mean zero spacing {np.mean(np.diff(zeros)):.2f})")
    say(f"           D_{{R,x}} (with END): min {D.min():+.4f} at t={ts[np.argmin(D)]:.2f};  frac D<0 = {np.mean(D<0):.4f};  "
        f"D − END = −κ/2π: min {(-kappa/(2*np.pi)).min():+.4f};  |END| max {np.abs(END).max():.4f}")
    say("           failure intervals: " + ", ".join(f"[{a:.2f},{b:.2f}]" for a, b in ivs[:12]) + (" ..." if len(ivs) > 12 else ""))
