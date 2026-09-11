#!/usr/bin/env python3
"""att710d — compiled-head part, conjugate-zero matrix dropped (< 1e−8 at L ≥ 20) of the margin law (att710b crashed on T=10: only one zero in [10,20]).
   Gaps taken from zeros in [T−8, 2T+8]; sample points restricted to [T, 2T].  Same D_zero_side as att710b."""
import numpy as np, mpmath as mp, time
mp.mp.dps = 15
zs = np.load("tmp/att710_zeros.npy")
out = open("tmp/att710d_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
def thetap(t): return float(mp.diff(mp.siegeltheta, t))
def trivial_term(t, L):
    z = 0.25 + 0.5j*t
    psi1 = 1/z + 1/(2*z**2) + 1/(6*z**3) - 1/(30*z**5) + 1/(42*z**7) - 1/(30*z**9)
    return -np.real(0.25*(psi1 - z**(-2)))/(np.pi*L)
def D_zero_side(t, L, W):
    D = np.empty_like(t); CH = 3000
    for c0 in range(0, len(t), CH):
        tc = t[c0:c0+CH]; Lc = L[c0:c0+CH]
        i0 = np.searchsorted(zs, tc[0] - W); i1 = np.searchsorted(zs, tc[-1] + W); sel = zs[i0:i1]
        u = sel[:, None] - tc[None, :]; F = (1 - np.cos(Lc[None, :]*u))/(Lc[None, :]*u**2)
        Fp = np.zeros((1, len(tc)))
        ell = np.log(tc/(2*np.pi)); Weff = np.minimum(W, zs[-1] - tc)
        D[c0:c0+CH] = (F.sum(axis=0) + Fp.sum(axis=0))/np.pi + ell/(2*np.pi**2*Lc*Weff) + trivial_term(tc, Lc)
    return D
t0 = time.time()
say("=== compiled head L = 2t + log 9  (zero side, W = 20; min over the middle third of every gap meeting [T,2T]) ===")
r_first = None
for T in (10, 20, 40, 80, 160, 320, 640, 1280, 2560):
    sel = zs[(zs >= T - 8) & (zs <= 2*T + 8)]
    ts = []
    for a, b in zip(sel[:-1], sel[1:]):
        Lg = a + b + np.log(9); npts = max(60, int(20*Lg*(b-a)/(6*np.pi)))
        tg = np.linspace(a + (b-a)/3, b - (b-a)/3, npts); tg = tg[(tg >= T) & (tg <= 2*T)]
        if len(tg): ts.append(tg)
    t = np.concatenate(ts); L = 2*t + np.log(9)
    Dg = D_zero_side(t, L, 20.0)
    j = int(np.argmin(Dg)); tstar, m = t[j], Dg[j]
    kk = np.searchsorted(zs, tstar); gap = zs[kk] - zs[kk-1]
    thp = thetap(tstar); ell = np.log(tstar/(2*np.pi)); r = m*np.pi/thp
    if r_first is None: r_first = r
    say(f"T={T:5d}: m(T) = {m:+.3e} at t*={tstar:.4f} (gap {gap:.3f} = {gap*thp/np.pi:.2f}×mean);  r = m/(ϑ′/π) = {r:.3e};  "
        f"m·T/ℓ² = {m*T/ell**2:.3e};  frac D<0: {np.mean(Dg < 0):.4f};  points {len(t)}   [{time.time()-t0:.0f}s]")
say(f"P2: r(2560)/r(10) = {r/r_first:.3e};  done ({time.time()-t0:.0f}s)")
