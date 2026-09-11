#!/usr/bin/env python3
"""att710b — THE MARGIN LAW, vectorised (same pre-registration as att710; loads the zero table saved by att710).
   m(T) := min_{t∈[T,2T]} D(t) with the front slaved to the height.  D on the zero side (568; Re ζ′/ζ(½+it) = −ϑ′ exactly):
   D = (1/π)Σ_{γ>0}[F_L(γ−t) + F_L(γ+t)] + trivial term + tail,  F_L(u) = (1 − cos Lu)/(Lu²),
   trivial term = −Re[¼(ψ′(¼+it/2) − (¼+it/2)^{−2})]/(πL) (asymptotic ψ′, |z| ≥ 5), tail ≈ ℓ/(2π² L W).
   P1 (stand-in L = log 9t²): m(T) > 0 at every dyadic T; r(T) = m(T)·π/ϑ′(t*) decreases with no positive limit —
      decision r(2560)/r(10) < 0.5 → "shrinking", > 0.5 → "fixed fraction".
   P2 (compiled head L = 2t + log 9): m(T)·T/ℓ(T)² within a factor 3 across T.
   P3: argmin at a Fejér null of the nearest zero: L·u*/(2π) within 0.15 of an integer (stand-in)."""
import numpy as np, mpmath as mp, time, os
mp.mp.dps = 15
while not os.path.exists("tmp/att710_zeros.npy"): time.sleep(5)
time.sleep(2); zs = np.load("tmp/att710_zeros.npy")
out = open("tmp/att710b_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
say(f"zeros loaded: {len(zs)} up to {zs[-1]:.2f}")
def thetap(t): return float(mp.diff(mp.siegeltheta, t))
def trivial_term(t, L):
    z = 0.25 + 0.5j*t
    psi1 = 1/z + 1/(2*z**2) + 1/(6*z**3) - 1/(30*z**5) + 1/(42*z**7) - 1/(30*z**9)
    return -np.real(0.25*(psi1 - z**(-2)))/(np.pi*L)
def D_zero_side(t, L, W):
    """vectorised: t, L arrays (chunk); zeros within [t_min−W, t_max+W] plus all conjugates; tail estimate."""
    D = np.empty_like(t)
    CH = 3000
    for c0 in range(0, len(t), CH):
        tc = t[c0:c0+CH]; Lc = L[c0:c0+CH]
        i0 = np.searchsorted(zs, tc[0] - W); i1 = np.searchsorted(zs, tc[-1] + W)
        sel = zs[i0:i1]
        u = sel[:, None] - tc[None, :]
        F = (1 - np.cos(Lc[None, :]*u))/(Lc[None, :]*u**2)
        up = zs[:, None] + tc[None, :]
        Fp = (1 - np.cos(Lc[None, :]*up))/(Lc[None, :]*up**2)
        ell = np.log(tc/(2*np.pi))
        Weff = np.minimum(W, zs[-1] - tc)
        D[c0:c0+CH] = (F.sum(axis=0) + Fp.sum(axis=0))/np.pi + ell/(2*np.pi**2*Lc*Weff) + trivial_term(tc, Lc)
    return D
t0 = time.time()
say("=== stand-in front L = log 9t²  (zero side, W = 300; prime-side exact cross-check for T ≤ 160) ===")
r_first = None
for T in (10, 20, 40, 80, 160, 320, 640, 1280, 2560):
    t = np.arange(T, 2*T, 0.002); L = np.log(9*t**2)
    Dz = D_zero_side(t, L, 300.0)
    i = int(np.argmin(Dz)); tstar = t[i]
    tf = np.arange(tstar - 0.01, tstar + 0.01, 1e-4); Df = D_zero_side(tf, np.log(9*tf**2), 300.0)
    j = int(np.argmin(Df)); tstar, m = tf[j], Df[j]
    thp = thetap(tstar); r = m*np.pi/thp
    if r_first is None: r_first = r
    near = zs[np.argmin(np.abs(zs - tstar))]; u = near - tstar; Lstar = np.log(9*tstar**2)
    kk = np.searchsorted(zs, tstar); gap = zs[kk] - zs[kk-1]; meangap = np.pi/thp
    say(f"T={T:5d}: m(T) = {m:+.5f} at t*={tstar:.4f};  ϑ′/π = {thp/np.pi:.4f};  r = {r:.4f};  "
        f"nearest zero {near:.4f} (u* = {u:+.4f}, L·u*/2π = {Lstar*u/(2*np.pi):+.3f});  gap {gap:.3f} = {gap/meangap:.2f}×mean;  "
        f"frac D<0: {np.mean(Dz < 0):.4f}   [{time.time()-t0:.0f}s]")
say(f"P1: r(2560)/r(10) = {r/r_first:.3f}")
# prime-side exact cross-check (T ≤ 160)
def vonmangoldt_upto(x):
    N = int(x) + 1; lam = np.zeros(N); sieve = np.ones(N, dtype=bool); sieve[:2] = False
    for p in range(2, N):
        if sieve[p]:
            sieve[p*p::p] = False; q = p
            while q < N: lam[q] = np.log(p); q *= p
    return lam
lam = vonmangoldt_upto(9*320**2 + 1); n = np.arange(2, len(lam)); keep = lam[2:] > 0
n = n[keep]; ln = np.log(n); lam = lam[2:][keep]
for T in (10, 40, 160):
    tp = np.arange(T, 2*T, 0.01); Lp = np.log(9*tp**2); Dp = np.empty_like(tp)
    for c0 in range(0, len(tp), 200):
        tc = tp[c0:c0+200]; Lc = Lp[c0:c0+200]
        w = np.clip(1 - np.outer(ln, 1/Lc), 0, None)
        clock = np.sum(w*(lam/np.sqrt(n))[:, None]*np.cos(np.outer(ln, tc)), axis=0)
        s0 = 0.5 - 1j*tc; KR = np.real((np.exp(Lc*s0) - 1)/(Lc*s0**2))
        th = np.array([thetap(x) for x in tc])
        Dp[c0:c0+200] = th/np.pi + KR/np.pi - clock/np.pi
    Dzc = D_zero_side(tp, Lp, 300.0)
    say(f"  prime side T={T:4d}: min {Dp.min():+.5f} at t={tp[np.argmin(Dp)]:.3f};  zero side on same grid min {Dzc.min():+.5f};  "
        f"max|prime − zero side| = {np.max(np.abs(Dp - Dzc)):.2e}   [{time.time()-t0:.0f}s]")
say("=== compiled head L = 2t + log 9  (zero side, W = 20; min over the middle third of every gap in [T,2T]) ===")
for T in (10, 20, 40, 80, 160, 320, 640, 1280, 2560):
    sel = zs[(zs >= T) & (zs <= 2*T)]
    ts, Ls = [], []
    for a, b in zip(sel[:-1], sel[1:]):
        Lg = a + b + np.log(9); npts = max(60, int(20*Lg*(b-a)/(6*np.pi)))
        tg = np.linspace(a + (b-a)/3, b - (b-a)/3, npts); ts.append(tg)
    t = np.concatenate(ts); L = 2*t + np.log(9)
    Dg = D_zero_side(t, L, 20.0)
    j = int(np.argmin(Dg)); tstar, m = t[j], Dg[j]
    kk = np.searchsorted(zs, tstar); gap = zs[kk] - zs[kk-1]
    thp = thetap(tstar); ell = np.log(tstar/(2*np.pi))
    say(f"T={T:5d}: m(T) = {m:+.3e} at t*={tstar:.4f} (gap {gap:.3f} = {gap*thp/np.pi:.2f}×mean);  r = {m*np.pi/thp:.3e};  "
        f"m·T/ℓ² = {m*T/ell**2:.3e};  frac D<0: {np.mean(Dg < 0):.4f}   [{time.time()-t0:.0f}s]")
say(f"done ({time.time()-t0:.0f}s)")
