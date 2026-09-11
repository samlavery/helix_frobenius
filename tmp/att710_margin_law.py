#!/usr/bin/env python3
"""att710 — THE MARGIN LAW (Sam: "run that test").  m(T) := min_{t∈[T,2T]} D(t) at a front slaved to the height,
   against the mean density ϑ′/π.  Register: the clause is D ≥ 0; the test measures the LAW of the margin, not the clause.
   D on the prime side (exact): D = ϑ′/π + Re K_R(½−it)/π − (1/π)Σ_{n<x} w_x(n)Λ(n)n^{−½}cos(t log n), x = 9t² (stand-in).
   D on the zero side (568, Re ζ′/ζ(½+it) = −ϑ′ exactly): D = (1/π)Σ_{γ>0}[F_L(γ−t) + F_L(γ+t)] + trivial term + tail,
   F_L(u) = (1 − cos Lu)/(Lu²), trivial term = −Re[¼(ψ′(¼+it/2) − (¼+it/2)^{−2})]/(πL), tail ≈ ℓ/(2π² L W).
   PRE-REGISTERED.  P1 (stand-in L = log 9t²): m(T) > 0 at every dyadic T; the ratio r(T) = m(T)·π/ϑ′(t*) DECREASES
   with T with no positive limit — decision: r(2560)/r(10) < 0.5 supports "shrinking", > 0.5 supports "fixed fraction".
   P2 (compiled head L = 2t + log 9): m(T)·T/ℓ(T)² within a factor 3 across T (m ~ ℓ²/T), so r(T) ~ 1/T.
   P3: the argmin sits at a Fejér null of the nearest zero: L·u*/(2π) within 0.15 of an integer at the stand-in."""
import numpy as np, mpmath as mp, time
mp.mp.dps = 15
out = open("tmp/att710_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
t0 = time.time()
# ---------- zeros up to Gmax ----------
Tmax = 2560; W = 300; Gmax = 2*Tmax + W
zs = []; k = 1
while True:
    z = float(mp.zetazero(k).imag)
    if z > Gmax: break
    zs.append(z); k += 1
    if k % 1000 == 0: say(f"  … {k} zeros, last {z:.2f}, {time.time()-t0:.0f}s")
zs = np.array(zs); say(f"zeros: {len(zs)} up to {zs[-1]:.2f}  ({time.time()-t0:.0f}s)")
np.save("tmp/att710_zeros.npy", zs)
def thetap(t): return float(mp.diff(mp.siegeltheta, t))
def trivial_term(t, L):
    z = mp.mpc(0.25, t/2)
    return -float(mp.re(0.25*(mp.polygamma(1, z) - z**(-2))))/(np.pi*L)
def D_zero_side(t, L):
    """t: array, L: array (same shape). Nontrivial comb over zeros within ±W plus far tail estimate, plus trivial term."""
    D = np.empty_like(t)
    for i in range(len(t)):
        ti, Li = t[i], L[i]
        sel = zs[np.abs(zs - ti) <= W]
        u = sel - ti; F = (1 - np.cos(Li*u))/(Li*u**2)
        up = zs + ti; Fp = (1 - np.cos(Li*up))/(Li*up**2)          # conjugate zeros, all of them (small)
        ell = np.log(ti/(2*np.pi))
        tail = ell/(2*np.pi**2*Li*W)                                # zeros beyond ±W (mean density ℓ/2π, ⟨1−cos⟩ = 1)
        D[i] = (np.sum(F) + np.sum(Fp))/np.pi + tail + trivial_term(ti, Li)
    return D
def vonmangoldt_upto(x):
    N = int(x) + 1; lam = np.zeros(N); sieve = np.ones(N, dtype=bool); sieve[:2] = False
    for p in range(2, N):
        if sieve[p]:
            sieve[p*p::p] = False; q = p
            while q < N: lam[q] = np.log(p); q *= p
    return lam
say("=== stand-in front L = log 9t²: prime side (exact) for T ≤ 160, zero side for all T ===")
lam = vonmangoldt_upto(9*320**2 + 1); n = np.arange(2, len(lam)); keep = lam[2:] > 0
n = n[keep]; ln = np.log(n); lam = lam[2:][keep]
r_first = None
for T in (10, 20, 40, 80, 160, 320, 640, 1280, 2560):
    t = np.arange(T, 2*T, 0.002); L = np.log(9*t**2)
    Dz = D_zero_side(t, L)
    i = int(np.argmin(Dz)); tstar = t[i]; m = Dz[i]
    # refine around the min with the zero side at step 2e-4
    tf = np.arange(tstar - 0.01, tstar + 0.01, 2e-4); Lf = np.log(9*tf**2); Df = D_zero_side(tf, Lf)
    j = int(np.argmin(Df)); tstar, m = tf[j], Df[j]
    thp = thetap(tstar); r = m*np.pi/thp
    if r_first is None: r_first = r
    near = zs[np.argmin(np.abs(zs - tstar))]; u = near - tstar; Lstar = np.log(9*tstar**2)
    kk = np.searchsorted(zs, tstar); gap = zs[kk] - zs[kk-1]; meangap = np.pi/thp
    line = (f"T={T:5d}: m(T) = {m:+.5f} at t*={tstar:.4f};  ϑ′/π = {thp/np.pi:.4f};  r = m/(ϑ′/π) = {r:.4f};  "
            f"nearest zero {near:.4f} (u*={u:+.4f}, L·u*/2π = {Lstar*u/(2*np.pi):+.3f});  gap {gap:.3f} = {gap/meangap:.2f}×mean")
    if T <= 160:   # prime-side exact cross-check at the argmin and over the range on a coarser grid
        tp = np.arange(T, 2*T, 0.01); Lp = np.log(9*tp**2)
        Dp = np.empty_like(tp)
        for c0 in range(0, len(tp), 200):
            tc = tp[c0:c0+200]; Lc = Lp[c0:c0+200]
            w = np.clip(1 - np.outer(ln, 1/Lc), 0, None)
            clock = np.sum(w*(lam/np.sqrt(n))[:, None]*np.cos(np.outer(ln, tc)), axis=0)
            KR = np.array([float(mp.re((mp.e**(Lc[q]*mp.mpc(0.5, -tc[q])) - 1)/(Lc[q]*mp.mpc(0.5, -tc[q])**2))) for q in range(len(tc))])
            th = np.array([thetap(x) for x in tc])
            Dp[c0:c0+200] = th/np.pi + KR/np.pi - clock/np.pi
        Dzc = D_zero_side(tp, Lp)
        line += f";  prime-side min {Dp.min():+.5f} at t={tp[np.argmin(Dp)]:.3f}, max|prime−zero side| {np.max(np.abs(Dp - Dzc)):.1e}"
    say(line)
say(f"P1 ratio r(2560)/r(10) = {r/r_first:.3f}   ({time.time()-t0:.0f}s)")
say("=== compiled head L = 2t + log 9: zero side, min over the middle of every gap in [T,2T] ===")
for T in (10, 20, 40, 80, 160, 320, 640, 1280, 2560):
    sel = zs[(zs >= T) & (zs <= 2*T)]
    best = (np.inf, None)
    for a, b in zip(sel[:-1], sel[1:]):
        Lg = 2*0.5*(a+b) + np.log(9)
        tg = np.linspace(a + (b-a)/3, b - (b-a)/3, max(50, int(20*Lg*(b-a)/(6*np.pi))))
        Dg = D_zero_side(tg, 2*tg + np.log(9))
        j = int(np.argmin(Dg))
        if Dg[j] < best[0]: best = (Dg[j], tg[j], b - a)
    m, tstar, gap = best; thp = thetap(tstar); ell = np.log(tstar/(2*np.pi))
    say(f"T={T:5d}: m(T) = {m:+.3e} at t*={tstar:.4f} (gap {gap:.3f});  r = m/(ϑ′/π) = {m*np.pi/thp:.3e};  m·T/ℓ² = {m*T/ell**2:.3e}")
say(f"done ({time.time()-t0:.0f}s)")
