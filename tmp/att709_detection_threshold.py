#!/usr/bin/env python3
"""att709 — WHAT DOES THE SLAVED-FRONT CLAUSE IMPLY?  (Sam: positivity means non-negativity; run only a test with value.)
   Control on the ZERO side (568: prime side = zero side exactly): D_{R,x}(t) = (1/π) Σ_ρ Re K_R(ρ − ½ − it) + O(1/x).
   Perturbation consistent with the functional equation: two neighbouring on-line zeros γ_j, γ_{j+1} merge and split
   off the line as the pair ½ ± δ + iγ₀, γ₀ = (γ_j + γ_{j+1})/2.  Then
       D^{pair}(t) = D^{RH}(t) − (1/π)[F(γ_j − t) + F(γ_{j+1} − t)] + (1/π)[Re K_R(δ + i(γ₀−t)) + Re K_R(−δ + i(γ₀−t))],
   F(u) = Re K_R(iu) = (1 − cos Lu)/(Lu²) ≥ 0.  Zeros farther than 60 from γ₀ contribute < 0.002 and are dropped.
   Front slaved to height: L = log(9 t²) (the 708 stand-in).  Threshold δ*(γ₀) := least δ with min_t D^{pair}(t) < 0.
   PRE-REGISTERED.  P1: δ*(γ₀)·log(9γ₀²) lies in [0.4, 1.2] at γ₀ ≈ 100, 1000, 10000 (a depth rung A₀/log γ, NOT RH):
   refutes 708's pencil "one-variable clause ⟺ RH".  P2 (free front, 568): at γ₀ ≈ 1000, δ = 0.02, the pair is
   detected for some L in {14, 50, 100, 300, 1000, 3000} — prediction: only for L ≳ 500 (x^δ ≫ L² log t)."""
import numpy as np, mpmath as mp
mp.mp.dps = 15
out = open("tmp/att709_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def zeros_near(gamma0, W=60):
    # zeros with |γ − γ₀| ≤ W via mpmath.zetazero, using N(T) ≈ (T/2π)log(T/2πe) + 7/8 to seed the index
    def Napprox(T): return T/(2*np.pi)*np.log(T/(2*np.pi*np.e)) + 7/8
    k0 = max(1, int(Napprox(gamma0 - W)) - 3); zs = []
    k = k0
    while True:
        z = float(mp.zetazero(k).imag)
        if z > gamma0 + W: break
        if z >= gamma0 - W: zs.append(z)
        k += 1
    return np.array(zs)
def KR_re(L, w):   # Re K_R(w), K_R(w) = (x^w − 1)/(L w²), x = e^L  (vectorised over complex w)
    w = np.asarray(w, dtype=complex)
    return np.real((np.exp(L*w) - 1)/(L*w**2))
def D_RH(L, zs, t):        # (1/π) Σ_γ F(γ − t) with F = Re K_R(iu)
    u = zs[:, None] - t[None, :]
    return np.sum(KR_re(L, 1j*u), axis=0)/np.pi
def D_pair(L, zs, j, delta, t):
    g0 = 0.5*(zs[j] + zs[j+1]); u = g0 - t
    base = D_RH(L, zs, t) - (KR_re(L, 1j*(zs[j]-t)) + KR_re(L, 1j*(zs[j+1]-t)))/np.pi
    return base + (KR_re(L, delta + 1j*u) + KR_re(L, -delta + 1j*u))/np.pi
say("P1 — slaved front L = log(9t²): detection threshold δ* of a merged pair, and A₀ = δ*·log(9γ₀²)")
for g_target in (100.0, 1000.0, 10000.0):
    zs = zeros_near(g_target)
    j = int(np.argmin(np.abs(zs - g_target))); j = min(j, len(zs) - 2)
    g0 = 0.5*(zs[j] + zs[j+1]); gap = zs[j+1] - zs[j]
    t = np.linspace(g0 - 4, g0 + 4, 8001); L = np.log(9*t**2)
    def minD(delta):
        return np.min(np.array([D_pair(L[i], zs, j, delta, t[i:i+1])[0] for i in range(0, len(t), 1)]))
    # bisection on δ (min D is monotone-ish in δ near the threshold; verify bracket first)
    lo, hi = 0.0, 0.6
    mlo, mhi = minD(1e-4), minD(hi)
    if mhi >= 0:
        say(f"  γ₀={g0:9.3f} (gap {gap:.3f}): NOT detected even at δ=0.6 (min D = {mhi:+.4f})"); continue
    for _ in range(18):
        mid = 0.5*(lo+hi)
        if minD(mid) < 0: hi = mid
        else: lo = mid
    dstar = hi; A0 = dstar*np.log(9*g0**2)
    say(f"  γ₀={g0:9.3f} (gap {gap:.3f}, {len(zs)} zeros in window): δ* = {dstar:.4f},  A₀ = δ*·log(9γ₀²) = {A0:.3f};  "
        f"min D at δ=1e-4: {mlo:+.5f}, at δ=0.6: {mhi:+.3f}")
say("P2 — free front (568), γ₀ ≈ 1000, δ = 0.02: min_t D^{pair} for fixed L")
zs = zeros_near(1000.0); j = int(np.argmin(np.abs(zs - 1000.0))); g0 = 0.5*(zs[j] + zs[j+1])
t = np.linspace(g0 - 4, g0 + 4, 8001)
for L in (14.0, 50.0, 100.0, 300.0, 1000.0, 3000.0):
    m = np.min(D_pair(L, zs, j, 0.02, t))
    say(f"  L={L:7.1f} (x = e^L): min D^{{pair}} = {m:+.4e}  →  {'DETECTED' if m < 0 else 'not detected'}")
