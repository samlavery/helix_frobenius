#!/usr/bin/env python3
"""att709b — the same detection-threshold control at the COMPILED head: physicalHead y ≥ 9 e^{2y} at ordinate y,
   so the slaved front is L(t) = 2t + log 9 (exponential head), not the 9t² stand-in of 708.
   PRE-REGISTERED: δ*(γ₀)·L(γ₀) ≈ A₀ ∈ [0.3, 0.6] (same constant as att709, rung β − ½ ≤ A₀/(2γ)): the compiled head's
   clause implies all zeros within O(1/γ) of the axis, still NOT RH.  Decision: A₀ outside [0.1, 2] refutes."""
import numpy as np, mpmath as mp
mp.mp.dps = 15
out = open("tmp/att709b_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def zeros_near(gamma0, W=60):
    def Napprox(T): return T/(2*np.pi)*np.log(T/(2*np.pi*np.e)) + 7/8
    k = max(1, int(Napprox(gamma0 - W)) - 3); zs = []
    while True:
        z = float(mp.zetazero(k).imag)
        if z > gamma0 + W: break
        if z >= gamma0 - W: zs.append(z)
        k += 1
    return np.array(zs)
def KR_re(L, w):
    w = np.asarray(w, dtype=complex)
    with np.errstate(over='ignore', invalid='ignore'):
        return np.real((np.exp(L*w) - 1)/(L*w**2))
def D_RH(L, zs, t):
    u = zs[:, None] - t[None, :]; return np.sum(KR_re(L, 1j*u), axis=0)/np.pi
def D_pair(L, zs, j, delta, t):
    g0 = 0.5*(zs[j] + zs[j+1]); u = g0 - t
    base = D_RH(L, zs, t) - (KR_re(L, 1j*(zs[j]-t)) + KR_re(L, 1j*(zs[j+1]-t)))/np.pi
    return base + (KR_re(L, delta + 1j*u) + KR_re(L, -delta + 1j*u))/np.pi
say("compiled head L(t) = 2t + log 9: detection threshold δ* of a merged pair and A₀ = δ*·L(γ₀)")
for g_target in (100.0, 1000.0, 10000.0):
    zs = zeros_near(g_target); j = int(np.argmin(np.abs(zs - g_target))); j = min(j, len(zs) - 2)
    g0 = 0.5*(zs[j] + zs[j+1]); gap = zs[j+1] - zs[j]
    # resolution 1/L is tiny: sample t densely within ±3/L·10 of γ₀ plus a coarse outer grid
    Lg = 2*g0 + np.log(9)
    t = np.concatenate([np.linspace(g0 - 40/Lg, g0 + 40/Lg, 20001), np.linspace(g0 - 4, g0 + 4, 4001)])
    L = 2*t + np.log(9)
    def minD(delta):
        return np.min(np.array([D_pair(L[i], zs, j, delta, t[i:i+1])[0] for i in range(len(t))]))
    lo, hi = 0.0, 0.05; mhi = minD(hi)
    if mhi >= 0: say(f"  γ₀={g0:9.3f}: not detected at δ=0.05 (min D {mhi:+.3e})"); continue
    for _ in range(26):
        mid = 0.5*(lo+hi)
        if minD(mid) < 0: hi = mid
        else: lo = mid
    say(f"  γ₀={g0:9.3f} (gap {gap:.3f}): δ* = {hi:.3e},  A₀ = δ*·L(γ₀) = {hi*Lg:.3f}   (L = {Lg:.1f})")
