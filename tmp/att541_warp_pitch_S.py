#!/usr/bin/env python3
"""
att541 — the warp as a pitch change, and S(t) as its registration cocycle, on the window Hankel.

Objects (Sam's, universal.tex §carrier-S / hp_pencil.tex §setup):
  clock:   ϑ(t) = Im log Γ(1/4 + it/2) − (t/2) log π   (the unit chart's continuous registration)
  count:   N(t) = #{γ ≤ t} (on-line events, all zeros below 3e12 are on the line)
  ledger:  S(t) = N(t) − 1 − ϑ(t)/π      (compiled: countMult_decomposition  dN = dϑ/π + dS)
  window:  W = (a,b),  μ_k(W) = Σ_{γ∈W} γ^k  (contour moments of A'/A; hp_pencil def:moments)

Exact split (Stieltjes against dN = dϑ/π + dS):
  μ_k(W) = C_k + S_k,   C_k := ∫_W z^k ϑ'(z)/π dz  (CLOCK Hankel: positive smooth measure ⇒ PD),
                          S_k := ∫_W z^k dS(z)        (S-Hankel: signed measure ⇒ indefinite in general).
Pre-registered:
  P1  μ_k = C_k + S_k to working precision for k ≤ 8, with S_k computed independently from S(t)
      by Stieltjes integration by parts:  S_k = [z^k S(z)]_a^b − k ∫_a^b z^{k-1} S(z) dz.
  P2  The clock Hankel (C_{j+k}) is positive definite; the S-Hankel (S_{j+k}) is indefinite at n = 3
      (like the windowing block of att221, inertia (2,1)); the total (μ_{j+k}) is PSD with the
      structural rank drop at n = 4 (3 zeros).
  P3  The warp as pitch change: Gram points g_n (ϑ(g_n) = nπ) are the clock-registered marks; the
      monotone map φ: g_{n} ↦ γ_{n+2} (Gram's law pairing) is the event-registering warp on W.
      Its displacement obeys  γ_j − g_{j−2} = (π/ϑ'(ξ_j)) · (1 − S(γ_j⁺))  exactly for some ξ_j in
      the interval (mean value theorem), and ≈ (π/ϑ'(g_{j−2}))(1 − S(γ_j⁺)) to first order:
      the pitch alteration of the helix between clock mark and event is the S-fraction of one
      Gram interval.  Predicted relative error of the first-order law < 5% on W.
  P4  Pushforward identity (moment form of "the defect is corrected by the warp"): the moments of
      the event measure equal the moments of the clock measure pushed forward by the warp,
      Σ_j γ_j^k = Σ_j g_{j−2}^k + Σ_j (γ_j^k − g_{j−2}^k), trivially; the non-trivial check is that the
      DISCRETE clock registration Σ_{g_n∈W} g_n^k tracks the CONTINUOUS clock moment C_k to within
      the boundary term (one Gram interval's worth): |Σ g_n^k − C_k| ≤ max_{z∈W} z^k · 1.
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 30

def theta(t):
    t = mp.mpf(t)
    return mp.im(mp.loggamma(mp.mpf(1)/4 + 1j*t/2)) - t/2*mp.log(mp.pi)

def theta_p(t):
    t = mp.mpf(t)
    return mp.re(mp.digamma(mp.mpf(1)/4 + 1j*t/2))/2 - mp.log(mp.pi)/2

zeros_all = [mp.zetazero(i).imag for i in range(1, 12)]
a, b = mp.mpf(10), mp.mpf(30)
zs = [g for g in zeros_all if a < g < b]
print("window W=(%s,%s): zeros" % (a, b), [mp.nstr(g, 10) for g in zs])

def N(t):
    return sum(1 for g in zeros_all if g <= t)

def S(t):
    return N(t) - 1 - theta(t)/mp.pi

K = 8
mu = [sum(g**k for g in zs) for k in range(K+1)]
C = [mp.quad(lambda z: z**k * theta_p(z)/mp.pi, [a, b]) for k in range(K+1)]
# S_k by Stieltjes parts: [z^k S]_a^b − k ∫ z^{k−1} S dz (S piecewise smooth; split at zeros)
pts = [a] + zs + [b]
def Sk(k):
    bd = b**k * S(b) - a**k * S(a)
    integ = mp.mpf(0)
    if k > 0:
        for lo, hi in zip(pts[:-1], pts[1:]):
            integ += mp.quad(lambda z: z**(k-1) * S(z), [lo, hi])
    return bd - k*integ
Sm = [Sk(k) for k in range(K+1)]

print("\nP1  exact split mu_k = C_k + S_k (S_k via Stieltjes parts, independent of the zero list except through N):")
for k in range(K+1):
    print("  k=%d  mu=%s  C=%s  S=%s  mu-(C+S)=%s" % (k, mp.nstr(mu[k], 12), mp.nstr(C[k], 12), mp.nstr(Sm[k], 12), mp.nstr(mu[k]-C[k]-Sm[k], 3)))

def hankel(m, n):
    return np.array([[float(m[i+j]) for j in range(n)] for i in range(n)])
def inertia(H):
    ev = np.linalg.eigvalsh(H)
    tol = 1e-9 * max(1.0, np.abs(ev).max())
    return (int((ev > tol).sum()), int((ev < -tol).sum()), int((np.abs(ev) <= tol).sum())), ev

print("\nP2  inertia (pos, neg, null):")
for n in (2, 3, 4):
    for name, m in (("clock C", C), ("S-Hankel", Sm), ("total mu", mu)):
        ine, ev = inertia(hankel(m, n))
        print("  n=%d  %-9s inertia=%s  eigs=%s" % (n, name, ine, np.array2string(ev, precision=4)))

# P3: Gram points in and around W
def gram(n):
    return mp.findroot(lambda t: theta(t) - n*mp.pi, 17 + 4.7*n)
grams = {n: gram(n) for n in range(-1, 5)}
print("\nP3  Gram points:", {n: mp.nstr(g, 8) for n, g in grams.items()})
print("    warp displacement  gamma_j - g_{j-2}  vs  (pi/theta'(g))(1 - S(gamma_j+)):")
for j, g in enumerate(zeros_all[:5], start=1):
    gp = grams[j-2]
    Splus = N(g) - 1 - theta(g)/mp.pi        # S at gamma_j from the right (N counts gamma_j)
    disp = g - gp
    pred = mp.pi/theta_p(gp) * (1 - Splus)
    pred_exact_xi = mp.pi/theta_p((g+gp)/2) * (1 - Splus)
    print("  j=%d gamma=%s g_{j-2}=%s  disp=%s  pred(1st order)=%s  rel.err=%s  | S(gamma+)=%s  gram-interval=%s"
          % (j, mp.nstr(g, 8), mp.nstr(gp, 8), mp.nstr(disp, 6), mp.nstr(pred, 6), mp.nstr((pred-disp)/disp, 3),
             mp.nstr(Splus, 5), mp.nstr(grams[j-1]-gp, 5)))

print("\nP4  discrete clock registration vs continuous clock moment on W:")
gW = [g for n, g in grams.items() if a < g < b]
print("    Gram points in W:", [mp.nstr(g, 8) for g in gW])
for k in range(0, 5):
    dg = sum(g**k for g in gW)
    print("  k=%d  sum g^k=%s  C_k=%s  diff=%s  bound(max z^k)=%s" % (k, mp.nstr(dg, 10), mp.nstr(C[k], 10), mp.nstr(dg - C[k], 6), mp.nstr(b**k, 6)))
