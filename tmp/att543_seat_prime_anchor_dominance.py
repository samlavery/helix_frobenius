#!/usr/bin/env python3
"""
att543 — the prime-anchor seat criterion: dominance of the off-line node at its own height.

Claim (to test before proving): for an anchor s = σ₀ + iγ_p with σ₀ > 1 placed AT the ordinate of
an off-line FE quadruple {ρ, ρ̄, 1−ρ, 1−ρ̄}, ρ = ½ + y + iγ_p, the FE-paired cross term of the pair
dominates every on-line term geometrically in the pencil order n, because
    |u₁ u₄| = 1/((σ₀−½)² − y²)  >  1/((σ₀−½)² + Δγ²) ≥ |u_ρ'|²   for every on-line ρ',
so λ_min(A_n(s)) < 0 for n large: positivity of A_n at ALL anchors with Re s > 1 and ALL n is
NECESSARY and SUFFICIENT for RH, and every entry is a finite combination of jets of ξ′/ξ at s and
1−s̄, i.e. of absolutely convergent Dirichlet series.

Pre-registered:
  P1  true configuration (first 1000 zeros + conjugates): A_n(1.1 + 18i) ⪰ 0 for n ≤ 8 (mp, 40 digits).
  P2  plants at γ_p = 18 with y ∈ {0.25, 0.1, 0.05}: the inertia flips to (n−1, 1) at some n ≤ 8, with
      the flipping order increasing as y decreases; predicted flip orders: y=0.25 → n ≤ 2, y=0.1 → n ≤ 4,
      y=0.05 → n ≤ 8.
  P3  jet-computability: A_01(s) from the zero sum equals the partial-fraction combination of jets
      of ξ′/ξ at s and at 1−s̄ (computed from mpmath ζ derivatives) to 1e−3 (zero-sum tail).
"""
import numpy as np, mpmath as mp, os
mp.mp.dps = 40

gam = np.load("tmp/zeta_zeros_1000.npy")
rho_true = [mp.mpc(0.5, g) for g in gam] + [mp.mpc(0.5, -g) for g in gam]

def seat_form(s, rhos, n):
    A = mp.matrix(n, n)
    sb = mp.conj(s)
    for r in rhos:
        u = 1/(s - r); v = 1/(sb - 1 + r)
        for j in range(n):
            for k in range(n):
                A[j, k] += u**(j+1) * v**(k+1)
    # Hermitian part
    H = mp.matrix(n, n)
    for j in range(n):
        for k in range(n):
            H[j, k] = (A[j, k] + mp.conj(A[k, j]))/2
    return H

def inertia(H):
    ev = mp.eigh(H, eigvals_only=True)
    ev = sorted([mp.re(e) for e in ev])
    tol = mp.mpf(10)**(-30) * max(1, max(abs(e) for e in ev))
    return (sum(1 for e in ev if e > tol), sum(1 for e in ev if e < -tol)), ev[0]

s0 = mp.mpc(1.1, 18)
print("anchor s0 =", s0)
print("P1 true configuration:")
for n in range(1, 9):
    ine, lmin = inertia(seat_form(s0, rho_true, n))
    print("   n=%d inertia=%s lam_min=%s" % (n, ine, mp.nstr(lmin, 6)))

print("P2 plants at gamma_p = 18:")
for y in (mp.mpf('0.25'), mp.mpf('0.1'), mp.mpf('0.05')):
    b = mp.mpf('0.5') + y
    quad = [mp.mpc(b, 18), mp.mpc(b, -18), mp.mpc(1-b, 18), mp.mpc(1-b, -18)]
    rhos = rho_true + quad
    flip = None
    out = []
    for n in range(1, 9):
        ine, lmin = inertia(seat_form(s0, rhos, n))
        out.append("n=%d %s %s" % (n, ine, mp.nstr(lmin, 4)))
        if flip is None and ine[1] > 0:
            flip = n
    ratio = (mp.mpf('0.6')**2)/((mp.mpf('0.6')**2) - y**2)
    print("   y=%s  dominance ratio per order = %s  first flip at n=%s" % (mp.nstr(y, 3), mp.nstr(ratio, 5), flip))
    print("      " + " | ".join(out))

print("P3 jet-computability of A_01 at s0 (a = 1, b = 2):")
# 1/(x (c−x)^2) = (1/c^2)(1/x) + (1/c^2) 1/(c−x) + (1/c) 1/(c−x)^2,   x = s−ρ, c−x = s̄−1+ρ, c = 2σ−1
c = s0 + mp.conj(s0) - 1
xi_ld = lambda s: mp.diff(lambda z: mp.log(mp.zeta(z)) if False else 0, s) if False else None
def xi_logderiv(s):
    # ξ = ½ s(s−1) π^{-s/2} Γ(s/2) ζ(s);  ξ′/ξ = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) + ζ′/ζ
    return 1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2 + mp.zeta(s, derivative=1)/mp.zeta(s)
def xi_logderiv_k(s, k):
    # k-th derivative of ξ′/ξ, numerically
    return mp.diff(xi_logderiv, s, k)
# Σ_ρ [1/(s−ρ) + 1/(ρ−(1−s̄))] = ξ′/ξ(s) − ξ′/ξ(1−s̄)   (Hadamard pairing, 1/ρ terms cancel on the FE-closed multiset)
# Σ_ρ 1/(s̄−1+ρ)^2 = Σ_ρ 1/(ρ − (1−s̄))^2 = −(ξ′/ξ)′(1−s̄)... careful: d/dw Σ 1/(ρ−w) = Σ 1/(ρ−w)^2 and Σ_ρ 1/(w−ρ) = ξ′/ξ(w) − A − Σ 1/ρ
# so Σ_ρ 1/(ρ−w)^2 = d/dw [ −(ξ′/ξ)(w) + const ] = −(ξ′/ξ)′(w)  at w = 1−s̄
w = 1 - mp.conj(s0)
S1 = xi_logderiv(s0) - xi_logderiv(w)            # Σ [1/(s−ρ) + 1/(ρ−w)]
S2 = -xi_logderiv_k(w, 1)                         # Σ 1/(ρ−w)^2 = Σ 1/(s̄−1+ρ)^2
A01_jets = S1/c**2 + S2/c
A01_zeros = sum((1/(s0-r)) * (1/(mp.conj(s0)-1+r))**2 for r in rho_true)
print("   A_01 from zeros =", mp.nstr(A01_zeros, 10))
print("   A_01 from jets  =", mp.nstr(A01_jets, 10), "  rel diff =", mp.nstr(abs(A01_zeros-A01_jets)/abs(A01_jets), 3))
