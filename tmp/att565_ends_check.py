#!/usr/bin/env python3
"""
att565 — numerical read of `selberg_identity_classical` / `truncated_explicit_formula_selberg_ends`
(RequestProject/TruncatedFormulaEnds.lean):

  Σ_n Λ_x(n)Λ(n)n^{−s₀} = −ζ′/ζ(s₀) + K₁(1−s₀) + K₁(−s₀) − Σ_ρ m_ρ K₁(ρ−s₀) + R_clock(s₀),
  R_clock(s₀) := (1/2π)[∫ K₁(b+it−s₀)Ψ(b+it)dt + ∫ K₁(a+it−s₀)Ψ(1−a−it)dt] − Ψ(s₀),  Ψ = ½ψ(s/2).

The two END terms K₁(1−s₀) (pole at 1) and K₁(−s₀) (pole at 0) are COMPILED residues. The clock
remainder R_clock is NOT compiled as a residue sum; classically it is the trivial zeros,
R_clock(s₀) = −Σ_{k≥0} K₁(−2k−s₀) (the k = 0 term cancels the compiled K₁(−s₀), so that the
classical identity has −Σ_{k≥1} K₁(−2k−s₀) and no K₁(−s₀)).  PRE-REGISTERED: (P1) the classical
identity holds to the truncation level of att564 (≤ 1e−4 relative); (P2) R_clock agrees with
−Σ_{k=0}^{40} K₁(−2k−s₀) to ≤ 1e−4 absolute at small x where K₁(−s₀) is visible (x = 5: |K₁(−s₀)|
≈ x^{−2σ}/(|s₀|²L) ~ 1e−2).
"""
import math, sys, time, numpy as np, mpmath as mp
from scipy.special import digamma
mp.mp.dps = 25

def run(xval, points, NZ=800):
    L = math.log(xval); x = xval
    def K(w):
        w = np.asarray(w, dtype=complex)
        return (np.exp(2*L*w) - np.exp(L*w))/(w**2 * L)
    def Kmp(w):
        return (mp.exp(2*L*w) - mp.exp(L*w))/(w**2 * L)
    def W(v):
        if v <= L: return 1.0
        if v >= 2*L: return 0.0
        return (2*L - v)/L
    def Psi(s):  # numpy
        return 0.5*digamma(s/2)
    def Psimp(s):
        return mp.digamma(s/2)/2
    N = int(x**2) + 1
    lam = np.zeros(N + 1)
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if sieve[p]: sieve[p*p::p] = False
    for p in np.nonzero(sieve)[0]:
        pk = p
        while pk <= N:
            lam[pk] = math.log(p); pk *= p
    nn = np.arange(1, N + 1, dtype=float); Wn = np.array([W(math.log(n)) for n in range(1, N + 1)])
    t0 = time.time(); zeros = [mp.zetazero(k) for k in range(1, NZ + 1)]
    print("x = %.2f: zeros %d (%.0fs)" % (x, NZ, time.time() - t0))
    a, b = -0.5, 1.5
    T = 500.0; h = 0.005; t = np.arange(-T, T + h/2, h)
    wts = np.ones_like(t); wts[1:-1:2] = 4; wts[2:-1:2] = 2; wts *= h/3
    sb = b + 1j*t; sa = a + 1j*t
    for s0 in points:
        s0m = mp.mpc(s0.real, s0.imag)
        zeta_ld = mp.zeta(s0m, derivative=1)/mp.zeta(s0m)
        zsum = mp.fsum(Kmp(r - s0m) + Kmp(mp.conj(r) - s0m) for r in zeros)
        ps = np.sum(lam[1:]*Wn*nn**(-s0))
        Ib = np.sum(wts*K(sb - s0)*Psi(sb)); Ia = np.sum(wts*K(sa - s0)*Psi(1 - sa))
        Rclock = (Ib + Ia)/(2*math.pi) - complex(Psimp(s0m))
        rhs = complex(-zeta_ld + Kmp(1 - s0m) + Kmp(-s0m) - zsum) + Rclock
        triv = complex(mp.fsum(Kmp(-2*k - s0m) for k in range(0, 41)))
        print("  s0 = %s" % s0)
        print("     prime side           = %s" % ps)
        print("     RHS (classical form) = %s   rel dev %.2e" % (rhs, abs(ps - rhs)/abs(ps)))
        print("     END terms: K1(1−s0) = %s ; K1(−s0) = %s" % (complex(Kmp(1 - s0m)), complex(Kmp(-s0m))))
        print("     R_clock              = %s" % Rclock)
        print("     −Σ_{k≥0} K1(−2k−s0)  = %s   |diff| %.2e" % (-triv, abs(Rclock + triv)))

run(5.0, (0.8 + 3.0j, 0.6 + 10.5j, 1.2 + 5.0j), NZ=600)
run(30.0, (0.8 + 30.0j, 1.2 + 5.0j), NZ=900)
