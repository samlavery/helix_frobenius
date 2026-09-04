#!/usr/bin/env python3
"""
att564 — numerical check of the COMPILED statement `truncated_explicit_formula_selberg`
(RequestProject/SelbergTruncatedFormula.lean), read literally:

  ξ′/ξ(s₀) + Σ_ρ m_ρ K₁(ρ − s₀)
     = (1/2π)[∫ K₁(b+it−s₀) E(b+it) dt + ∫ K₁(a+it−s₀) E(1−a−it) dt] − Σ_n Λ_x(n) Λ(n) n^{−s₀},

K₁(w) = (x^{2w} − x^{w})/(w² L), x = e^L, Λ_x = Selberg's weight (1 for n ≤ x, log(x²/n)/log x for
x ≤ n ≤ x², 0 beyond), E = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2).  END reading: the E-lines equal
2π·[E(s₀) + K₁(1 − s₀)] (not compiled).  The zero sum now converges only like Σ log γ/γ² — tail
estimated and reported.
PRE-REGISTERED: relative agreement ≤ 1e−5 (the line integrals are truncated at |t| ≤ 500 where the
kernel decays like 1/t², tail ≈ 1e−3·log/500 ≈ 1e−5 relative; so 1e−5 is the honest tolerance);
END reading to the same order.
"""
import math, sys, time, numpy as np, mpmath as mp
from scipy.special import digamma
mp.mp.dps = 25

L = math.log(float(sys.argv[1]) if len(sys.argv) > 1 else 60.0); x = math.exp(L)
def K(w):
    w = np.asarray(w, dtype=complex)
    return (np.exp(2*L*w) - np.exp(L*w))/(w**2 * L)
def Kmp(w):
    return (mp.exp(2*L*w) - mp.exp(L*w))/(w**2 * L)
def W(v):
    if v <= L: return 1.0
    if v >= 2*L: return 0.0
    return (2*L - v)/L
def E(s):
    return 1/s + 1/(s - 1) - 0.5*math.log(math.pi) + 0.5*digamma(s/2)
def Emp(s):
    return 1/s + 1/(s - 1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2

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
print("x = %.3f, x^2 = %.0f, weighted prime powers: %d (weight 1 up to n=%d)" % (x, x**2, int((lam[1:]*Wn > 0).sum()), int(x)))

t0 = time.time(); NZ = 1200
zeros = [mp.zetazero(k) for k in range(1, NZ + 1)]
print("zeros: %d (last γ = %.2f), %.0fs" % (NZ, float(zeros[-1].imag), time.time() - t0))

a, b = -0.5, 1.5
def check(s0):
    s0m = mp.mpc(s0.real, s0.imag)
    xi_ld = Emp(s0m) + mp.zeta(s0m, derivative=1)/mp.zeta(s0m)
    terms = [Kmp(r - s0m) + Kmp(mp.conj(r) - s0m) for r in zeros]
    zsum = mp.fsum(terms)
    # tail estimate: |K₁(ρ−s₀)| ≈ (x^{2(½−σ)} + x^{½−σ})/(L γ²); Σ_{γ>γ_N} ≈ ∫ N'(γ) c/γ² with N' ≈ log(γ/2π)/2π
    gN = float(zeros[-1].imag); c = (x**(2*(0.5 - s0.real)) + x**(0.5 - s0.real))/L
    tail = 2*c*(math.log(gN/(2*math.pi)) + 1)/(2*math.pi*gN)
    lhs = complex(xi_ld + zsum)
    ps = np.sum(lam[1:]*Wn*nn**(-s0))
    T = 500.0; h = 0.005; t = np.arange(-T, T + h/2, h)
    wts = np.ones_like(t); wts[1:-1:2] = 4; wts[2:-1:2] = 2; wts *= h/3
    sb = b + 1j*t; sa = a + 1j*t
    Ib = np.sum(wts*K(sb - s0)*E(sb)); Ia = np.sum(wts*K(sa - s0)*E(1 - sa))
    rhs = (Ib + Ia)/(2*math.pi) - ps
    end_read = complex(Emp(s0m) + Kmp(1 - s0m))
    print("s0 = %s" % s0)
    print("   ξ'/ξ(s0)            = %s" % complex(xi_ld))
    print("   Σ m K₁(ρ−s0)        = %s   (|last pair| %.1e, tail est. %.1e)" % (complex(zsum), abs(complex(terms[-1])), tail))
    print("   LHS                 = %s" % lhs)
    print("   E-lines/(2π)        = %s" % ((Ib + Ia)/(2*math.pi)))
    print("   prime side          = %s" % ps)
    print("   RHS                 = %s" % rhs)
    print("   |LHS − RHS|/|LHS|   = %.2e" % (abs(lhs - rhs)/abs(lhs)))
    print("   END reading E(s0)+K₁(1−s0) = %s ; |lines/2π − that| = %.2e" % (end_read, abs((Ib + Ia)/(2*math.pi) - end_read)))

for s0 in (0.8 + 30.0j, 0.6 + 100.5j, 1.2 + 5.0j):
    check(s0)
