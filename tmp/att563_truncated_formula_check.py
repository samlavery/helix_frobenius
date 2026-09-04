#!/usr/bin/env python3
"""
att563 — numerical check of the COMPILED statement `truncated_explicit_formula_cubic`
(RequestProject/TruncatedExplicitFormula.lean), read literally:

  ξ′/ξ(s₀) + Σ_ρ m_ρ K(ρ − s₀)
     = (1/2π)[∫ K(b+it−s₀) E(b+it) dt + ∫ K(a+it−s₀) E(1−a−it) dt] − Σ_n W(log n) Λ(n) n^{−s₀},

K(w) = (x^{4w} − 3x^{3w} + 3x^{2w} − x^w)/(w⁴ L³), x = e^L, W = cubic B-spline (1 for n ≤ x, 0 for
n ≥ x⁴), E = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2).  Also the END reading: the two E-lines equal
2π·[E(s₀) + K(1 − s₀)] (residues at s₀ and at the pole s = 1 of E; the pole of 1/s at 0 is cancelled
by ½ψ(s/2)) — NOT compiled, checked here numerically.
PRE-REGISTERED: relative agreement of the two sides ≤ 1e−6 at two points s₀; END reading agrees
to the same order.  Disagreement = a transcription error in the ledger's reading of the theorem.
"""
import math, time, numpy as np, mpmath as mp
from scipy.special import digamma
mp.mp.dps = 25

L = math.log(30.0); x = math.exp(L); LC = L
def K(w):
    w = np.asarray(w, dtype=complex)
    return (np.exp(4*L*w) - 3*np.exp(3*L*w) + 3*np.exp(2*L*w) - np.exp(L*w))/(w**4 * L**3)
def Kmp(w):
    return (mp.exp(4*L*w) - 3*mp.exp(3*L*w) + 3*mp.exp(2*L*w) - mp.exp(L*w))/(w**4 * L**3)
def W(v):
    r = lambda c: max(c - v, 0.0)**3
    return (r(4*L) - 3*r(3*L) + 3*r(2*L) - r(L))/(6*L**3)
def E(s):  # numpy complex
    return 1/s + 1/(s - 1) - 0.5*math.log(math.pi) + 0.5*digamma(s/2)
def Emp(s):
    return 1/s + 1/(s - 1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2

# von Mangoldt up to x^4
N = int(x**4) + 1
lam = np.zeros(N + 1)
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for p in range(2, int(N**0.5) + 1):
    if sieve[p]: sieve[p*p::p] = False
primes = np.nonzero(sieve)[0]
for p in primes:
    pk = p
    while pk <= N:
        lam[pk] = math.log(p); pk *= p
nn = np.arange(1, N + 1, dtype=float); Wn = np.array([W(math.log(n)) for n in range(1, N + 1)])
print("x = %.3f, x^4 = %.0f, prime powers weighted: %d (weight 1 up to n=%d)" % (x, x**4, int((lam[1:]*Wn > 0).sum()), int(x)))

# zeros
t0 = time.time(); NZ = 900
zeros = [mp.zetazero(k) for k in range(1, NZ + 1)]
print("zeros: %d (last γ = %.2f), %.0fs" % (NZ, float(zeros[-1].imag), time.time() - t0))

a, b = -0.5, 1.5
def check(s0):
    s0m = mp.mpc(s0.real, s0.imag)
    xi_ld = Emp(s0m) + mp.zeta(s0m, derivative=1)/mp.zeta(s0m)
    zsum = mp.fsum(Kmp(r - s0m) + Kmp(mp.conj(r) - s0m) for r in zeros)
    lhs = complex(xi_ld + zsum)
    # prime side
    ps = np.sum(lam[1:]*Wn*nn**(-s0))
    # E-lines by Simpson on [-T, T]
    T = 500.0; h = 0.005; t = np.arange(-T, T + h/2, h)
    wts = np.ones_like(t); wts[1:-1:2] = 4; wts[2:-1:2] = 2; wts *= h/3
    sb = b + 1j*t; sa = a + 1j*t
    Ib = np.sum(wts*K(sb - s0)*E(sb)); Ia = np.sum(wts*K(sa - s0)*E(1 - sa))
    rhs = (Ib + Ia)/(2*math.pi) - ps
    end_read = complex(Emp(s0m) + Kmp(1 - s0m))
    print("s0 = %s" % s0)
    print("   ξ'/ξ(s0)            = %s" % complex(xi_ld))
    print("   Σ m K(ρ−s0)         = %s   (|last term| %.1e)" % (complex(zsum), abs(complex(Kmp(zeros[-1] - s0m)))))
    print("   LHS                 = %s" % lhs)
    print("   E-lines/(2π)        = %s" % ((Ib + Ia)/(2*math.pi)))
    print("   prime side          = %s" % ps)
    print("   RHS                 = %s" % rhs)
    print("   |LHS − RHS|/|LHS|   = %.2e" % (abs(lhs - rhs)/abs(lhs)))
    print("   END reading E(s0)+K(1−s0) = %s ; |lines/2π − that| = %.2e" % (end_read, abs((Ib + Ia)/(2*math.pi) - end_read)))

for s0 in (0.8 + 30.0j, 0.6 + 100.5j, 1.2 + 5.0j):
    check(s0)
