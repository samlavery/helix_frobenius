#!/usr/bin/env python3
"""
att542 — can the PRIME-COMPUTABLE anchor see an off-line pair?  (seat construction, first datum)

Object (hp_pencil rem:travelingseat): the FE-paired traveling-seat form at anchor s,
    A_jk(s) = Σ_ρ m_ρ (s−ρ)^{−(j+1)} (s̄−1+ρ)^{−(k+1)},     j,k = 0..n−1,
Hermitian; on-line zeros contribute rank-one POSITIVE terms (1−ρ̄ = ρ); an off-line FE pair
contributes an indefinite block.  RH ⟺ A(s) ⪰ 0 at every anchor (n=1 is Hinkkanen–Lagarias).
By partial fractions in ρ every entry is a finite combination of jets of ξ′/ξ at s and at 1−s̄
(= −conj jets at s), so for Re s > 1 the whole matrix is PRIME-COMPUTABLE (absolutely convergent
Dirichlet series).  Question: at such anchors, does an off-line pair at realistic depth change the
inertia?  If not, the prime side at σ>1 is blind and the seat construction must travel into the strip.

Pre-registration:
  Anchor s₀ = 1.1 + iT, T ∈ {20, 25}; n = 1..4.  Zero set: first 1000 zeros (γ>0) and conjugates.
  P1 (control): true configuration gives A(s₀) ⪰ 0 at every n (RH holds in range) — must hold.
  P2 (n=1 prime check): A_00(s₀) = 2 Re[ξ′/ξ(s₀)]/(2σ₀−1) with ξ′/ξ from E(s)+ζ′/ζ(s), ζ′/ζ from
      the von Mangoldt series at σ₀ = 1.1 (n ≤ 10^6): agreement < 1e−3 relative (tail of the zero
      sum and of the prime sum both ~1e−3).
  P3 (adversarial): plant an FE quadruple with ρ = β + iγ_p, β ∈ {0.6, 0.75, 0.9}, γ_p = 18
      (and its FE/conjugate partners), by adding the four resolvent terms.  PREDICTION: at σ₀ = 1.1
      the planted pair does NOT flip the inertia for β ≤ 0.75 at n ≤ 4 (relative change of λ_min
      below 10%); at β = 0.9 (pair within 0.2 of the anchor abscissa) it may.  Decision rule: an
      inertia flip at β ≤ 0.75 REFUTES "the σ>1 anchor is blind" and hands the seat a prime-side
      detector; no flip SUPPORTS it.
  P4 (the same plant seen from the strip): anchor s₁ = 0.7 + 18i (not prime-computable) — the
      resolution law says the pair is detected there; measure λ_min for the same plants as the
      contrast.
"""
import numpy as np, mpmath as mp, os, sys
mp.mp.dps = 20

def zeros(N, cache="tmp/zeta_zeros_%d.npy"):
    fn = cache % N
    if os.path.exists(fn):
        return np.load(fn)
    z = np.array([float(mp.zetazero(i).imag) for i in range(1, N + 1)])
    np.save(fn, z); return z

gam = zeros(1000)
rho_true = np.concatenate([0.5 + 1j*gam, 0.5 - 1j*gam])      # ρ and ρ̄ (= 1−ρ on the line)

def seat_form(s, rhos, n):
    A = np.zeros((n, n), dtype=complex)
    u = 1.0/(s - rhos)                 # (s−ρ)^{-1}
    v = 1.0/(np.conj(s) - 1 + rhos)    # (s̄−1+ρ)^{-1}
    for j in range(n):
        for k in range(n):
            A[j, k] = np.sum(u**(j+1) * v**(k+1))
    return (A + A.conj().T)/2

def inertia(A):
    ev = np.linalg.eigvalsh(A)
    tol = 1e-12*max(1, abs(ev).max())
    return (int((ev > tol).sum()), int((ev < -tol).sum())), ev

def E(s):
    return 1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2

def zeta_logderiv_series(s, N=10**6):
    # −Σ Λ(n) n^{−s}, sieve of Λ
    N = int(N)
    lam = np.zeros(N+1)
    sieve = np.ones(N+1, dtype=bool); sieve[:2] = False
    for i in range(2, int(N**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    for p in np.nonzero(sieve)[0]:
        pk = int(p)
        while pk <= N:
            lam[pk] = np.log(float(p)); pk *= int(p)
    n = np.arange(1, N+1, dtype=float)
    s = complex(s)
    return -np.sum(lam[1:] * n**(-s))

print("att542: prime-computable anchor vs off-line plant")
for T in (20.0, 25.0):
    s0 = 1.1 + 1j*T
    print("\n=== anchor s0 = %s ===" % s0)
    # P2: n=1 prime check
    A00 = seat_form(s0, rho_true, 1)[0, 0].real
    xi_ld = complex(E(mp.mpc(s0.real, s0.imag))) + zeta_logderiv_series(s0)
    scalar = 2*xi_ld.real/(2*s0.real - 1)
    print("P2  A_00 from zeros = %.6f ; 2Re[xi'/xi]/(2σ−1) from primes+Γ = %.6f ; rel diff %.2e"
          % (A00, scalar, abs(A00-scalar)/abs(scalar)))
    # P1: true inertia
    for n in (1, 2, 3, 4):
        ine, ev = inertia(seat_form(s0, rho_true, n))
        print("P1  n=%d true inertia=%s  lam_min=%.4e" % (n, ine, ev[0]))
    # P3: plants
    for beta in (0.6, 0.75, 0.9):
        gp = 18.0
        quad = np.array([beta + 1j*gp, beta - 1j*gp, 1-beta + 1j*gp, 1-beta - 1j*gp])
        rho_pl = np.concatenate([rho_true, quad])
        line = []
        for n in (1, 2, 3, 4):
            ine_t, ev_t = inertia(seat_form(s0, rho_true, n))
            ine_p, ev_p = inertia(seat_form(s0, rho_pl, n))
            line.append("n=%d %s lam_min %.3e→%.3e (Δrel %.1e)" % (n, ine_p, ev_t[0], ev_p[0], (ev_p[0]-ev_t[0])/abs(ev_t[0])))
        print("P3  plant β=%.2f at γ=%.0f: " % (beta, gp) + " | ".join(line))

# P4: strip anchor contrast
s1 = 0.7 + 18j
print("\n=== strip anchor s1 = %s (contrast, not prime-computable) ===" % s1)
for n in (1, 2, 3, 4):
    ine, ev = inertia(seat_form(s1, rho_true, n))
    print("P4  n=%d true inertia=%s lam_min=%.4e" % (n, ine, ev[0]))
for beta in (0.6, 0.75, 0.9):
    quad = np.array([beta + 18j, beta - 18j, 1-beta + 18j, 1-beta - 18j])
    rho_pl = np.concatenate([rho_true, quad])
    line = []
    for n in (1, 2, 3, 4):
        ine_p, ev_p = inertia(seat_form(s1, rho_pl, n))
        line.append("n=%d %s lam_min %.3e" % (n, ine_p, ev_p[0]))
    print("P4  plant β=%.2f: " % beta + " | ".join(line))
