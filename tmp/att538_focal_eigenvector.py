#!/usr/bin/env python3
"""
att538 — Sam's "focal cancellation and an eigenvalue", run on the compiled Weil form.

The Weil form on the phasor bank is positive definite at every support length L, with smallest
eigenvalue λ_min(L) → 0 as primes enter (att537b). The minimal eigenvector g_* is the profile along
which the Archimedean (diagonal) part and the prime phasors (off-diagonal, frequencies ±log n)
nearly cancel: focal alignment of the bank. This script asks what g_* IS.

Pre-registration (ledger 538):
  Basis: nb bumps of width w = L/nb on [-L, L]; Gram from the prime side (compiled identity).
  Outputs for the minimal eigenvector g_*:
    (a) λ_min, and the split  W(g_*) = Arch(g_*) − Prime(g_*)  (both ≥ 0 individually? measured).
    (b) |ĝ_*(τ)|² on τ ∈ [0, 60] against the first zeros: does g_* avoid the zeros (mass between
        them) or sit on them?  Prediction P1: since W(g_*) = Σ_ρ |ĝ_*(τ_ρ)|² is tiny, |ĝ_*|² is
        SMALL AT EVERY ZERO and its mass sits between zeros — the focal profile is the one the
        zero comb cannot see.
    (c) The prime content: the autocorrelation G_*(log n) for prime powers n ≤ e^{2L} — which
        clocks carry the cancellation. Prediction P2: dominated by n = 2, 3, 4 (largest Λ(n)n^{-1/2}
        within reach).
    (d) Shape: is g_* a near-uniform profile (a DC on the bank) or oscillatory?  Prediction P3:
        smooth and low-frequency (the form penalises high frequency through the Archimedean term
        growth ~ log|τ|).
  Decision rule: P1 fails if |ĝ_*(τ_ρ)|² at the first zeros is comparable to the peak of |ĝ_*|².
"""
import numpy as np, sys
sys.path.insert(0, "tmp")
from att537b_phasor_bank_gram_fast import F_on, G_pair, E, vonmangoldt_terms, zeros, gram_prime_side
from scipy.special import digamma

np.set_printoptions(precision=4, suppress=True, linewidth=140)
zs = zeros(1000)

def analyse(L, nb):
    w = L / nb
    centres = [-L + w + 2 * w * i for i in range(nb)]
    Mp, nt = gram_prime_side(centres, w, L)
    H = (Mp + Mp.conj().T) / 2
    ev, V = np.linalg.eigh(H)
    v = V[:, 0]                              # minimal eigenvector (coefficients on the bumps)
    v = v / np.linalg.norm(v)
    print("\n=== L=%.2f nb=%d w=%.3f  prime powers=%d ===" % (L, nb, w, nt))
    print("eigenvalues:", ev)
    print("minimal eigenvector coefficients (real part):", v.real)
    print("                                 (imag part):", v.imag)
    # (a) Arch / prime split along v, computed from the same pieces
    a, b = -0.5, 1.5
    t = np.arange(-250, 250 + 0.005, 0.01)
    sb = b + 1j * t; sa = a + 1j * t
    Fb = sum(v[j] * F_on(c, w, sb) for j, c in enumerate(centres))
    Fb_r = sum(np.conj(v[k]) * np.conj(F_on(c, w, 1 - np.conj(sb))) for k, c in enumerate(centres))
    Fa = sum(v[j] * F_on(c, w, sa) for j, c in enumerate(centres))
    Fa_r = sum(np.conj(v[k]) * np.conj(F_on(c, w, 1 - np.conj(sa))) for k, c in enumerate(centres))
    arch = (np.trapezoid(Fb * Fb_r * E(sb), t) + np.trapezoid(Fa * Fa_r * E(1 - sa), t)) / (2 * np.pi)
    terms = vonmangoldt_terms(2 * L + 1e-9)
    prime_terms = []
    for (nn, lam) in terms:
        x0 = np.log(nn)
        Gp = sum(v[j] * np.conj(v[k]) * (G_pair(centres[j], centres[k], w, x0) + G_pair(centres[j], centres[k], w, -x0))
                 for j in range(nb) for k in range(nb))
        prime_terms.append((nn, (lam / np.sqrt(nn) * Gp).real))
    prime = sum(p for _, p in prime_terms)
    print("(a) W(g*) = %.4e ;  Arch(g*) = %.4e ; Prime(g*) = %.4e ; Arch − Prime = %.4e"
          % (ev[0], arch.real, prime, arch.real - prime))
    # (b) |ĝ*(τ)|² on [0,60] vs zeros
    tau = np.linspace(0, 60, 6001)
    ghat = sum(v[j] * F_on(c, w, 0.5 + 1j * tau) for j, c in enumerate(centres))
    p2 = np.abs(ghat) ** 2
    zsm = zs[zs < 60]
    at_zeros = np.abs(sum(v[j] * F_on(c, w, 0.5 + 1j * zsm) for j, c in enumerate(centres))) ** 2
    print("(b) peak |ĝ*|² on [0,60] = %.4e at τ=%.2f ; |ĝ*|² at the %d zeros below 60: max %.4e mean %.4e ; ratio max/peak = %.3f"
          % (p2.max(), tau[p2.argmax()], len(zsm), at_zeros.max(), at_zeros.mean(), at_zeros.max() / p2.max()))
    # local minima of |ĝ*|² vs zero positions
    mins = tau[1:-1][(p2[1:-1] < p2[:-2]) & (p2[1:-1] < p2[2:])]
    print("    local minima of |ĝ*|² below 60:", np.round(mins[:12], 2))
    print("    first zeros                    :", np.round(zsm[:12], 2))
    # (c) prime content
    prime_terms.sort(key=lambda x: -abs(x[1]))
    print("(c) largest prime-phasor terms Λ(n)n^{-1/2}(G*(log n)+G*(-log n)):",
          [(n, "%.3e" % p) for n, p in prime_terms[:6]])
    # (d) shape: sign changes of the coefficient vector
    sc = int(np.sum(np.sign(v.real[:-1]) != np.sign(v.real[1:])))
    print("(d) sign changes along the bank coefficients: %d of %d" % (sc, nb - 1))

if __name__ == "__main__":
    analyse(1.2, 6)
    analyse(2.5, 8)
    analyse(3.5, 10)
