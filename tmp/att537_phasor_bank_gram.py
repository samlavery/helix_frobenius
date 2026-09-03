#!/usr/bin/env python3
"""
att537 — the Weil form on the prime phasor bank: Gram matrices vs support length.

Pre-registration (ledger 537).
  Object.  For g smooth, supported in [-L, L], F_g(s) = ∫ g(x) e^{(s-1/2)x} dx and
           W(g) = Σ_ρ m_ρ F_g(ρ) conj(F_g(1 - conj ρ))   (= Σ_ρ |ĝ(τ_ρ)|² on RH).
  Instrument (compiled, WeilExplicitFormula.weil_explicit_formula_smooth applied to G = g ⋆ g~):
           W(g) = (1/2π)[∫ F_G(b+it) E(b+it) dt + ∫ F_G(a+it) E(1-a-it) dt]
                  − Σ_n Λ(n) n^{-1/2} (G(log n) + G(-log n)),    G(x) = ∫ g(y) conj g(y-x) dy,
           E(s) = 1/s + 1/(s-1) − ½ log π + ½ ψ(s/2),  a < 0 < 1 < b (we take a = -1/2, b = 3/2).
  Bank.    Basis g_j = smooth bump of width w centred at x_j ∈ (-L, L); Gram matrix
           M_jk = Σ_ρ conj(F_{g_j}(ρ)) F_{g_k}(1-conj ρ)... computed from the PRIME SIDE by polarisation
           of the compiled identity (bilinear form in (g_j, g_k)); smallest eigenvalue λ_min(L).
  Control. The same Gram matrix from the ZERO SIDE with the first N zeros (mpmath.zetazero),
           which are on the line: M_jk = Σ_ρ conj(ĝ_j(τ_ρ)) ĝ_k(τ_ρ). Agreement to the zero-tail
           error validates the compiled normalisation.
  Predictions (pre-registered):
    P1. Prime-side and zero-side Gram matrices agree to < 1e-3 relative (Frobenius) for L ≤ 1.5.
    P2. λ_min(L) > 0 for every L tested (positivity is RH-true in the range where all zeros are
        known to be on the line — this is NOT a test of RH, it is a positive control on the form).
    P3. λ_min(L) decreases as L grows; for 2L < log 2 no prime enters (Archimedean regime).
  Decision rule: P1 failing means a normalisation error in the instrument (not in the theorem —
  Lean checked it — but in this script's transcription); P2 failing means a bug; P3 is descriptive.
"""
import mpmath as mp
import numpy as np
import sys, time

mp.mp.dps = 20

# ---------- test functions: smooth bumps ----------
def bump(x, c, w):
    # C^∞ bump  exp(-1/(1-u^2)) on |u|<1, u=(x-c)/w
    u = (x - c) / w
    if abs(u) >= 1:
        return mp.mpf(0)
    return mp.e ** (-1 / (1 - u * u))

def laplace_bump(c, w, s):
    # F_g(s) = ∫ g(x) e^{(s-1/2)x} dx over [c-w, c+w]
    f = lambda x: bump(x, c, w) * mp.e ** ((s - mp.mpf(1) / 2) * x)
    return mp.quad(f, [c - w, c, c + w])

def G_pair(cj, ck, w, x):
    # G_{jk}(x) = ∫ g_j(y) conj(g_k(y - x)) dy   (real bumps)
    lo = max(cj - w, ck - w + x); hi = min(cj + w, ck + w + x)
    if hi <= lo:
        return mp.mpf(0)
    f = lambda y: bump(y, cj, w) * bump(y - x, ck, w)
    return mp.quad(f, [lo, hi])

def E(s):
    return 1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2

# ---------- prime side ----------
def primes_upto(N):
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return np.nonzero(sieve)[0]

def vonmangoldt_terms(xmax):
    # (n, Λ(n)) for n = p^k ≤ e^{xmax}
    N = int(mp.e ** xmax) + 1
    out = []
    for p in primes_upto(N):
        pk = int(p)
        while pk <= N:
            out.append((pk, mp.log(p)))
            pk *= int(p)
    return out

def gram_prime_side(centres, w, L, a=mp.mpf(-1) / 2, b=mp.mpf(3) / 2):
    n = len(centres)
    M = mp.matrix(n, n)
    # polarised form: B(g_j, g_k) = Σ_ρ conj(F_j(ρ))... via the identity applied to G_{jk}
    # F_{G_jk}(s) = F_j(s) * conj(F_k(1 - conj s))   (real bumps)
    terms = vonmangoldt_terms(2 * L + 1e-9)
    for j, cj in enumerate(centres):
        for k, ck in enumerate(centres):
            Fj = lambda s: laplace_bump(cj, w, s)
            Fk = lambda s: laplace_bump(ck, w, s)
            FG = lambda s: Fj(s) * mp.conj(Fk(1 - mp.conj(s)))
            # Archimedean line integrals (integrands decay like the bumps' transforms)
            T = 60
            arch_b = mp.quad(lambda t: FG(b + 1j * t) * E(b + 1j * t), [-T, -10, 0, 10, T])
            arch_a = mp.quad(lambda t: FG(a + 1j * t) * E(1 - a - 1j * t), [-T, -10, 0, 10, T])
            arch = (arch_b + arch_a) / (2 * mp.pi)
            prime = mp.mpf(0)
            for (nn, lam) in terms:
                x = mp.log(nn)
                prime += lam / mp.sqrt(nn) * (G_pair(cj, ck, w, x) + G_pair(cj, ck, w, -x))
            M[j, k] = arch - prime
    return M

# ---------- zero side (control) ----------
def gram_zero_side(centres, w, nzeros):
    n = len(centres)
    M = mp.matrix(n, n)
    zs = [mp.zetazero(i).imag for i in range(1, nzeros + 1)]
    Fhat = [[laplace_bump(c, w, mp.mpf(1) / 2 + 1j * t) for t in zs] for c in centres]
    for j in range(n):
        for k in range(n):
            M[j, k] = mp.fsum(mp.conj(Fhat[j][i]) * Fhat[k][i] for i in range(nzeros))
    return M

def eigmin(M):
    A = np.array([[complex(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])
    A = (A + A.conj().T) / 2
    return float(np.linalg.eigvalsh(A).min()), float(np.linalg.eigvalsh(A).max())

if __name__ == "__main__":
    quick = "--quick" in sys.argv
    Ls = [0.30, 0.34, 0.5, 0.8, 1.2] if not quick else [0.30, 0.8]
    nb = 3          # basis size per L (small: each entry is a triple quadrature)
    nzeros = 400 if not quick else 150
    print("att537 phasor-bank Gram: L, w, lam_min(prime side), lam_max, rel Frobenius diff vs zero side (N=%d zeros)" % nzeros)
    for L in Ls:
        w = L / nb
        centres = [mp.mpf(-L + w + 2 * w * i) for i in range(nb)]
        t0 = time.time()
        Mp = gram_prime_side(centres, w, L)
        Mz = gram_zero_side(centres, w, nzeros)
        lm, lM = eigmin(Mp)
        diff = mp.mnorm(Mp - Mz, 'F') / mp.mnorm(Mz, 'F')
        nterms = len(vonmangoldt_terms(2 * L + 1e-9))
        print("L=%.2f w=%.3f primes(n<=e^{2L})=%d  lam_min=%.6e lam_max=%.6e  relFrob(prime vs zero)=%.2e  (%.0fs)"
              % (L, w, nterms, lm, lM, float(diff), time.time() - t0))
        sys.stdout.flush()
