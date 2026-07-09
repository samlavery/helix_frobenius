"""RUNG 3 STAGE 2 — the KATZ-BASIS overconvergent ordinary projection (the CORRECT method).

The prior ad-hoc attempts (Krylov-of-Φ, T_ℓ projectors) leaked the non-ordinary tail because
they never represented U_p as a genuine finite matrix.  Lauder's method does: on a fixed Katz
basis of p/(p+1)-overconvergent forms, U_p IS a finite matrix, and e_ord is its unit-eigenvalue
spectral projector — no q^{p^d} depth, no contamination.

Coefficients are plain integers mod p^prec (we work over Q_13 = f=1; ζ12 ∈ Z_13).

Foundation (verified): E_{p-1} = E_12 (p=13), the Hasse-invariant lift E_12 ≡ 1 mod 13; its
inverse E_12^{-1}; the Katz basis {W_i · E_12^{-i}}.
"""
import sympy as sp
from fractions import Fraction as Q


def sigma(k, n):
    return sum(int(d) ** k for d in sp.divisors(int(n)))


def eisenstein_pm1(p, prec, M):
    """E_{p-1} to q^M as integers mod p^prec.  E_k = 1 − (2k/B_k) Σ σ_{k-1}(n) q^n.
    For p=13, k=12: −2k/B_k = 65520/691.  E_{p-1} ≡ 1 mod p (Hasse lift)."""
    mod = p ** prec
    k = p - 1
    Bk = sp.bernoulli(k)                      # B_12 = -691/2730
    lead = (-2 * k) / Bk                      # sympy Rational 65520/691
    num, den = int(sp.fraction(lead)[0]), int(sp.fraction(lead)[1])
    ld = (num % mod) * pow(den % mod, -1, mod) % mod
    a = [0] * M
    a[0] = 1
    for n in range(1, M):
        a[n] = (ld * sigma(k - 1, n)) % mod
    return a, mod


def series_inv(A, mod):
    """Inverse power series of A (A[0] a unit) mod `mod`."""
    M = len(A)
    B = [0] * M
    B[0] = pow(A[0] % mod, -1, mod)
    for n in range(1, M):
        s = 0
        for k in range(1, n + 1):
            s = (s + A[k] * B[n - k]) % mod
        B[n] = (-B[0] * s) % mod
    return B


def series_mul(A, B, mod, M=None):
    if M is None:
        M = min(len(A), len(B))
    C = [0] * M
    for i in range(min(len(A), M)):
        if A[i]:
            for j in range(min(len(B), M - i)):
                if B[j]:
                    C[i + j] = (C[i + j] + A[i] * B[j]) % mod
    return C


def U_p_series(A, p, M):
    """(U_p A)_n = A_{pn}, truncated to q^M (needs A to q^{pM} for full validity)."""
    return [A[p * n] if p * n < len(A) else 0 for n in range(M)]


def V_p_series(A, p, M):
    """(V_p A)_n = A_{n/p} (Frobenius): A_{n/p} if p|n else 0."""
    return [A[n // p] if n % p == 0 else 0 for n in range(M)]


def p_deplete(A, p):
    """Remove p-divisible-index terms: a_n = 0 for p|n (the [p] operator)."""
    return [A[n] if n % p != 0 else 0 for n in range(len(A))]
