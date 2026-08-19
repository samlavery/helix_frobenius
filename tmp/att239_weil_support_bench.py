#!/usr/bin/env python3
"""
att239 — Weil-form SUPPORT-SIDE bench (the seat/census Weil-positivity track).

Conventions (Bombieri 2000 normalization, additive coordinates):
  u = log x, F(u) = e^{u/2} f(e^u); f = g * g~ (mult) <=> F = autocorrelation of G,
  G real EVEN (the sigma+ sector), support [-a, a]; f-side support L = 2a.
  Weil form:
    Q(G) = 2 P^2 - 2 sum_n Lambda(n) n^{-1/2} F(log n) - A(F)
    P    = int G(u) cosh(u/2) du          (pole pair f~(0)+f~(1) = 2P^2)
    A(F) = (log 4pi + gamma) F(0)
           + int_0^{2a} [2 e^{-u/2} F(u) - 2 e^{-u} F(0)] / (1 - e^{-2u}) du
           - 2 F(0) artanh(e^{-2a})                       (exact tail, u > 2a)
  RH <=> Q >= 0 for all such G (all supports).  On-line zero: contributes Ghat(gamma)^2.

PRE-REGISTERED FALSIFICATION LINES:
  F1 arithmetic-side vs zero-side must agree (else conventions wrong -> stop).
  F2 arch-only lambda_min at L=log2 should match CC zeta-cycles ~ +0.00133
     (up to their operator normalization), sign change just beyond log 2.
  F3 (hypothesis) handoff criticality: lambda_min -> 0 at L -> log m for every
     prime power m (measured at 3 in att240; here we establish the instrument).
"""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh, null_space

EULER = np.euler_gamma
LOG2, LOG3 = np.log(2.0), np.log(3.0)

# ---------------------------------------------------------------- basis pieces
def omegas(K, a):
    return np.arange(K + 1) * np.pi / a

def gram(K, a):
    d = np.full(K + 1, a); d[0] = 2 * a
    return np.diag(d)

def T_piece(sig, phi, v0, v1):
    """int_{v0}^{v1} cos(sig*v - phi) dv, vectorized, sig may contain exact 0."""
    out = np.empty(np.broadcast(sig, phi).shape)
    z = (sig == 0.0)
    s = np.where(z, 1.0, sig)
    out = (np.sin(s * v1 - phi) - np.sin(s * v0 - phi)) / s
    if np.any(z):
        out = np.where(z, (v1 - v0) * np.cos(phi), out)
    return out

def S_all(u, K, a):
    """Symmetrized correlation matrix S_jk(u) = sym int phi_j(v) phi_k(v-u) dv,
    for 0 <= u <= 2a; support edge: returns 0-matrix beyond."""
    if u >= 2 * a:
        return np.zeros((K + 1, K + 1))
    om = omegas(K, a)
    al = om[:, None]; be = om[None, :]
    v0, v1 = u - a, a
    I = 0.5 * (T_piece(al + be, be * u, v0, v1) + T_piece(al - be, -be * u, v0, v1))
    return 0.5 * (I + I.T)

def pole_vec(K, a):
    """p_k = int_{-a}^{a} cos(om_k u) cosh(u/2) du  (closed form)."""
    om = omegas(K, a)
    k = np.arange(K + 1)
    return ((-1.0) ** k) * np.sinh(a / 2) / (0.25 + om ** 2)

def zero_freq_vec(K, a):
    q = np.zeros(K + 1); q[0] = 2 * a
    return q

def ghat(c, r, K, a):
    """Ghat(r) = int G cos(ru) du for real r array."""
    om = omegas(K, a)
    rp = om[:, None] + r[None, :]
    rm = om[:, None] - r[None, :]
    def sc(x):
        y = np.where(np.abs(x) < 1e-12, 1.0, x)
        return np.where(np.abs(x) < 1e-12, a, np.sin(y * a) / y)
    B = sc(rp) + sc(rm)
    return c @ B

# ---------------------------------------------------------------- arch block
def arch_matrix(K, a, Nq=1000):
    x, w = leggauss(Nq)
    u = (x + 1) * a            # (0, 2a)
    wq = w * a
    S0 = S_all(0.0, K, a)
    A = (np.log(4 * np.pi) + EULER) * S0 - 2 * np.arctanh(np.exp(-2 * a)) * S0
    for ui, wi in zip(u, wq):
        Su = S_all(ui, K, a)
        A += wi * (2 * np.exp(-ui / 2) * Su - 2 * np.exp(-ui) * S0) / (1 - np.exp(-2 * ui))
    return A

# ---------------------------------------------------------------- assembly
def prime_powers(L):
    """(n, Lambda(n)) for log n strictly inside the support."""
    out = []
    N = int(np.floor(np.exp(L))) + 1
    for n in range(2, N + 1):
        if np.log(n) >= L:
            continue
        m, p = n, None
        for q in range(2, int(np.sqrt(n)) + 1):
            if m % q == 0:
                p = q
                while m % q == 0:
                    m //= q
                break
        if p is None:
            out.append((n, np.log(n)))        # n prime
        elif m == 1:
            out.append((n, np.log(p)))        # prime power
    return out

def weil_matrix(L, K=30, Nq=1000, primes=True, pole=True):
    a = L / 2.0
    M = -arch_matrix(K, a, Nq)
    if primes:
        for n, lam in prime_powers(L):
            M -= 2.0 * (lam / np.sqrt(n)) * S_all(np.log(n), K, a)
    if pole:
        p = pole_vec(K, a)
        M += 2.0 * np.outer(p, p)
    return M

def lam_min(L, K=30, Nq=1000, primes=True, constraints=("pole", "zero")):
    """min of Q(G)/||G||^2 on the constrained even sector; pole term dropped
    when 'pole' is constrained (it vanishes there anyway)."""
    a = L / 2.0
    M = weil_matrix(L, K, Nq, primes=primes, pole=("pole" not in constraints))
    N = gram(K, a)
    rows = []
    if "pole" in constraints:
        rows.append(pole_vec(K, a))
    if "zero" in constraints:
        rows.append(zero_freq_vec(K, a))
    if rows:
        Z = null_space(np.array(rows))
        lam, V = eigh(Z.T @ M @ Z, Z.T @ N @ Z)
        return lam[0], Z @ V[:, 0]
    lam, V = eigh(M, N)
    return lam[0], V[:, 0]

# ---------------------------------------------------------------- self-tests
def self_tests():
    print("== SELF-TESTS ==")
    K, a = 8, 0.55
    rng = np.random.default_rng(7)
    # (1) closed-form correlation vs brute quadrature
    worst = 0.0
    x, w = leggauss(4000)
    for _ in range(12):
        j, k = rng.integers(0, K + 1, 2)
        u = rng.uniform(0, 2 * a)
        v = (x + 1) / 2 * (a - (u - a)) + (u - a)
        wv = w / 2 * (a - (u - a))
        om = omegas(K, a)
        brute = np.sum(wv * np.cos(om[j] * v) * np.cos(om[k] * (v - u)))
        bruteT = np.sum(wv * np.cos(om[k] * v) * np.cos(om[j] * (v - u)))
        S = S_all(u, K, a)
        worst = max(worst, abs(S[j, k] - 0.5 * (brute + bruteT)))
    print(f"  corr closed-form vs quad : worst |diff| = {worst:.3e}")
    # (2) Gram check
    print(f"  S(0) vs Gram             : {np.max(np.abs(S_all(0,K,a)-gram(K,a))):.3e}")
    # (3) pole vector vs quadrature
    v = (x + 1) / 2 * 2 * a - a; wv = w / 2 * 2 * a
    om = omegas(K, a)
    pb = np.array([np.sum(wv * np.cos(om[k] * v) * np.cosh(v / 2)) for k in range(K + 1)])
    print(f"  pole vec closed vs quad  : {np.max(np.abs(pb - pole_vec(K,a))):.3e}")

def validate_arch_density(K=6, a=0.55):
    """A-route (u-integral) vs psi-density route on the Hann window G."""
    print("== ARCH TWO-ROUTE CHECK (Hann window) ==")
    c = np.zeros(K + 1); c[0], c[1] = 0.5, 0.5
    A_route = c @ arch_matrix(K, a) @ c
    try:
        from scipy.special import digamma
        cplx = np.asarray(digamma(0.25 + 0.5j))
        use_scipy = np.isfinite(cplx.real)
    except Exception:
        use_scipy = False
    x, w = leggauss(4000)
    R = 400.0
    r = (x + 1) / 2 * R; wr = w / 2 * R
    G2 = ghat(c, r, K, a) ** 2
    if use_scipy:
        from scipy.special import digamma
        dens = np.real(digamma(0.25 + 0.5j * r)) - np.log(np.pi)
    else:
        import mpmath as mp
        dens = np.array([float(mp.re(mp.digamma(0.25 + 0.5j * ri))) for ri in r]) - np.log(np.pi)
    dens_route = -(1.0 / np.pi) * np.sum(wr * dens * G2)
    print(f"  A(F) u-integral route    : {A_route:+.10f}")
    print(f"  -1/2pi int dens*|Ghat|^2 : {dens_route:+.10f}")
    print(f"  diff                     : {A_route - dens_route:+.3e}"
          f"   (gamma/2*F0 would be {EULER/2*(c@S_all(0,K,a)@c):+.3e})")

def validate_zeros(L, K=8, tag=""):
    """Global EF check: Q via arithmetic side vs Q via 35673 actual zeros."""
    a = L / 2.0
    c = np.zeros(K + 1); c[0], c[1] = 0.5, 0.5       # Hann: smooth, Ghat ~ r^-3
    M = weil_matrix(L, K, primes=True, pole=True)
    Q_arith = c @ M @ c
    z = np.load("att015_zeros_to_30000.npy")
    Gz = ghat(c, z, K, a)
    Q_zero = 2.0 * np.sum(Gz ** 2)
    # tail beyond 30000 via RvM density (utterly small for Hann, printed anyway)
    x, w = leggauss(200)
    r = 30000.0 + (x + 1) / 2 * 200000.0; wr = w / 2 * 200000.0
    tail = np.sum(wr * (np.log(r / (2 * np.pi)) / (2 * np.pi)) * 2 * ghat(c, r, K, a) ** 2)
    pp = [n for n, _ in prime_powers(L)]
    print(f"  L={L:.4f} {tag} primes={pp}")
    print(f"    Q arithmetic side : {Q_arith:+.10f}")
    print(f"    Q zero side       : {Q_zero + tail:+.10f}   (tail est {tail:.2e})")
    print(f"    rel diff          : {abs(Q_arith-(Q_zero+tail))/abs(Q_arith):.3e}")

# ---------------------------------------------------------------- the bench
def main():
    self_tests()
    validate_arch_density()
    print("== GLOBAL EF VALIDATION (arithmetic vs actual zeros) ==")
    validate_zeros(1.20, tag="(crosses log2, log3? no: log3=1.0986<1.2 -> {2,3})")
    validate_zeros(1.90, tag="({2,3,4,5})")

    print("== CC ANCHORS: arch-only, constraints (pole, zero) ==")
    for L in [0.60, 0.65, LOG2, LOG2 + 0.005, LOG2 + 0.01, LOG2 + 0.02,
              LOG2 + 0.05, LOG2 + 0.10, LOG2 + 0.20]:
        lam, _ = lam_min(L, K=30, primes=False)
        print(f"  L = {L:.4f} (e^L = {np.exp(L):.4f})  lam_min(arch-only) = {lam:+.6e}")

    print("== RUNG (log2, log3): arch + prime-2, constraints (pole, zero) ==")
    for L in np.concatenate([np.linspace(LOG2 + 0.01, LOG3 - 0.01, 12),
                             [LOG3 - 0.005, LOG3 - 0.002, LOG3]]):
        lam, _ = lam_min(L, K=30, primes=True)
        print(f"  L = {L:.5f} (e^L = {np.exp(L):.4f})  lam_min = {lam:+.6e}")

    print("== K-CONVERGENCE at L = 1.00 (arch+p2) ==")
    for K in [20, 30, 40, 50]:
        lam, _ = lam_min(1.00, K=K, primes=True)
        print(f"  K = {K}:  lam_min = {lam:+.9e}")

    print("== UNCONSTRAINED (true Weil criterion, pole term in) sanity ==")
    for L in [0.60, 1.00, LOG3 - 0.01]:
        lam, _ = lam_min(L, K=30, primes=True, constraints=())
        print(f"  L = {L:.4f}  lam_min(no constraints) = {lam:+.6e}")

if __name__ == "__main__":
    main()
