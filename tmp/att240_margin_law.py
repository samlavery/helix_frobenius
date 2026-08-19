#!/usr/bin/env python3
"""
att240 — the support-side Weil margin LAW (follows att239's validated bench).

Measured in att239 (even sector, unconstrained, primes in):
  lam_min: 7.6e-3 (L=0.6) -> 9.6e-7 (L=1.0) -> 8.2e-8 (L=log3).
Crude slopes suggest ln lam ~ -gamma1 * L^2-type collapse (gamma1 = 14.1347...).

PRE-REGISTERED here:
  H1 (law): ln lam_min(L) is smooth; candidate models  a + b*L  vs  a + b*L + c*L^2;
     house constants to compare: 2*gamma1 = 28.2694 (slope) / gamma1 (curvature rate).
  H2 (clocks): if the prime terms are load-bearing, arch-only lam_min goes NEGATIVE
     somewhere and the prime term restores it; if instead the collapse is a pure
     zero-clock (first-zero) phenomenon, the curve is smooth through log2/log3 and
     arch-only stays positive far past log2.  These are DISTINGUISHABLE — measure.
  H3 (sectors): odd sector has pole term -2*Po^2 (derived); its margin may collapse
     differently.  Validated against actual zeros before use.
Falsification lines: a negative lam_min anywhere (primes in) at these supports would
contradict the verified zeros — treat as instrument failure, not discovery.
"""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh, null_space
import att239_weil_support_bench as B

EULER = np.euler_gamma
LOG2, LOG3, LOG4, LOG5 = map(np.log, (2.0, 3.0, 4.0, 5.0))
GAMMA1 = 14.134725141734695

# ------------------------------------------------------------ odd sector pieces
def S_all_odd(u, K, a):
    if u >= 2 * a:
        return np.zeros((K, K))
    om = (np.arange(1, K + 1)) * np.pi / a
    al = om[:, None]; be = om[None, :]
    v0, v1 = u - a, a
    I = 0.5 * (B.T_piece(al - be, -be * u, v0, v1) - B.T_piece(al + be, be * u, v0, v1))
    return 0.5 * (I + I.T)

def gram_odd(K, a):
    return np.diag(np.full(K, a))

def pole_vec_odd(K, a):
    k = np.arange(1, K + 1)
    om = k * np.pi / a
    return -2.0 * om * np.sinh(a / 2) * ((-1.0) ** k) / (0.25 + om ** 2)

def ghat_odd(c, r, K, a):
    om = (np.arange(1, K + 1)) * np.pi / a
    rm = om[:, None] - r[None, :]
    rp = om[:, None] + r[None, :]
    def sc(x):
        y = np.where(np.abs(x) < 1e-12, 1.0, x)
        return np.where(np.abs(x) < 1e-12, a, np.sin(y * a) / y)
    return c @ (sc(rm) - sc(rp))

def arch_matrix_odd(K, a, Nq=1000):
    x, w = leggauss(Nq)
    u = (x + 1) * a; wq = w * a
    S0 = S_all_odd(0.0, K, a)
    A = (np.log(4 * np.pi) + EULER) * S0 - 2 * np.arctanh(np.exp(-2 * a)) * S0
    for ui, wi in zip(u, wq):
        Su = S_all_odd(ui, K, a)
        A += wi * (2 * np.exp(-ui / 2) * Su - 2 * np.exp(-ui) * S0) / (1 - np.exp(-2 * ui))
    return A

def weil_matrix_odd(L, K=30, Nq=1000, primes=True):
    a = L / 2.0
    M = -arch_matrix_odd(K, a, Nq)
    if primes:
        for n, lam in B.prime_powers(L):
            M -= 2.0 * (lam / np.sqrt(n)) * S_all_odd(np.log(n), K, a)
    p = pole_vec_odd(K, a)
    M -= 2.0 * np.outer(p, p)          # odd-sector pole pair is NEGATIVE (derived)
    return M

def lam_min_sector(L, sector="even", K=35, Nq=1200, primes=True):
    a = L / 2.0
    if sector == "even":
        M = B.weil_matrix(L, K, Nq, primes=primes, pole=True)
        N = B.gram(K, a)
    else:
        M = weil_matrix_odd(L, K, Nq, primes=primes)
        N = gram_odd(K, a)
    lam, V = eigh(M, N)
    return lam[0], V[:, 0]

# ------------------------------------------------------------ runs
def odd_zero_validation():
    print("== ODD SECTOR: global EF validation vs actual zeros ==")
    L, K = 1.2, 8
    a = L / 2.0
    c = np.zeros(K); c[0], c[1], c[2] = 1.0, 0.5, 0.25
    M = weil_matrix_odd(L, K)
    Q_arith = c @ M @ c
    z = np.load("att015_zeros_to_30000.npy")
    Gz = ghat_odd(c, z, K, a)
    Q_zero = 2.0 * np.sum(Gz ** 2)
    x, w = leggauss(200)
    r = 30000.0 + (x + 1) / 2 * 200000.0; wr = w / 2 * 200000.0
    tail = np.sum(wr * (np.log(r / (2 * np.pi)) / (2 * np.pi)) * 2 * ghat_odd(c, r, K, a) ** 2)
    print(f"  Q arithmetic: {Q_arith:+.10f}   Q zeros: {Q_zero + tail:+.10f}"
          f"   rel diff {abs(Q_arith-(Q_zero+tail))/abs(Q_arith):.3e}")

def k_convergence():
    print("== K-CONVERGENCE of the tiny margins (even, unconstrained, primes in) ==")
    for L in [1.00, LOG3, 1.12]:
        vals = []
        for K in [30, 45, 60, 80]:
            lam, _ = lam_min_sector(L, "even", K=K, Nq=max(1200, 30 * K))
            vals.append(lam)
            print(f"  L = {L:.4f}  K = {K:2d}:  lam_min = {lam:+.9e}")
        d1 = vals[-2] - vals[-1]
        print(f"    K-tail estimate (K60->K80 change): {d1:+.2e}")

def fine_scan():
    print("== FINE L-SCAN (primes in, both sectors) ==")
    grid = sorted(set(
        list(np.arange(0.45, 1.14, 0.025)) +
        [LOG2 - 0.006, LOG2 - 0.003, LOG2, LOG2 + 0.003, LOG2 + 0.006,
         LOG3 - 0.006, LOG3 - 0.003, LOG3, LOG3 + 0.003, LOG3 + 0.006,
         1.11, 1.12, 1.13]))
    out = []
    print(f"  {'L':>8} {'e^L':>7} {'lam_even':>14} {'lam_odd':>14}")
    for L in grid:
        le, _ = lam_min_sector(L, "even")
        lo, _ = lam_min_sector(L, "odd")
        out.append((L, le, lo))
        print(f"  {L:8.5f} {np.exp(L):7.4f} {le:+14.6e} {lo:+14.6e}")
    return out

def law_fit(data):
    print("== LAW FIT: ln lam vs L (even sector, lam > 1e-12) ==")
    L = np.array([d[0] for d in data]); lam = np.array([d[1] for d in data])
    m = lam > 1e-12
    x, y = L[m], np.log(lam[m])
    # model 1: linear
    A1 = np.vstack([np.ones_like(x), x]).T
    c1, res1, *_ = np.linalg.lstsq(A1, y, rcond=None)
    # model 2: quadratic
    A2 = np.vstack([np.ones_like(x), x, x ** 2]).T
    c2, res2, *_ = np.linalg.lstsq(A2, y, rcond=None)
    print(f"  linear   : ln lam = {c1[0]:+.3f} {c1[1]:+.3f}*L"
          f"        rms {np.sqrt(res1[0]/len(x)) if len(res1) else 0:.3f}"
          f"   [2*gamma1 = {2*GAMMA1:.4f}]")
    print(f"  quadratic: ln lam = {c2[0]:+.3f} {c2[1]:+.3f}*L {c2[2]:+.3f}*L^2"
          f"  rms {np.sqrt(res2[0]/len(x)) if len(res2) else 0:.3f}"
          f"   [gamma1 = {GAMMA1:.4f}]")
    # local slopes around clocks (kink test)
    print("  local d(ln lam)/dL near clocks (kink test):")
    for Lc, name in [(LOG2, "log2"), (LOG3, "log3")]:
        lo = [d for d in data if Lc - 0.007 < d[0] < Lc - 0.001]
        hi = [d for d in data if Lc + 0.001 < d[0] < Lc + 0.007]
        at = [d for d in data if abs(d[0] - Lc) < 1e-9]
        if lo and hi and at:
            sl = (np.log(at[0][1]) - np.log(lo[-1][1])) / (at[0][0] - lo[-1][0])
            sh = (np.log(hi[0][1]) - np.log(at[0][1])) / (hi[0][0] - at[0][0])
            print(f"    {name}: slope below = {sl:+.2f}, above = {sh:+.2f}, jump = {sh-sl:+.2f}")

def arch_only_and_rescue():
    print("== ARCH-ONLY (primes OFF) vs primes ON — the load-bearing test ==")
    print(f"  {'L':>8} {'lam_arch_only':>15} {'lam_with_primes':>16} {'prime effect':>13}")
    for L in [0.60, LOG2, 0.75, 0.80, 0.85, 0.90, 0.95, 1.00, 1.05, LOG3, 1.12]:
        la, _ = lam_min_sector(L, "even", primes=False)
        lp, _ = lam_min_sector(L, "even", primes=True)
        print(f"  {L:8.5f} {la:+15.6e} {lp:+16.6e} {lp-la:+13.2e}")

def portraits():
    print("== MINIMIZER PORTRAITS (even, unconstrained) ==")
    for L in [1.00, LOG3]:
        K, a = 45, L / 2.0
        lam, c = lam_min_sector(L, "even", K=K, Nq=1600)
        c = c / np.sqrt(c @ B.gram(K, a) @ c)
        P = c @ B.pole_vec(K, a)
        F0 = c @ B.S_all(0.0, K, a) @ c
        Flog2 = c @ B.S_all(LOG2, K, a) @ c
        A = c @ B.arch_matrix(K, a, 1600) @ c
        prime_term = 0.0
        for n, lamn in B.prime_powers(L):
            prime_term += -2.0 * (lamn / np.sqrt(n)) * (c @ B.S_all(np.log(n), K, a) @ c)
        print(f"  L = {L:.4f}: lam = {lam:+.4e}")
        print(f"    P (pole amp)  = {P:+.6e}   -> pole term 2P^2 = {2*P*P:+.6e}")
        print(f"    F(0)          = {F0:+.6f}")
        print(f"    F(log2)       = {Flog2:+.6e}   (prime-2 reads -2*(log2/sqrt2)*this)")
        print(f"    prime term    = {prime_term:+.6e}")
        print(f"    arch term -A  = {-A:+.6e}")
        print(f"    total check   = {2*P*P + prime_term - A:+.6e}  (should = lam)")
        us = np.linspace(0, a, 9)
        om = B.omegas(K, a)
        Gv = [float(c @ np.cos(om * u)) for u in us]
        print("    G(u) profile  : " + "  ".join(f"{g:+.3f}" for g in Gv))
        us2 = np.linspace(0, 2 * a, 9)
        Fv = [float(c @ B.S_all(u, K, a) @ c) for u in us2]
        print("    F(u) profile  : " + "  ".join(f"{f:+.4f}" for f in Fv))

def main():
    odd_zero_validation()
    k_convergence()
    data = fine_scan()
    law_fit(data)
    arch_only_and_rescue()
    portraits()

if __name__ == "__main__":
    main()
