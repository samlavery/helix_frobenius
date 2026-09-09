# att637 — the paired-prime coefficients at s0 = −1 + 20i: closed arithmetic form, the sequence three
# ways, its growth to degree 2000, and the cancellation an arithmetic bound has to produce.
#
# Objects (PairedSides.lean, DraftBPrimeStages.lean):
#   pairedPrime s = 1/s + Σ_n Λ(n) n^{s−1};   μ_{k+1} := toeplitzCoeff (−3) (jets pairedPrime s0) (k+1)
#   μ_{k+1} = ω_0 w_0^{k+1} + Σ_n Λ(n) n^{−2+20i} q_k(log n),   q_k(ℓ) = Σ_i C(k,i)(−3)^{k−i}(−1)^i (−1)^{k+1−i} ℓ^{k+1−i}/(k+1−i)!
#   w_a = (a − c)/(s0 − a), ω_a = 1/((s0 − a)(a − c)), c = 1 − conj(s0) = 2 + 20i, d = 2Re s0 − 1 = −3.
# Pencil (this attempt): q_k(ℓ) = (−1)^{k+1} (ℓ/(k+1)) L_k^{(1)}(3ℓ); generating function
#   Σ_k q_k(u) t^k = (e^{3tu/(1+t)} − 1)/(−3t);  Σ_k μ_{k+1} t^k = [pairedPrime(s_t) − pairedPrime(s0)]/(t d),
#   s_t = (s0 + t c)/(1 + t)  (the sweep, 627).
import sys, time
import numpy as np
from fractions import Fraction
from math import comb, factorial
from mpmath import mp, mpc, mpf, zeta, log, pi, exp, conj, fabs, sqrt, quad, inf, binomial, laguerre, gammainc

mp.dps = 50
s0 = mpc(-1, 20); c = 1 - conj(s0); d = 2 * s0.real - 1
sp = 1 - s0                      # s' = 2 − 20i, where the Dirichlet series lives
def w(a): return (a - c) / (s0 - a)
def om(a): return 1 / ((s0 - a) * (a - c))
out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)

P("att637  anchor s0 = %s, c = %s, d = %s, s' = %s" % (s0, c, d, sp))
P("end atom: |w_0| = %.10f, |ω_0| = %.6e, e-fold k = %d" % (fabs(w(0)), fabs(om(0)), round(1 / float(log(fabs(w(0)))))))

# ---------- P1: closed form of the prime weights, exact rational check ----------
def q_binom(k, l):   # Draft B's primeCoeffSymbol (−3) k ℓ, exact in Fraction
    return sum(Fraction(comb(k, i) * (-3) ** (k - i) * (-1) ** i * (-1) ** (k + 1 - i)) * l ** (k + 1 - i) / factorial(k + 1 - i)
               for i in range(k + 1))
def lag1(k, x):      # generalized Laguerre L_k^{(1)}(x), exact
    return sum(Fraction((-1) ** j * comb(k + 1, k - j)) * x ** j / factorial(j) for j in range(k + 1))
ok = True
for k in range(0, 31):
    for l in (Fraction(1), Fraction(2), Fraction(7, 3), Fraction(11, 5)):
        lhs = q_binom(k, l); rhs = Fraction((-1) ** (k + 1)) * l / (k + 1) * lag1(k, 3 * l)
        if lhs != rhs: ok = False; P("  P1 MISMATCH k=%d l=%s" % (k, l))
P("P1  q_k(ℓ) = (−1)^{k+1} (ℓ/(k+1)) L_k^{(1)}(3ℓ)  exact for k ≤ 30, four rational ℓ:", "PASS" if ok else "FAIL")

# ---------- P2a: the sequence from the Taylor coefficients of −ζ′/ζ at s' (Cauchy/FFT) ----------
K = 60; Nc = 1024; rc = mpf("1.2")   # nearest singularity of ζ′/ζ to s': zero 1/2+21.02i at distance 1.81
t0 = time.time()
g = [-zeta(sp + rc * exp(2j * pi * j / Nc), derivative=1) / zeta(sp + rc * exp(2j * pi * j / Nc)) for j in range(Nc)]
a = []
for m in range(K + 2):
    a.append(sum(g[j] * exp(-2j * pi * j * m / Nc) for j in range(Nc)) / Nc / rc ** m)
P("P2a Taylor coefficients of −ζ′/ζ at s' by Cauchy/FFT: N=%d, r=%s, dps=%d  (%.0f s)" % (Nc, rc, mp.dps, time.time() - t0))
P("     a_0 = %s  (= −ζ′/ζ(2−20i))" % a[0])
def jets_pp(m):      # jets pairedPrime s0 (m+1) = 1/s0^{m+1} + a_m   (∂^m_s g(1−s) = (−1)^m g^{(m)}, jets carry (−1)^m/m!)
    return 1 / s0 ** (m + 1) + a[m]
def toeplitz(J, n):  # toeplitzCoeff d J (n+1) with J(m) = jets(m)
    return sum(binomial(n, i) * d ** (n - i) * (-1) ** i * J(n + 2 - i - 1) for i in range(n + 1))
mu_a = [toeplitz(jets_pp, k) for k in range(K + 1)]
mu0_a = 2 * jets_pp(0).real / d
P("     μ_0 = %.12f ; |μ_{k+1}| for k=0..9: %s" % (mu0_a, ["%.6f" % fabs(x) for x in mu_a[:10]]))

# ---------- P2b: the sequence from the atoms: zeros (+ smooth tail) and the Γ ticks with residue +1 ----------
gam = np.load("tmp/att015_zeros_to_30000.npy")
assert abs(gam[0] - 14.134725141734693) < 1e-8, "zero table sanity"
T = float(gam[-1]); M = len(gam)
def zero_atoms(kk, digits=20):
    with mp.workdps(digits):
        tot = mpc(0)
        for gv in gam:
            r1 = mpc(mpf(1) / 2, gv); r2 = conj(r1)
            tot += om(r1) * w(r1) ** kk + om(r2) * w(r2) ** kk
        # smooth tail: density (1/2π) log(γ/2π) above T
        f = lambda gv: (log(gv / (2 * pi)) / (2 * pi)) * (om(mpc(mpf(1) / 2, gv)) * w(mpc(mpf(1) / 2, gv)) ** kk
                                                          + om(mpc(mpf(1) / 2, -gv)) * w(mpc(mpf(1) / 2, -gv)) ** kk)
        tail = quad(f, [T, 2 * T, 10 * T, inf])
        return tot, tail
def tick_atoms(kk, digits=20):
    with mp.workdps(digits):
        tot = mpc(0); n = 0
        while True:
            a_ = 3 + 2 * n; t = om(a_) * w(a_) ** kk; tot += t
            if fabs(t) < mpf(10) ** (-24) and n > 50: break
            n += 1
            if n > 400000: break
        return tot
P("P2b atoms: %d zeros to height %.0f (+ smooth tail) and Γ ticks 3,5,7,… (residue +1)" % (M, T))
P("      k   |μ_{k+1}| Cauchy      |μ_{k+1}| atoms      |diff|       zero-tail   ticks part")
for k in (0, 1, 2, 5, 10, 20, 40, 60):
    za, tl = zero_atoms(k + 1); tk = tick_atoms(k + 1)
    mb = za + tl + tk
    P("     %2d   %.10f   %.10f   %.2e   %.2e   %.6f" % (k, fabs(mu_a[k]), fabs(mb), fabs(mu_a[k] - mb), fabs(tl), fabs(tk)))
sum_abs_om = sum(1 / ((mpf(1.5)) ** 2 + (mpf(gv) - 20) ** 2) + 1 / ((mpf(1.5)) ** 2 + (mpf(gv) + 20) ** 2) for gv in gam)
P("     Σ_ρ |ω_ρ| over the table = %.6f  (the RH bound on |Σ_ρ ω_ρ w_ρ^k|; tail ≈ log(T/2π)/(2πT) = %.1e)" % (sum_abs_om, float(log(T / (2 * pi)) / (2 * pi * T))))

# ---------- P2c: the direct prime sum, k ≤ 4, with the PNT main-term tail ----------
X = 10 ** 7
t0 = time.time()
sieve = np.ones(X + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(X ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
primes = np.nonzero(sieve)[0]
lam = np.zeros(X + 1); lam[primes] = np.log(primes)
for p in primes[primes <= int(X ** 0.5)]:
    q = p * p
    while q <= X: lam[q] = np.log(p); q *= p
n = np.arange(X + 1, dtype=np.float64); ln = np.zeros(X + 1); ln[1:] = np.log(n[1:])
from scipy.special import eval_genlaguerre
def q_np(k, l): return (-1) ** (k + 1) * l / (k + 1) * eval_genlaguerre(k, 1, 3 * l)
P("P2c sieve Λ to X = %d (%.0f s); direct sum Σ_{n≤X} Λ(n) n^{−2+20i} q_k(log n) + PNT tail ∫_{log X}^∞ e^{−(1−20i)u} q_k(u) du + ω_0 w_0^{k+1}"
  % (X, time.time() - t0))
phase = np.exp(20j * ln[2:]); wt = lam[2:] / n[2:] ** 2 * phase
def pnt_tail(k, X):
    with mp.workdps(30):
        return quad(lambda u: exp(-(1 - 20j) * u) * (-1) ** (k + 1) * u / (k + 1) * laguerre(k, 1, 3 * u), [log(X), inf])
P("      k   direct+tail |μ|      Cauchy |μ|       |diff|")
for k in (0, 1, 2, 3, 4):
    S = complex(np.sum(wt * q_np(k, ln[2:])))
    val = om(0) * w(0) ** (k + 1) + mpc(S) + pnt_tail(k, X)
    P("     %2d   %.10f   %.10f   %.2e" % (k, fabs(val), fabs(mu_a[k]), fabs(val - mu_a[k])))

# ---------- P3: growth to degree 2000 through the generating function on |t| = r ----------
r = mpf("0.995"); Ng = 8192
t0 = time.time()
with mp.workdps(20):
    pp0 = 1 / s0 - zeta(sp, derivative=1) / zeta(sp)
    Fv = np.zeros(Ng, dtype=np.complex128)
    for j in range(Ng):
        t = r * exp(2j * pi * j / Ng)
        st = (s0 + t * c) / (1 + t); u = 1 - st
        ppt = 1 / st - zeta(u, derivative=1) / zeta(u)
        Fv[j] = complex((ppt - pp0) / (t * d))
coef = np.fft.fft(Fv) / Ng          # coef[k] ≈ μ_{k+1} r^k
ks = np.arange(Ng); mu_g = coef * (float(r) ** (-ks.astype(np.float64)))
P("P3  generating function on |t| = %s, %d points, dps 20 (%.0f s): circle of pseudo-hyperbolic radius r reaches heights 20 ± %.0f, Re(1−s_t) ≥ 1/2 + %.2e"
  % (r, Ng, time.time() - t0, float(3 * r / (1 - r ** 2)), float(3 * (1 - r) / (2 * (1 + r)))))
P("     aliasing r^N = %.1e; amplification r^{−k} at k=2000: %.1e" % (float(r) ** Ng, float(r) ** (-2000)))
P("      k   |μ_{k+1}| gen.fn.    |μ_{k+1}| Cauchy/atoms   |diff|")
for k in (0, 1, 5, 20, 60):
    P("     %4d  %.10f   %.10f   %.2e" % (k, abs(mu_g[k]), float(fabs(mu_a[k])), abs(mu_g[k] - complex(mu_a[k]))))
for k in (200, 500, 1000, 2000):
    za, tl = zero_atoms(k + 1, digits=25); tk = tick_atoms(k + 1, digits=25); mb = za + tl + tk
    P("     %4d  %.10f   %.10f   %.2e   (atoms)" % (k, abs(mu_g[k]), float(fabs(mb)), abs(mu_g[k] - complex(mb))))
P("     growth: max |μ_{k+1}| on k-ranges vs the end atom alone |ω_0||w_0|^{k+1}")
for lo, hi in ((0, 100), (100, 500), (500, 1000), (1000, 2000), (2000, 3000)):
    seg = np.abs(mu_g[lo:hi])
    P("       k ∈ [%4d,%4d): max = %.6f  mean = %.6f   end atom at k=%d: %.4f" % (lo, hi, seg.max(), seg.mean(), hi - 1, float(fabs(om(0)) * fabs(w(0)) ** hi)))

# ---------- P4: the cancellation an absolute (worst-case) arithmetic bound has to beat ----------
P("P4  A_k := Σ_n Λ(n) n^{−2} |q_k(log n)| (sieve to X, PNT tail) and its PNT-density proxy Ā_k = ∫_0^∞ e^{−u}|q_k(u)| du, against |μ_{k+1}|")
P("      k      A_k (sieve+tail)     Ā_k (proxy)     |μ_{k+1}|      A_k/|μ|       e^{2k/3}")
def abs_proxy(k):
    with mp.workdps(20):
        f = lambda u: exp(-u) * fabs(u / (k + 1) * laguerre(k, 1, 3 * u))
        return quad(f, np.linspace(0, 4 * k / 3 + 6, 4 * k + 8).tolist() + [inf])
for k in (0, 1, 2, 4, 6, 8):
    A = float(np.sum(lam[2:] / n[2:] ** 2 * np.abs(q_np(k, ln[2:]))))
    with mp.workdps(20):
        A += float(quad(lambda u: exp(-u) * fabs(u / (k + 1) * laguerre(k, 1, 3 * u)), [log(X), inf]))
    Ab = float(abs_proxy(k))
    P("     %2d   %.6e   %.6e   %.6f   %.3e   %.3e" % (k, A, Ab, abs(mu_g[k]), A / abs(mu_g[k]), np.exp(2 * k / 3)))
for k in (12, 20, 30, 45, 60):
    Ab = float(abs_proxy(k))
    P("     %2d   %-16s   %.6e   %.6f   %.3e   %.3e" % (k, "—", Ab, abs(mu_g[k]), Ab / abs(mu_g[k]), np.exp(2 * k / 3)))

# ---------- P5: what exponent in |ψ(x) − x| ≤ x^θ the bound needs — the planted remainder ----------
P("P5  a remainder R(u) = −2Re(e^{ρu}/ρ) with ρ = β + iγ satisfies |R(u)| ≤ 2e^{βu}/|ρ| and has coefficients ω_ρ w_ρ^{k+1} + conj partner:")
for beta, gv in ((0.5, 50.0), (0.51, 50.0), (0.6, 50.0), (0.6, 5000.0), (0.75, 1000.0)):
    rho = mpc(beta, gv)
    P("     β = %.2f, γ = %6.0f:  |w_ρ| = %.8f  → growth base %.8f, e-fold at k ≈ %s" %
      (beta, gv, fabs(w(rho)), fabs(w(rho)), "∞" if beta == 0.5 else "%d" % round(1 / float(log(fabs(w(rho)))))))

# ---------- P6: how far in n the arithmetic sum must go — partial sums of the k-th coefficient ----------
P("P6  partial sums S_k(X) = ω_0 w_0^{k+1} + Σ_{n≤X} Λ(n) n^{−2+20i} q_k(log n): raw, and PNT-corrected (+ main-term tail); target μ_{k+1}")
for k in (2, 5, 8):
    P("     k = %d, |μ| = %.8f, Laguerre bulk ends at log n ≈ 4k/3 = %.1f (n ≈ %.1e)" % (k, abs(mu_g[k]), 4 * k / 3, np.exp(4 * k / 3)))
    qk = q_np(k, ln[2:])
    for Xc in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7):
        S = complex(np.sum((lam[2:] / n[2:] ** 2 * phase * qk)[: Xc - 1]))
        raw = om(0) * w(0) ** (k + 1) + mpc(S)
        corr = raw + pnt_tail(k, Xc)
        P("       X = %.0e   raw |S−μ| = %.3e   PNT-corrected |S−μ| = %.3e" % (Xc, fabs(raw - complex(mu_g[k])), fabs(corr - complex(mu_g[k]))))

open("tmp/att637_results.txt", "w").write("\n".join(out) + "\n")
