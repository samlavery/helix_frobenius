"""Hands-on Sym^5 FE test (degree 6): does the 3D helix-conjugation FE (ray pinning of the
completed Lambda) survive to Sym^5 with the 3-Gamma_C (degree-6 MeijerG) completion?

Method mirrors bsd_weld.py but at degree 6:
  - a_p for E11 by point counting (oracle-free); normalized theta_p, a_p = 2 sqrt(p) cos theta_p.
  - Sym^5 Dirichlet coeffs b_n from Satake {e^{i(5-2j)theta}}_{j=0..5} via Newton's identities
    (power sums p_m = 2(cos5m th + cos3m th + cos m th) -> complete homogeneous h_k = c_{p^k}).
  - completed Lambda(1/2+it) = pref(t) * sum_n b_n n^{-1/2} e^{-it ln n}  (tapered fiber),
    pref(t) = e^{i t L} * Gamma(1+it) Gamma(2+it) Gamma(3+it)   [3 Gamma_C = degree-6 completion].
  - FE test = RAY PINNING: choose the single real conductor-scale L that makes arg Lambda(1/2+it)
    FLAT in t. If a clean flat ray exists, the FE holds and eps = ray (0/pi->+1, pi/2->-1) EMERGES.
    If no L flattens it, the degree-6 FE does NOT close by this mechanism -> honest null.
This is the 3D-conjugation FE at degree 6, NOT a 2D lattice theta.
"""
import math
import numpy as np
from scipy.special import loggamma

NB = 60000
# E11 = 11a1 : y^2 + y = x^3 - x^2 - 10x - 20  (conductor 11, multiplicative at 11)
A2, A4, A6 = -1, -10, -20
Q_BAD = 11


def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]


def ap_curve(p):
    if p == 2:
        cnt = sum(1 for x in range(2) for y in range(2)
                  if (y * y + y - (x**3 + A2*x*x + A4*x + A6)) % 2 == 0)
        return 2 + 1 - (cnt + 1)
    x = np.arange(p, dtype=np.int64)
    z = (4*(x**3 % p) + 4*A2 % p*(x*x % p) + 4*A4 % p*x + (4*A6 + 1)) % p
    isq = np.zeros(p, dtype=bool); isq[(x*x) % p] = True
    chi = np.where(z == 0, 0, np.where(isq[z], 1, -1))
    return int(-chi.sum())


def sym_local_coeffs(theta, kmax, M):
    """c_{p^k}=h_k of the (M+1) Sym^M Satake e^{i(M-2j)theta}, via Newton's identities (odd M)."""
    exps = [M - 2*j for j in range((M+1)//2)]  # positive Satake exponents (odd M): M,M-2,...,1
    pm = [2.0*sum(math.cos(e*m*theta) for e in exps) for m in range(1, kmax+1)]
    h = [1.0]
    for k in range(1, kmax+1):
        acc = sum(pm[m-1]*h[k-m] for m in range(1, k+1))
        h.append(acc / k)
    return h


def build_bn(nmax):
    primes = sieve_primes(nmax)
    # theta_p for good primes; bad prime 11 handled as Steinberg (single normalized Satake)
    theta = {}
    a11 = ap_curve(Q_BAD)  # +-1 for multiplicative
    for p in primes:
        p = int(p)
        if p == Q_BAD:
            continue
        c = ap_curve(p) / (2.0*math.sqrt(p))
        c = max(-1.0, min(1.0, c))
        theta[p] = math.acos(c)
    # local coefficient tables c_{p^k}
    spf = np.zeros(nmax+1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    loc = {}
    for p in primes:
        p = int(p)
        kmax = int(math.log(nmax)/math.log(p)) + 1
        if p == Q_BAD:
            # Steinberg Sym^5: single Satake alpha = a11/sqrt(11), local factor (1-alpha^5 p^-s)^-1
            al = a11/math.sqrt(Q_BAD)
            loc[p] = [al**(5*k) for k in range(kmax+1)]
        else:
            loc[p] = sym5_local_coeffs(theta[p], kmax)
    b = np.zeros(nmax+1)
    b[1] = 1.0
    for n in range(2, nmax+1):
        p = int(spf[n]); m, k = n, 0
        while m % p == 0:
            m //= p; k += 1
        pk = n // m
        b[n] = (b[m]*b[pk]) if m > 1 else loc[p][k]
    return b


def completed_ray(b, ts, L):
    n = np.arange(1, len(b), dtype=np.float64)
    u = n/(len(b)-1)
    w = np.where(u < 1.0, np.exp(1.0 - 1.0/np.clip(1.0 - u*u, 1e-300, None)), 0.0)
    amp = b[1:]*w*n**(-0.5)
    ln = np.log(n)
    F = np.array([np.sum(amp*np.exp(-1j*t*ln)) for t in ts])
    pref = np.exp(1j*ts*L + loggamma(1+1j*ts) + loggamma(2+1j*ts) + loggamma(3+1j*ts))
    return pref*F


def main():
    print("building Sym^5(E11) degree-6 coefficients, NB =", NB)
    b = build_bn(NB)
    print("  |b_n| growth check: b_2=%.4f b_3=%.4f b_5=%.4f (bounded by binom(k+5,5))" % (b[2], b[3], b[5]))
    ts = np.linspace(-3.0, 3.0, 61)
    # scan the conductor log-scale L to flatten the ray
    best = None
    for L in np.linspace(-2.0, 14.0, 321):
        Lam = completed_ray(b, ts, L)
        ph = np.angle(Lam)
        # unwrap-free flatness: measure spread of ph mod pi (the FE ray is defined mod pi)
        phm = np.mod(ph, math.pi)
        # circular spread on the mod-pi circle
        z = np.exp(2j*phm)  # period pi -> full circle
        spread = float(np.abs(np.std(np.angle(z*np.conj(np.mean(z))))))
        if best is None or spread < best[1]:
            best = (L, spread, phm.copy())
    L, spread, phm = best
    ray = float(np.median(phm))
    eps = -1 if abs(ray - math.pi/2) < math.pi/4 else +1
    print("  best conductor log-scale L = %.4f  (=> effective sqrt-cond*(2pi)-combo)" % L)
    print("  ray pinning: median ray = %.4f pi, spread(mod pi) = %.3e" % (ray/math.pi, spread))
    print("  => eps (emergent from ray) = %+d" % eps)
    print("  reference: for comparison, degree-2 pins to spread ~4e-7 (bsd_weld). Degree-6 spread here:", "%.2e" % spread)
    # verdict
    if spread < 1e-2:
        print("  VERDICT: a clean flat ray EXISTS at degree 6 -> Sym^5 FE closes by ray-pinning (eps emergent).")
    elif spread < 1e-1:
        print("  VERDICT: partial pinning (spread %.2e) -> FE approximately closes; check completion/conductor." % spread)
    else:
        print("  VERDICT: NO flat ray found (spread %.2e) -> degree-6 FE does NOT close by this mechanism as-built." % spread)


if __name__ == "__main__":
    main()
