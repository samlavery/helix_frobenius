#!/usr/bin/env python3
"""Adapter-system probe, phase 1: the one-sided Sym^r reflection substrate.

Constructor order (Sam, 2026-08-08): make it WORK first.
Phase 1 = build the one-sided theta T_r(x) = sum_n lam_r(n) K_r(n x) for
Delta (weight 12, level 1) with exact Sym^r coefficients assembled from the
Satake side (the compiled CG engine's numerical shadow), and the rank
Gamma-stack kernel K_r as a Meijer G-function; calibrate at r=1 (where the
reflection is Hecke's theorem) until D(x) = T(1/x) - eps * x * T(x) sits at
truncation level; then ascend r = 2, 3, ...

Analytic normalization throughout: FE at s <-> 1-s,
  GammaR(s) = pi^(-s/2) Gamma(s/2),  GammaC(s) = 2 (2pi)^(-s) Gamma(s).
Sym^r of weight k=12 discrete series: parameters (k-1)(r-2j)/2 = 11(r-2j)/2,
  L_inf = prod_{j: r-2j>0} GammaC(s + 11(r-2j)/2) * (r even: GammaR(s+delta_r)).
All GammaC converted to GammaR pairs via duplication:
  GammaC(s+mu) = GammaR(s+mu) GammaR(s+mu+1).
Kernel for an all-GammaR stack {lam_i}_{i=1..m}:
  K(y) = (1/2pi i) int prod GammaR(s+lam_i) y^{-s} ds
       = 2 * pi^{-L/2} * G^{m,0}_{0,m}( pi^{m/1?} ... ) -- constants fixed by
  the r=1 calibration gate below rather than trusted from convention.
Phase 2 (next): the self-compatible adapter dressing on this substrate.
"""

import mpmath as mp

mp.mp.dps = 30

K_WEIGHT = 12
KM1 = K_WEIGHT - 1  # 11

# ---------------------------------------------------------------- tau(n)
def tau_coeffs(N):
    """Ramanujan tau(1..N) exactly, via eta^24 (pentagonal numbers)."""
    # eta-series exponents: k(3k-1)/2 for k in Z, coefficient (-1)^k
    eta = [0] * (N + 1)
    k = 0
    while True:
        for kk in (k, -k) if k > 0 else (0,):
            e = kk * (3 * kk - 1) // 2
            if e <= N:
                eta[e] = (-1) ** kk
        if k * (3 * k - 1) // 2 > N and k * (3 * k + 1) // 2 > N:
            break
        k += 1
    # (eta)^24 by repeated multiplication: ((eta^2)^2)^2 * ... use exponent 24 = 8*3
    def mul(a, b):
        c = [0] * (N + 1)
        for i, ai in enumerate(a):
            if ai:
                for j in range(0, N + 1 - i):
                    bj = b[j]
                    if bj:
                        c[i + j] += ai * bj
        return c
    e2 = mul(eta, eta)
    e4 = mul(e2, e2)
    e8 = mul(e4, e4)
    e16 = mul(e8, e8)
    e24 = mul(e16, e8)
    # Delta = q * eta(q)^24  => tau(n) = e24[n-1]
    return [0] + [e24[n - 1] for n in range(1, N + 1)]

# ------------------------------------------------- Sym^r coefficients
def primes_upto(N):
    sieve = [True] * (N + 1)
    sieve[0:2] = [False, False]
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = [False] * len(sieve[i * i :: i])
    return [p for p in range(2, N + 1) if sieve[p]]

def sym_coeffs(r, N, tau):
    """lam_{Sym^r}(n) for n<=N, analytic normalization, via Satake alpha_p."""
    lam = [mp.mpf(0)] * (N + 1)
    lam[1] = mp.mpf(1)
    ps = primes_upto(N)
    # local coefficients at each prime power via the Sym^r local factor
    for p in ps:
        ap = mp.mpf(tau[p]) / mp.mpf(p) ** (mp.mpf(KM1) / 2)  # S_1(alpha_p)
        # alpha from ap = alpha + 1/alpha, |alpha| = 1 (Deligne)
        disc = mp.sqrt(mp.mpc(ap * ap - 4))
        alpha = (ap + disc) / 2
        # Sym^r local weights alpha^{r-2j}
        wts = [alpha ** (r - 2 * j) for j in range(r + 1)]
        # power series of prod 1/(1 - w p^{-s}) to needed length
        kmax = 0
        pk = p
        while pk <= N:
            kmax += 1
            pk *= p
        loc = [mp.mpc(1)] + [mp.mpc(0)] * kmax
        for w in wts:
            # multiply by 1/(1 - w X): cumulative geometric
            for k in range(1, kmax + 1):
                loc[k] = loc[k] + w * loc[k - 1]
        pk = 1
        for k in range(1, kmax + 1):
            pk *= p
            if pk <= N:
                lam[pk] = loc[k].real  # self-dual: real
    # multiplicative assembly
    for n in range(2, N + 1):
        if lam[n] == 0 and n > 1:
            # factor n = p^k * m with (p^k, m)=1
            m = n
            p = None
            for q in ps:
                if m % q == 0:
                    p = q
                    break
                if q * q > m:
                    break
            if p is None:
                continue
            pk = 1
            while m % p == 0:
                m //= p
                pk *= p
            if m > 1:
                lam[n] = lam[pk] * lam[m]
    return lam

# ------------------------------------------------- Gamma stack + kernel
def gammaR_params(r, delta=1):
    """All-GammaR parameter list for Sym^r Delta (analytic normalization).
    Even r carries the zero-channel GammaR(s+delta); delta is a calibration
    switch (Sym^2: delta=1, classical)."""
    lams = []
    for j in range(r + 1):
        m = r - 2 * j
        if m > 0:
            mu = mp.mpf(KM1 * m) / 2
            lams += [mu, mu + 1]  # GammaC -> GammaR pair
    if r % 2 == 0:
        lams.append(mp.mpf(delta))
    return lams

def kernel_factory(lams):
    """K(y) = (1/2pi i) int prod GammaR(s+lam_i) y^{-s} ds, computed as a
    Meijer G in the doubled variable.  prod pi^{-(s+lam)/2} Gamma((s+lam)/2):
    substitute s = 2u:  K(y) = 2 pi^{-L/2} (1/2pi i) int prod Gamma(u+lam/2)
    (pi^{m} y^2)^{-u} du  with m = len(lams), L = sum lams."""
    m = len(lams)
    L = sum(lams)
    half = [l / 2 for l in lams]
    c0 = 2 * mp.pi ** (-L / 2)
    cut = mp.mpf(10) ** (-(mp.mp.dps + 8))
    def K(y):
        z = mp.pi ** m * y ** 2
        # G^{m,0}_{0,m}(z) ~ exp(-m z^{1/m}) scale: skip provably negligible
        if m * z ** (mp.mpf(1) / m) > (mp.mp.dps + 12) * mp.log(10):
            return mp.mpf(0)
        try:
            return c0 * mp.meijerg([[], []], [half, []], z)
        except ValueError:
            return mp.mpf(0)
    return K

def theta(lam, K, x, N):
    return mp.fsum(lam[n] * K(n * x) for n in range(1, N + 1) if lam[n] != 0)

# ------------------------------------------------- the reflection gate
def defect(r, N, tau, xs, eps):
    lam = sym_coeffs(r, N, tau) if r > 1 else [mp.mpf(0)] + [
        mp.mpf(tau[n]) / mp.mpf(n) ** (mp.mpf(KM1) / 2) for n in range(1, N + 1)
    ]
    lams = gammaR_params(r)
    K = kernel_factory(lams)
    out = []
    for x in xs:
        T1 = theta(lam, K, 1 / x, N)
        T2 = theta(lam, K, x, N)
        out.append((x, T1 - eps * x * T2, T2))
    return out

def defect_d(r, N, tau, xs, eps, delta):
    lam = sym_coeffs(r, N, tau) if r > 1 else [mp.mpf(0)] + [
        mp.mpf(tau[n]) / mp.mpf(n) ** (mp.mpf(KM1) / 2) for n in range(1, N + 1)
    ]
    K = kernel_factory(gammaR_params(r, delta))
    out = []
    for x in xs:
        T1 = theta(lam, K, 1 / x, N)
        T2 = theta(lam, K, x, N)
        out.append((x, T1 - eps * x * T2, T2))
    return out

if __name__ == "__main__":
    import sys
    r = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    eps = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    delta = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    print(f"# Sym^{r} Delta reflection substrate, N={N}, eps={eps}, delta={delta}, dps={mp.mp.dps}")
    tau = tau_coeffs(N)
    xs = [mp.mpf('1.0'), mp.mpf('1.1'), mp.mpf('1.3'), mp.mpf('1.6')]
    for x, D, T in defect_d(r, N, tau, xs, eps, delta):
        rel = abs(D) / (abs(T) + mp.mpf('1e-40'))
        print(f"x={float(x):.2f}  D={mp.nstr(D, 6)}  T={mp.nstr(T, 6)}  rel={mp.nstr(rel, 4)}")
