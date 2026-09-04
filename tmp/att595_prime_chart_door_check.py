# att595: independent numeric check of the compiled chain
#   hermForm (zero sum) == Σ conj(r_j) r_k jetValueS (pf recursion, jets by numeric diff)
#                       == Σ conj(r_j) r_k jetValueP (pole jets + polygamma + ζ'/ζ jets)
import numpy as np, mpmath as mp, math, os, time
mp.mp.dps = 30
gam = np.load("tmp/zeros1500.npy")
def pf(d, j, k):
    """Lean's pf: returns (a, b) dicts index->coef."""
    if k == 0:
        return ({j: mp.mpf(1)}, {})
    if j == 0:
        return ({}, {k: mp.mpf(1)})
    a1, b1 = pf(d, j, k-1); a2, b2 = pf(d, j-1, k)
    a = {}; b = {}
    for key in set(a1) | set(a2): a[key] = (a1.get(key, 0) + a2.get(key, 0)) / d
    for key in set(b1) | set(b2): b[key] = (b1.get(key, 0) + b2.get(key, 0)) / d
    return a, b
def logxi(s): return mp.log(mp.zeta(s)) + mp.log(mp.gamma(s/2)) - s/2*mp.log(mp.pi) + mp.log(s*(s-1)/2)
def xi_jet_numeric(s, m):   # (ξ'/ξ)^{(m)}(s)
    return mp.diff(logxi, s, m+1)
def zz_jet_numeric(s, m):   # (ζ'/ζ)^{(m)}(s)
    return mp.diff(lambda z: mp.zeta(z, derivative=1)/mp.zeta(z), s, m)
def primeJet(s, m):         # Lean's primeJet: (-1)^m m!(s^{-m-1}+(s-1)^{-m-1}) + (½ψ(·/2))^{(m)}(s) − (−1)^m LSeries(log^m Λ)(s)
    pole = (-1)**m * mp.factorial(m) * (s**(-1-m) + (s-1)**(-1-m))
    gam_jet = mp.polygamma(m, s/2) / 2**(m+1)
    lser = -(-1)**m * zz_jet_numeric(s, m)          # Σ Λ(n) log^m n n^{-s} = −(−1)^m (ζ'/ζ)^{(m)}
    return pole + gam_jet - (-1)**m * lser
def primeLogDeriv(s):
    return 1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2 + zz_jet_numeric(s, 0)
def jetValue_generic(s, d, M, j, k, J0re, J):   # J0re = Re(ξ'/ξ)(s); J[m] = m-th jet
    a, b = pf(d, j, k)
    v = a.get(1, 0) * 2 * J0re
    for i in range(M-1):
        v += a.get(i+2, 0) * (J[i+1] / ((-1)**(i+1) * mp.factorial(i+1)))
    for l in range(M-1):
        v += b.get(l+2, 0) * ((-1)**(l+1) * mp.conj(J[l+1]) / mp.factorial(l+1))
    return v
def hermForm_zero_sum(s, c, r):
    N = len(r) - 1
    tot = mp.mpc(0)
    for t in gam:
        for rho in (mp.mpc(0.5, t), mp.mpc(0.5, -t)):
            x = 1/(s - rho); xp = 1/(rho - c)
            Rx = sum(r[j] * mp.conj(x)**j for j in range(N+1))       # R(conj x)
            Rxp = sum(r[k] * xp**k for k in range(N+1))
            tot += mp.conj(Rx) * Rxp
    return tot
rng = np.random.default_rng(595)
for (g0, s0) in [(50.0, 1.2), (200.0, 1.45)]:
    s = mp.mpc(s0, g0); c = mp.mpc(1 - s0, g0); d = s - c
    N = 3
    r = [mp.mpc(0)] + [mp.mpc(*rng.normal(size=2)) for _ in range(N)]
    M = 2*N + 2
    J = {m: xi_jet_numeric(s, m) for m in range(0, M)}
    J0re = mp.re(J[0])
    Jp = {m: primeJet(s, m) for m in range(1, M)}
    JP0re = mp.re(primeLogDeriv(s))
    Hz = hermForm_zero_sum(s, c, r)
    HS = sum(mp.conj(r[j]) * r[k] * jetValue_generic(s, d, M, j, k, J0re, J) for j in range(N+1) for k in range(N+1))
    HP = sum(mp.conj(r[j]) * r[k] * jetValue_generic(s, d, M, j, k, JP0re, Jp) for j in range(N+1) for k in range(N+1))
    print("s = %s  d = %s  N = %d" % (mp.nstr(s, 6), mp.nstr(d, 4), N))
    print("  zero-sum hermForm (1500 zeros) = %s" % mp.nstr(Hz, 10))
    print("  jets (numeric diff, pf recursion) = %s   rel diff vs zero sum = %.2e" % (mp.nstr(HS, 10), float(abs(HS-Hz)/abs(Hz))))
    print("  prime chart (pole+polygamma+ζ'/ζ) = %s   rel diff vs jets = %.2e" % (mp.nstr(HP, 10), float(abs(HP-HS)/abs(HS))))
    print("  Re hermForm = %s  (door: ≥ 0)" % mp.nstr(mp.re(HP), 8))
    # jet formula check per m
    for m in range(1, 4):
        print("    m=%d: (ξ'/ξ)^(m) numeric %s  vs primeJet %s  rel %.1e" % (m, mp.nstr(J[m], 8), mp.nstr(Jp[m], 8), float(abs(J[m]-Jp[m])/abs(J[m]))))
