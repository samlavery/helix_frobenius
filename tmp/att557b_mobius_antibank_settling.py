#!/usr/bin/env python3
"""
att557b — item 2, the purest multiplicative form: the ANTI-BANK.  The fiber's Dirichlet inverse
(a_n = 1 ⇒ a^{−1} = μ, compiled multiplicative: dirichletInverse_isMultiplicative3D) has NO pole, so
no END term, and no positivity: Σ_{n≤x} μ(n) n^{−s} settles to 1/ζ(s) right of balance at rate
x^{½−σ} iff RH (Littlewood).  Control: DH's Dirichlet inverse b = a^{−1} (exists, a_1 = 1, NOT
multiplicative): Σ b_n n^{−s} settles to 1/DH(s) iff no DH zero right of σ.
PRE-REGISTERED slopes (x = 10³…10⁶): ζ/μ: ½ − σ (±0.15) at t = 85.7 and 30;  DH: β − σ = 0.8085 − σ
at t = 85.7 (±0.15); at t = 30 drifting from ½ − σ upward.
"""
import math, numpy as np, mpmath as mp
mp.mp.dps = 20
X = 1_000_000
kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1)
a_per = np.array([0.0, 1.0, kappa, -kappa, -1.0])
n = np.arange(0, X + 1, dtype=float); logn = np.zeros(X + 1); logn[1:] = np.log(n[1:])
# Dirichlet inverse of a periodic a with a_1 = 1:  b[1] = 1, b[n] = −Σ_{m≥2, mk=n} a[m] b[k]
b = np.zeros(X + 1); acc = np.zeros(X + 1); b[1] = 1.0
for k in range(1, X + 1):
    if k > 1: b[k] = -acc[k]
    if b[k] != 0.0 and 2*k <= X:
        ms = np.arange(2, X//k + 1)
        acc[2*k::k][:len(ms)] += a_per[ms % 5]*b[k]
# Möbius by sieve
mu = np.ones(X + 1); sieve = np.ones(X + 1, dtype=bool); sieve[:2] = False
for p in range(2, int(X**0.5) + 1):
    if sieve[p]: sieve[p*p::p] = False
for p in np.nonzero(sieve)[0]:
    mu[p::p] *= -1; mu[p*p::p*p] = 0
mu[0] = 0
chi = [0, 1, 1j, -1j, -1]; chib = [0, 1, -1j, 1j, -1]
DH = lambda s: (1 - 1j*kappa)/2*mp.dirichlet(s, chi) + (1 + 1j*kappa)/2*mp.dirichlet(s, chib)
s3 = mp.mpc(3, 0.7)
print("sanity s=3+0.7i:  Σ μ n^{-s} = %s  1/ζ = %s |  Σ b n^{-s} = %s  1/DH = %s"
      % (mp.nstr(complex(np.sum(mu[1:]*np.exp(-complex(s3)*logn[1:]))), 9), mp.nstr(1/mp.zeta(s3), 9),
         mp.nstr(complex(np.sum(b[1:]*np.exp(-complex(s3)*logn[1:]))), 9), mp.nstr(1/DH(s3), 9)))
xs = [1_000, 3_000, 10_000, 30_000, 100_000, 300_000, 1_000_000]
def slope(coef, s, target):
    cum = np.cumsum(coef[1:]*np.exp(-s*logn[1:])); errs = [abs(cum[x - 1] - target) for x in xs]
    return np.polyfit(np.log(xs), np.log(errs), 1)[0], errs
print("\nANTI-BANK settling: slope of log|Σ_{n≤x} a⁻¹(n) n^{-s} − 1/F(s)| vs log x")
print(" object    t      σ     slope   predicted      |err| 10^3 / 10^6")
for t in (85.699348, 30.0):
    for sig in (0.6, 0.75, 0.9):
        s = complex(sig, t)
        sz, ez = slope(mu, s, complex(1/mp.zeta(mp.mpc(sig, t))))
        sd, ed = slope(b, s, complex(1/DH(mp.mpc(sig, t))))
        print(" ζ / μ   %6.2f  %.2f   %+.3f   %+.3f (½−σ)   %.2e / %.2e" % (t, sig, sz, 0.5 - sig, ez[0], ez[-1]))
        print(" DH / b  %6.2f  %.2f   %+.3f   %+.3f (β−σ)   %.2e / %.2e" % (t, sig, sd, 0.808517 - sig, ed[0], ed[-1]))
