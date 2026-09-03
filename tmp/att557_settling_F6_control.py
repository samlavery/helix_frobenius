#!/usr/bin/env python3
"""
att557 — item 2, part (ii): the settling register's F6 control.  The END-corrected clock resultant
settles right of balance at rate x^{½−σ} for ζ (554f).  Same instrument on Davenport–Heilbronn:
  DH(s) = Σ a_n n^{−s},  a = (1, κ, −κ, −1, 0) periodic mod 5,  κ = (√(10−2√5) − 2)/(√5 − 1)
  (= (1−iκ)/2·L(s,χ) + (1+iκ)/2·L(s,χ̄), χ mod 5 with χ(2) = i); FE with the same Γ-factor as
  L(s,χ); NO Euler product; NO pole (so no END term); off-line zeros, e.g. 0.808517 + 85.699348 i.
  Log-derivative coefficients c_n by Dirichlet division:  a_n log n = Σ_{mk=n} a_m c_k.
  C_x^{DH}(s) = Σ_{n≤x} c_n n^{−s}  should settle to −DH′/DH(s) iff no zero to the right of σ.
PRE-REGISTERED (slopes of log|error| vs log x over x = 10³…10⁶):
  ζ at t = 85.7:  ½ − σ = −0.10 / −0.25 / −0.40 at σ = 0.6 / 0.75 / 0.9  (±0.15)
  DH at t = 85.7: β − σ with β = 0.8085:  +0.21 / +0.06 / −0.09  (±0.15) — the off-line zero READ AS A RATE
  DH at t = 30 (no nearby off-line zero): the far off-line zero's term grows like x^{β−σ}/|ρ−s| against the
      on-line terms' decay, so the slope drifts upward from ½ − σ toward β − σ across the range; report.
DECISION: if DH's slopes at t = 85.7 come out ≈ ½ − σ, the register is F6-blind and item 2 is not
the place; if they come out ≈ β − σ, the register reads the arithmetic and item 2 is the place.
"""
import math, numpy as np, mpmath as mp
mp.mp.dps = 20
X = 1_000_000
kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1)
a_per = np.array([0.0, 1.0, kappa, -kappa, -1.0])          # index n mod 5
n = np.arange(0, X + 1, dtype=float)
a = a_per[(np.arange(0, X + 1)) % 5]; a[0] = 0.0
logn = np.zeros(X + 1); logn[1:] = np.log(n[1:])
# Dirichlet division: c[n] = a[n] log n − Σ_{m≥2, mk=n} a[m] c[k]; forward sieve keeps order correct
c = np.zeros(X + 1); acc = np.zeros(X + 1)
for k in range(1, X + 1):
    c[k] = a[k]*logn[k] - acc[k]
    if c[k] != 0.0 and 2*k <= X:
        ms = np.arange(2, X//k + 1)
        acc[2*k::k][:len(ms)] += a_per[ms % 5]*c[k]
# Λ for ζ
lam = np.zeros(X + 1); sieve = np.ones(X + 1, dtype=bool); sieve[:2] = False
for p in range(2, int(X**0.5) + 1):
    if sieve[p]: sieve[p*p::p] = False
for p in np.nonzero(sieve)[0]:
    q = p
    while q <= X: lam[q] = math.log(p); q *= p
# sanity: c should equal Λ-like structure? (no: DH is not multiplicative) — check c against a direct series at s=3
chi = [0, 1, 1j, -1j, -1]; chib = [0, 1, -1j, 1j, -1]
def DH(s):  return (1 - 1j*kappa)/2*mp.dirichlet(s, chi) + (1 + 1j*kappa)/2*mp.dirichlet(s, chib)
def target_DH(s): return -mp.diff(DH, s)/DH(s)
def target_zeta(s): return -mp.zeta(s, derivative=1)/mp.zeta(s)
s3 = mp.mpc(3, 0.7)
print("sanity at s=3+0.7i: Σ c_n n^{-s} (n≤10^6) = %s   −DH′/DH = %s" % (mp.nstr(complex(np.sum(c[1:]*np.exp(-complex(s3)*logn[1:]))), 10), mp.nstr(target_DH(s3), 10)))
xs = [1_000, 3_000, 10_000, 30_000, 100_000, 300_000, 1_000_000]
def slopes(coef, s, target, end_term):
    cum = np.cumsum(coef[1:]*np.exp(-s*logn[1:]))
    errs = []
    for x in xs:
        val = cum[x - 1] - (x**(1 - s)/(1 - s) if end_term else 0.0)
        errs.append(abs(val - target))
    return np.polyfit(np.log(xs), np.log(errs), 1)[0], errs
print("\nsettling slopes of log|C_x − target| vs log x, x = 10^3…10^6")
print(" object   t      σ     slope    predicted        |err| at 10^3 / 10^6")
for t in (85.699348, 30.0):
    for sig in (0.6, 0.75, 0.9):
        s = complex(sig, t)
        sz, ez = slopes(lam, s, complex(target_zeta(mp.mpc(sig, t))), True)
        sd, ed = slopes(c, s, complex(target_DH(mp.mpc(sig, t))), False)
        print(" ζ      %6.2f  %.2f   %+.3f   %+.3f (½−σ)      %.2e / %.2e" % (t, sig, sz, 0.5 - sig, ez[0], ez[-1]))
        print(" DH     %6.2f  %.2f   %+.3f   %+.3f (β−σ)      %.2e / %.2e" % (t, sig, sd, 0.808517 - sig, ed[0], ed[-1]))
