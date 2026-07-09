"""Origin positivity (Li's criterion) with source attribution (2026-07-02).
lambda_n = n * sum_j C(n-1, n-j) c_j, where c_j are Taylor coefficients of
log xi(1+u) at u=0. Decomposition: xi = [gauge part (1/2)s(s-1)pi^(-s/2)Gamma(s/2)]
* [prime part (s-1)zeta(s) / (s-1) ... folded as regularized zeta].
Anchor: lambda_1 = 1 + gamma/2 - log(4 pi)/2 = 0.0230957...
"""
import mpmath as mp
mp.mp.dps = 90
NMAX = 24

def log_gauge(u):   # log[ (1/2) s (s-1)->regularized ... ]: gauge = (1/2) s pi^(-s/2) Gamma(s/2)
    s = 1 + u
    return mp.log(mp.mpf(1)/2) + mp.log(s) - s/2 * mp.log(mp.pi) + mp.loggamma(s/2)

def log_prime(u):   # log[ (s-1) zeta(s) ]  (pole regularized; prime/arithmetic carrier)
    s = 1 + u
    return mp.log((s - 1) * mp.zeta(s)) if u != 0 else mp.log(mp.mpf(1))

cg = mp.taylor(log_gauge, 0, NMAX)
cp = mp.taylor(log_prime, 0, NMAX)

def li(coeffs, n):
    return n * mp.fsum(mp.binomial(n - 1, n - j) * coeffs[j] for j in range(1, n + 1))

anchor = 1 + mp.euler/2 - mp.log(4*mp.pi)/2
print(f"anchor lambda_1 (closed form) = {mp.nstr(anchor, 12)}")
print(f"{'n':>3} {'lambda_n':>16} {'gauge part':>16} {'prime part':>16}  {'margin |p|/g':>12}  sign")
allpos = True
for n in range(1, NMAX + 1):
    lg = li(cg, n); lp = li(cp, n); lam = lg + lp
    allpos &= lam > 0
    print(f"{n:>3} {mp.nstr(lam, 10):>16} {mp.nstr(lg, 10):>16} {mp.nstr(lp, 10):>16}"
          f"  {mp.nstr(abs(lp)/lg, 6):>12}  {'+' if lam > 0 else 'NEGATIVE  <-- REGISTER HIT'}")
print()
print(f"lambda_1 check: computed {mp.nstr(li(cg,1)+li(cp,1), 12)} vs anchor {mp.nstr(anchor, 12)}")
print(f"ALL POSITIVE n<=24: {allpos}")
