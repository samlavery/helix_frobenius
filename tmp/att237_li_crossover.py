"""att237: Li-criterion RESOLUTION LAW.  The planted quadruple's contribution
Q(n) is exact (4 points); the true lambda_n grows like (n/2)log(n/2pi).
Find where Q(n) drives the total negative -> the detection threshold n*(delta,gamma),
the Li-side analogue of the census y0^2 law."""
from mpmath import mp, mpf, mpc, log, pi, nstr, cos, arg
mp.dps = 40

def Q(n, beta, gamma):
    tot = mpf(0)
    for b in (mpf(beta), 1-mpf(beta)):
        for sgn in (1,-1):
            rho = mpc(b, sgn*mpf(gamma))
            tot += (1 - (1 - 1/rho)**n).real
    return tot

def lam_asym(n):
    # standard: lambda_n ~ (n/2)(log n - log(2*pi) - 1 + gamma_E) + ...
    ge = mpf('0.5772156649015328606')
    return (mpf(n)/2)*(log(n) - log(2*pi) - 1 + ge)

print("planted quadruple beta=0.8, gamma=18   (|1-1/rho| = 1.000925 on the 0.2 side)")
print("     n      Q(n)          lambda_n(asym)   total ~      negative?")
for n in [100, 1000, 5000, 10000, 12000, 15000, 20000, 30000]:
    q = Q(n, '0.8', '18'); l = lam_asym(n)
    print(f" {n:>7}  {nstr(q,7):>13}  {nstr(l,7):>13}  {nstr(l+q,7):>13}   {'YES' if l+q < 0 else 'no'}")

print("\nthreshold vs depth (gamma = 18):")
for beta in ['0.9','0.8','0.7','0.6','0.55']:
    d = abs(mpf(beta)-mpf('0.5'))
    lo, hi = 100, 4000000
    while hi - lo > max(100, lo//50):
        mid = (lo+hi)//2
        if lam_asym(mid) + Q(mid, beta, '18') < 0: hi = mid
        else: lo = mid
    print(f"  beta={beta} (delta={float(d):.2f}): first n with total<0  ~ {hi}"
          f"    gamma^2/delta = {float(324/d):.0f}")

print("\nthreshold vs height (delta = 0.3, beta = 0.8):")
for g in ['10','18','30','50']:
    lo, hi = 100, 20000000
    while hi - lo > max(100, lo//50):
        mid = (lo+hi)//2
        if lam_asym(mid) + Q(mid, '0.8', g) < 0: hi = mid
        else: lo = mid
    print(f"  gamma={g:>3}: first n ~ {hi:>9}    gamma^2/delta = {float(mpf(g)**2/mpf('0.3')):.0f}")
