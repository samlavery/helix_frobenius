"""att238: the Li-side resolution law, derived and checked.
For rho = beta + i*gamma with delta = beta - 1/2, the mirror point 1-rho has
|1 - 1/(1-rho)| = r > 1 and the quadruple contributes ~ -2 r^n cos(n*theta).
Violation of lambda_n >= 0 first becomes possible when 2 r^n exceeds the main
term lambda_n ~ (n/2)log(n/2pi).  Claim: log r = delta/gamma^2 to leading
order, so n* solves n*log r = log(n log n / 2), i.e. n* ~ (gamma^2/delta)*L."""
from mpmath import mp, mpf, mpc, log, pi, nstr, findroot
mp.dps = 40

print("(1) is log r = delta/gamma^2 ?")
print("  gamma  delta     log r          delta/gamma^2    ratio")
for g in ['10','18','30','50']:
    for d in ['0.3','0.1','0.02']:
        gg, dd = mpf(g), mpf(d)
        rho = mpc(mpf('0.5') - dd, gg)          # the mirror member, beta < 1/2
        r = abs(1 - 1/rho)
        print(f"  {g:>5}  {d:>5}   {nstr(log(r),8):>13}   {nstr(dd/gg**2,8):>13}"
              f"   {nstr(log(r)/(dd/gg**2),6)}")

ge = mpf('0.5772156649015328606')
def lam_asym(n): return (mpf(n)/2)*(log(n) - log(2*pi) - 1 + ge)

print("\n(2) detection order n*: solve  n log r = log(lambda_n)  ")
print("  gamma  delta      n*(solved)      gamma^2/delta   n*/(g^2/d)")
for g in ['10','18','30','50']:
    for d in ['0.3','0.1','0.02']:
        gg, dd = mpf(g), mpf(d)
        r = abs(1 - 1/mpc(mpf('0.5')-dd, gg)); lr = log(r)
        f = lambda n: n*lr - log(2*lam_asym(n))
        try:
            ns = findroot(f, mpf(gg**2/dd)*10)
            print(f"  {g:>5}  {d:>5}   {nstr(ns,7):>13}   {float(gg**2/dd):>13.0f}"
                  f"   {float(ns/(gg**2/dd)):>8.1f}")
        except Exception as e:
            print(f"  {g:>5}  {d:>5}   (no root found)")

print("\n(3) direct check at gamma=18, delta=0.3: scan for an actual violation")
def Q(n, beta, gamma):
    tot = mpf(0)
    for b in (mpf(beta), 1-mpf(beta)):
        for sgn in (1,-1):
            tot += (1 - (1 - 1/mpc(b, sgn*mpf(gamma)))**n).real
    return tot
first = None
for n in range(8000, 14000, 50):
    if lam_asym(n) + Q(n,'0.8','18') < 0:
        first = n; break
print(f"   first violating n found by scan: {first}   (law predicts ~1.2e4)")
