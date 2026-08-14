"""Jensen polynomials for xi (Griffin-Ono-Rolen-Zagier).
RH <=> J^{d,n}(X) = sum_j C(d,j) gamma(n+j) X^j is HYPERBOLIC (all roots real) for all d,n.
GORZ proved: for each d, hyperbolic for all n >> 0.  The open part is small n.
GATE: reproduce known gamma(n) magnitudes and check a d=2 case against Turan."""
import mpmath as mp, sys
from math import comb
mp.mp.dps=60
def P(*a): print(*a); sys.stdout.flush()
def F(z):
    return (-1+4*z**2)/8 * mp.power(mp.pi,-mp.mpf(1)/4 - z/2) * mp.gamma(mp.mpf(1)/4+z/2) * mp.zeta(mp.mpf(1)/2+z)
NC=30
P("computing Taylor coefficients of the xi-generating function ...")
co=mp.taylor(F, 0, 2*NC+2)
gam=[co[2*n]*mp.factorial(n) for n in range(NC+1)]   # gamma(n)/n! = coeff of z^{2n}
P(f"  gamma(0..5) = {[mp.nstr(g,8) for g in gam[:6]]}")
P(f"  all gamma(n) > 0 for n<= {NC}? {all(g>0 for g in gam[:NC+1])}")
P()
def hyperbolic(d,n):
    c=[gam[n+j]*comb(d,j) for j in range(d+1)]
    if any(x==0 for x in c): return None,None
    r=mp.polyroots(list(reversed(c)), maxsteps=200, extraprec=400)
    im=max(abs(mp.im(x)) for x in r); sc=max(abs(x) for x in r)
    return (im/sc < mp.mpf('1e-20')), float(im/sc)
P("HYPERBOLICITY of J^{d,n}:")
P(f"  {'d':>3}" + "".join(f"{f'n={n}':>9}" for n in range(0,9)))
bad=[]
for d in range(2,9):
    row=""
    for n in range(0,9):
        if n+d>NC: row+=f"{'-':>9}"; continue
        h,v=hyperbolic(d,n)
        row+=f"{('YES' if h else 'NO'):>9}"
        if h is False: bad.append((d,n,v))
    P(f"  {d:>3}"+row)
P()
if bad:
    P(f"  NON-hyperbolic cases: {len(bad)}")
    for d,n,v in bad[:10]: P(f"    d={d} n={n}  max|Im root|/scale = {v:.3e}")
else:
    P("  ALL tested Jensen polynomials are hyperbolic -> consistent with RH")
