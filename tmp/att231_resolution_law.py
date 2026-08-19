"""att231: is the resolution law GENERAL?  Prediction with no free parameters:
signal = -2 y0^2 P'(x0)^2 / ||c||^2, where P is the real polynomial killing the
real zeros (and x0 when the plant is in open space) — the y0^2 law times a
Christoffel-type factor.  Compare against measured min-eigs."""
from mpmath import mp, mpf, mpc, matrix, eighe, polyval, nstr
mp.dps = 50
ZS = [mpf('14.134725141734693790'), mpf('21.022039638771554993'),
      mpf('25.010857580145688763')]

def measured(x0, y0, n=5):
    z = mpc(mpf(x0), mpf(y0))
    mu = [sum(x**k for x in ZS) + (z**k + z.conjugate()**k).real for k in range(2*n)]
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    ev = [e.real for e in eighe(M, eigvals_only=True)]
    return min(ev)

def poly_from_roots(rs):
    c = [mpf(1)]
    for r in rs:
        c = [mpf(0)] + c
        for i in range(len(c)-1): c[i] -= r*c[i+1]
    return c                      # ascending coefficients

def predicted(x0, y0):
    """open-space plant: P = (x-x1)(x-x2)(x-x3)(x-x0), quartic, all 4 roots."""
    c = poly_from_roots(ZS + [mpf(x0)])
    # P'(x0)
    dc = [c[i]*i for i in range(1, len(c))]
    dP = sum(dc[i]*mpf(x0)**i for i in range(len(dc)))
    nrm2 = sum(ci**2 for ci in c)
    return -2*mpf(y0)**2 * dP**2 / nrm2

print("open-space plants, y0 = 0.01, n = 5:")
print("   x0        measured        predicted       ratio")
for x0 in ['11','12','16','18','23','28','29']:
    m = measured(x0,'0.01'); p = predicted(x0,'0.01')
    print(f" {x0:>5}  {nstr(m,5):>14}  {nstr(p,5):>14}   {nstr(m/p,5)}")

print("\ncollision plants (x0 = an actual zero) — only 3 conditions, extra freedom:")
for x0 in ['14.134725141734693790','21.022039638771554993']:
    m = measured(x0,'0.01'); p = predicted(x0,'0.01')
    print(f" {x0[:9]:>9}  measured {nstr(m,5):>13}  4-root pred {nstr(p,5):>13}"
          f"   ratio {nstr(m/p,4) if p != 0 else 'n/a'}")

print("\ndepth check of the SAME law at one position (x0=18):")
for y0 in ['0.02','0.01','0.005']:
    m = measured('18',y0); p = predicted('18',y0)
    print(f"   y0={y0:>6}: measured {nstr(m,5):>13}  predicted {nstr(p,5):>13}"
          f"   ratio {nstr(m/p,6)}")
