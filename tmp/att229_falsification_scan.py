"""att229: FALSIFICATION SCAN — where does the unconditional detector fail?
Exact moments from support (argument principle): 3 real zeros + one planted
off-line pair at depth y0.  Question: at what depth does the negative
eigenvalue drop below a given working precision's noise floor?"""
from mpmath import mp, mpf, mpc, matrix, eighe, nstr

ZS = [mpf('14.134725141734693790'), mpf('21.022039638771554993'),
      mpf('25.010857580145688763')]
X0 = mpf('18')

def scan(y0, n, dps):
    mp.dps = dps
    z = mpc(X0, mpf(y0))
    mu = [sum(x**k for x in ZS) + (z**k + z.conjugate()**k).real
          for k in range(2*n)]
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    ev = [e.real for e in eighe(M, eigvals_only=True)]
    sc = max(abs(e) for e in ev)
    floor = sc * mpf(10)**(-dps+1)      # working-precision noise floor
    return min(ev), sc, floor

print("planted pair at 18 + i*y0, three real zeros, n = 5")
print(" y0        min-eig        matrix scale   noise floor(dps)  DETECTED?")
for dps in [16, 25, 50]:
    print(f"  --- working precision dps = {dps} ---")
    for y0 in ['0.3','0.1','0.03','0.01','0.003','0.001','1e-4','1e-5','1e-6']:
        mn, sc, fl = scan(y0, 5, dps)
        det = "YES" if mn < -fl else "no  (invisible)"
        print(f" {y0:>6}  {nstr(mn,4):>14}  {nstr(sc,3):>12}  {nstr(fl,3):>12}   {det}")
print("\nscaling law check (min-eig vs y0, dps=50, n=5):")
prev = None
for y0 in ['0.1','0.05','0.025','0.0125']:
    mn,_,_ = scan(y0,5,50)
    r = "" if prev is None else f"  ratio {nstr(prev/mn,4)}"
    print(f"  y0={y0:>7}: min-eig {nstr(mn,5)}{r}")
    prev = mn
