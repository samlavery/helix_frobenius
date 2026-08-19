"""att230: HOW THE PLANTED PAIR CONTAMINATES DOWNSTREAM MEASUREMENTS.
The plant changes the function (A -> A*(z-w)(z-wbar)); every quantity measured
on it is about that object, not zeta.  Quantify: does the detection signal
(and hence any threshold calibrated from it) depend on WHERE and at what SIZE
we plant?"""
from mpmath import mp, mpf, mpc, matrix, eighe, nstr
mp.dps = 50
ZS = [mpf('14.134725141734693790'), mpf('21.022039638771554993'),
      mpf('25.010857580145688763')]

def sig(x0, y0, n):
    z = mpc(mpf(x0), mpf(y0))
    mu = [sum(x**k for x in ZS) + (z**k + z.conjugate()**k).real
          for k in range(2*n)]
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    ev = [e.real for e in eighe(M, eigvals_only=True)]
    return min(ev), max(abs(e) for e in ev)

print("(1) POSITION dependence — same depth y0=0.01, n=5, moving the plant:")
print("   x0        min-eig        scale        relative signal")
for x0 in ['11','12','14.134725','16','18','21.022040','23','25.010858','28','29']:
    mn, sc = sig(x0, '0.01', 5)
    print(f" {x0:>10}  {nstr(mn,4):>13}  {nstr(sc,3):>10}  {nstr(abs(mn)/sc,3):>10}")

print("\n(2) SIZE dependence — same plant (18 + 0.01i), varying n:")
for n in [3,4,5,6,7]:
    mn, sc = sig('18','0.01',n)
    print(f"   n={n}: min-eig {nstr(mn,4):>13}  scale {nstr(sc,3):>10}"
          f"  relative {nstr(abs(mn)/sc,3):>10}")

print("\n(3) the y0^2 law across positions (is the exponent stable?):")
for x0 in ['12','18','24']:
    a,_ = sig(x0,'0.02',5); b,_ = sig(x0,'0.01',5)
    print(f"   x0={x0:>3}: ratio(y0 halved) = {nstr(a/b,5)}   (2^2 = 4 expected)")

print("\n(4) CONTAMINATION CHECK — true object vs planted object, n=5:")
def true_sig(n):
    mu = [sum(x**k for x in ZS) for k in range(2*n)]
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    ev = [e.real for e in eighe(M, eigvals_only=True)]
    return min(ev), max(abs(e) for e in ev), sum(1 for e in ev if e < -1e-40*max(abs(x) for x in ev))
mn, sc, nneg = true_sig(5)
print(f"   TRUE (3 real zeros only): min-eig {nstr(mn,4)}  n_-={nneg}"
      f"   [mu_0 = 3]")
mnp, scp = sig('18','0.01',5)
print(f"   PLANTED:                  min-eig {nstr(mnp,4)}  n_-=1"
      f"   [mu_0 = 5]  <- a different function")
