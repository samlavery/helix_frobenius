"""ATTEMPT 032 stage G2c -- NOISE AUDIT on the Lambda_DH recursion + direct abscissa test.
NULLS pre-registered:
 (a) float64 recursion is unstable: max|Lambda_DH| differs from the float128 recursion by >1%.
 (b) the coefficients are wrong: sum_{n<=N} Lambda_DH(n) n^{-2} != -f'/f(2) to 1e-8.
 (c) the abscissa of convergence of sum Lambda_DH(n) n^{-s} is <= 1 (no sigma>1 zeros felt),
     i.e. the partial sums at sigma = 1.05..1.5 converge as smoothly as zeta's do.
"""
import numpy as np, math, sys
import mpmath as mp
def P(*a): print(*a); sys.stdout.flush()
XI=(math.sqrt(((4/math.sqrt(5))*math.sin(2*math.pi/5))**2+((4/math.sqrt(5))*math.sin(4*math.pi/5))**2)
    -(4/math.sqrt(5))*math.sin(2*math.pi/5))/((4/math.sqrt(5))*math.sin(4*math.pi/5))
CHI4=np.array([0,1,1j,-1j,-1]); Acst=(1-1j*XI)/2
COEF=np.array([2*np.real(Acst*CHI4[r]) for r in range(5)])

def lam_f(N, dtype=np.float64):
    a=np.array([COEF[n%5] for n in range(N+1)],dtype); a[0]=0
    acc=np.zeros(N+1,dtype); acc[1:]=a[1:]*np.log(np.arange(1,N+1)).astype(dtype)
    Lam=np.zeros(N+1,dtype)
    for k in range(2,N+1):
        v=acc[k]; Lam[k]=v
        if v!=0: acc[2*k::k]-=v*a[2:N//k+1]
    return Lam

N=400000
L64=lam_f(N,np.float64); L128=lam_f(N,np.longdouble)
d=np.abs(L64-L128.astype(np.float64)); rel=d.max()/np.abs(L64).max()
P(f"(a) NOISE AUDIT  N={N}:  max|Lam64|={np.abs(L64).max():.6f}  max|Lam128|={float(np.abs(L128).max()):.6f}")
P(f"    max abs disagreement {d.max():.3e}, relative to peak {rel:.3e}   "
  f"{'PASS (stable)' if rel<1e-2 else 'FAIL (unstable)'}")

mp.mp.dps=25
def fmp(s):
    s=mp.mpc(s); return mp.power(5,-s)*sum(mp.mpf(COEF[r])*mp.zeta(s,mp.mpf(r)/5) for r in range(1,5))
n=np.arange(1,N+1)
P("\n(b)/(c) partial sums of  sum Lambda_DH(n) n^{-sigma}  vs  -f'/f(sigma)")
P(f"    {'sigma':>6} {'-f'+chr(39)+'/f':>14} {'n<=1e4':>14} {'n<=1e5':>14} {'n<=4e5':>14} {'|err| 4e5':>11}")
for sg in (3.0,2.0,1.6,1.4,1.3,1.2,1.1,1.05):
    h=mp.mpf('1e-8'); s=mp.mpf(sg)
    dlog=-(mp.log(abs(fmp(s+h)))-mp.log(abs(fmp(s-h))))/(2*h)
    ps=np.cumsum(L64[1:]/n**sg)
    P(f"    {sg:6.2f} {float(dlog):14.7f} {ps[9999]:14.7f} {ps[99999]:14.7f} {ps[N-1]:14.7f} "
      f"{abs(ps[N-1]-float(dlog)):11.3e}")
# zeta control, same table
def lam_vm(N):
    Lam=np.zeros(N+1); s=np.ones(N+1,bool); s[:2]=False
    for p in range(2,int(N**0.5)+1):
        if s[p]: s[p*p::p]=False
    for p in np.nonzero(s)[0]:
        q=int(p); lp=math.log(p)
        while q<=N: Lam[q]=lp; q*=p
    return Lam
Lz=lam_vm(N)
P("\n    zeta control (same table, -zeta'/zeta):")
for sg in (2.0,1.4,1.2,1.1,1.05):
    tv=float(-mp.zeta(mp.mpf(sg),derivative=1)/mp.zeta(mp.mpf(sg)))
    ps=np.cumsum(Lz[1:]/n**sg)
    P(f"    {sg:6.2f} {tv:14.7f} {ps[9999]:14.7f} {ps[99999]:14.7f} {ps[N-1]:14.7f} {abs(ps[N-1]-tv):11.3e}")
