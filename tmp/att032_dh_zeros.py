"""ATTEMPT 032, stage G2b -- DH zeros with sigma > 1, to pin beta_max independently.
PRE-REGISTERED NULL: no zero of f_DH with sigma > 1 in the scanned box => the measured power
growth of Lambda_DH is an artifact and Prop 5.6 might still hold for DH.
Cross-check to be applied AFTER: 1 + delta = 2 beta_max - 1 (delta from the coefficient growth).
"""
import numpy as np, math, sys
import mpmath as mp
def P(*a): print(*a); sys.stdout.flush()

XI=(math.sqrt(((4/math.sqrt(5))*math.sin(2*math.pi/5))**2+((4/math.sqrt(5))*math.sin(4*math.pi/5))**2)
    -(4/math.sqrt(5))*math.sin(2*math.pi/5))/((4/math.sqrt(5))*math.sin(4*math.pi/5))
CHI4=np.array([0,1,1j,-1j,-1]); Acst=(1-1j*XI)/2
COEF=np.array([2*np.real(Acst*CHI4[r]) for r in range(5)])

_B2k=np.array([1/6,-1/30,1/42,-1/30,5/66,-691/2730,7/6])
def hurwitz(s, a, Nfac=3.0):
    """Euler-Maclaurin Hurwitz zeta, vectorised over complex s."""
    s=np.asarray(s,complex)
    M=int(max(60, Nfac*np.abs(s.imag).max()+60))
    n=np.arange(M)[:,None]
    head=np.sum((n+a)**(-s[None,:]),axis=0)
    Ma=M+a
    out=head+Ma**(1-s)/(s-1)+0.5*Ma**(-s)
    term=s*Ma**(-s-1)
    fac=1.0
    for k in range(1,8):
        out=out+_B2k[k-1]/math.factorial(2*k)*term
        term=term*(s+2*k-1)*(s+2*k)/(Ma*Ma)
    return out

def fDH(s):
    s=np.atleast_1d(np.asarray(s,complex))
    return 5.0**(-s)*sum(COEF[r]*hurwitz(s, r/5.0) for r in range(1,5))

# ---- gates
ds=sum(COEF[n%5]/float(n)**3 for n in range(1,400000))
P(f"gate 1: |f(3) - Dirichlet partial sum(4e5)| = {abs(fDH(3.0)[0]-ds):.3e}")
mp.mp.dps=25
def fmp(s):
    s=mp.mpc(s); return mp.power(5,-s)*sum(mp.mpf(COEF[r])*mp.zeta(s,mp.mpf(r)/5) for r in range(1,5))
for z in (complex(1.2,10.0), complex(1.5,80.0), complex(1.05,150.0)):
    P(f"gate 2: s={z}  EM {fDH(z)[0]:.10f}   mpmath {complex(fmp(z)):.10f}   diff {abs(fDH(z)[0]-complex(fmp(z))):.2e}")

# ---- scan
P("\nscan sigma in [1.001,1.40] x t in [0.5,120]")
sig=np.arange(1.001,1.401,0.015); tt=np.arange(0.5,120.0,0.03)
V=np.empty((len(sig),len(tt)))
for i,s0 in enumerate(sig):
    V[i]=np.abs(fDH(s0+1j*tt))
P(f"   global min |f| on grid = {V.min():.5f}")
cand=[]
for i in range(1,len(sig)-1):
    row=V[i]
    loc=np.nonzero((row[1:-1]<row[:-2])&(row[1:-1]<row[2:]))[0]+1
    for j in loc:
        if row[j]<V[i-1,j] and row[j]<V[i+1,j] and row[j]<0.25:
            cand.append((row[j],sig[i],tt[j]))
cand.sort()
P(f"   {len(cand)} interior local minima below 0.25")
zeros=[]
for v,s0,t0 in cand[:60]:
    try:
        r=mp.findroot(fmp, mp.mpc(s0,t0), tol=mp.mpf('1e-25'))
        b,t=float(mp.re(r)),float(mp.im(r))
        if abs(fmp(r))<1e-16 and b>1.0 and 0<t<125 and not any(abs(b-x)<1e-7 and abs(t-y)<1e-7 for x,y in zeros):
            zeros.append((b,t))
    except Exception: pass
zeros.sort(key=lambda z:z[1])
P(f"\n{len(zeros)} distinct zeros of f_DH with sigma>1, t in (0,125):")
for b,t in zeros: P(f"    beta = {b:.7f}   t = {t:.5f}")
if zeros:
    bmax=max(b for b,_ in zeros)
    P(f"\n  beta_max on this box = {bmax:.6f}")
    P(f"  => sum_{{n<=x}}|c(n)|^2   ~ x^{{{2*bmax-1:.4f}}} , i.e. delta = {2*bmax-2:.4f}")
    P(f"  => sum_{{n<=x}}|c(n)|^2/n ~ x^{{{2*bmax-2:.4f}}}")
    np.save('att032_dh_sigma_gt1.npy',np.array(zeros))
else:
    P("  NULL HELD on this box: no sigma>1 zero found.")
