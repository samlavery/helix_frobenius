"""Locate zeros of zeta' near the critical line and measure how close they get to Re=1/2.
Under RH all have Re > 1/2 (Speiser).  How close is the Speiser analogue of Lambda=0."""
import numpy as np, sys, time
from em_zeta import zz
def P(*a): print(*a); sys.stdout.flush()
def zp(s,N): return zz(s,N=N)[1]
def zpp(s,N,h=1e-4): return (zp(s+h,N)-zp(s-h,N))/(2*h)
def newton(s0,N,it=60):
    s=complex(s0)
    for _ in range(it):
        f=zp(np.array([s]),N)[0]; d=zpp(np.array([s]),N)[0]
        if abs(d)<1e-300: return None
        st=s-f/d
        if abs(st-s)<1e-13: s=st; break
        s=st
    return s if abs(zp(np.array([s]),N)[0])<1e-8 else None

# zeta zeros on the line via Z (reuse the RS routine)
def theta(t): return t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)+7/(5760*t**3)
def Psi(p): return np.cos(2*np.pi*(p*p-p-1/16))/np.cos(2*np.pi*p)
def d3(p,h=1e-3): return (Psi(p+2*h)-2*Psi(p+h)+2*Psi(p-h)-Psi(p-2*h))/(2*h**3)
def Zf(t):
    t=np.asarray(t,float); tau=np.sqrt(t/(2*np.pi)); Nn=np.floor(tau).astype(np.int64)
    th=theta(t); s=np.zeros_like(t)
    for n in range(1,int(Nn.max())+1):
        m=Nn>=n; s[m]+=np.cos(th[m]-t[m]*np.log(n))/np.sqrt(n)
    p=tau-Nn
    return 2*s+((-1)**(Nn-1))*(2*np.pi/t)**0.25*(Psi(p)-d3(p)/(96*np.pi**2)*np.sqrt(2*np.pi/t))

T0,T1=200.0,1200.0
ts=np.arange(T0,T1,0.005); z=Zf(ts); sg=np.sign(z)
i=np.nonzero(sg[:-1]*sg[1:]<0)[0]
g=ts[i]-z[i]*(ts[i+1]-ts[i])/(z[i+1]-z[i]); g.sort()
P(f"zeta zeros in [{T0:g},{T1:g}]: {len(g)}")
Nem=int(2*T1)
res=[]
t0=time.time()
for k in range(len(g)-1):
    mid=(g[k]+g[k+1])/2
    for off in (0.02,0.08,0.2,0.5):
        r=newton(complex(0.5+off,mid),Nem)
        if r is not None and 0.3<r.real<3.0 and abs(r.imag-mid)<(g[k+1]-g[k]):
            res.append((r.real,r.imag,g[k+1]-g[k])); break
P(f"zeta' zeros located: {len(res)}   [{time.time()-t0:.0f}s]")
R=np.array([r[0] for r in res]); T=np.array([r[1] for r in res]); G=np.array([r[2] for r in res])
sp=2*np.pi/np.log(T/(2*np.pi)); dn=G*np.log(T/(2*np.pi))/(2*np.pi)
P(f"\n  Re(rho') : min {R.min():.6f}  median {np.median(R):.6f}  max {R.max():.6f}")
P(f"  all > 1/2 ? {'YES' if R.min()>0.5 else 'NO -- SPEISER VIOLATION'}")
P(f"  min (Re - 1/2) = {R.min()-0.5:.6f}  at t = {T[np.argmin(R)]:.4f}")
P(f"  that zero sits in a zeta-gap of normalised width {dn[np.argmin(R)]:.5f} (mean 1)")
c=np.corrcoef(np.log(R-0.5), np.log(dn))[0,1]
P(f"\n  corr( log(Re-1/2), log(normalised zeta gap) ) = {c:+.4f}  over {len(R)} zeros")
o=np.argsort(R)[:8]
P(f"  closest approaches to the critical line:")
P(f"    {'Re-1/2':>10}{'t':>12}{'zeta gap (norm)':>18}")
for q in o: P(f"    {R[q]-0.5:>10.6f}{T[q]:>12.4f}{dn[q]:>18.5f}")
