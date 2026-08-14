"""Push the cheapest instrument: critical-point count + min gap + min L1, to t=1e5."""
import numpy as np, time, sys
from collections import Counter
def P(*a): print(*a); sys.stdout.flush()
def theta(t): return t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)+7/(5760*t**3)
def Psi(p): return np.cos(2*np.pi*(p*p-p-1/16))/np.cos(2*np.pi*p)
def d3(p,h=1e-3): return (Psi(p+2*h)-2*Psi(p+h)+2*Psi(p-h)-Psi(p-2*h))/(2*h**3)
def Z(t):
    t=np.asarray(t,float); tau=np.sqrt(t/(2*np.pi)); N=np.floor(tau).astype(np.int64)
    th=theta(t); s=np.zeros_like(t)
    for n in range(1,int(N.max())+1):
        m=N>=n; s[m]+=np.cos(th[m]-t[m]*np.log(n))/np.sqrt(n)
    p=tau-N
    return 2*s+((-1)**(N-1))*(2*np.pi/t)**0.25*(Psi(p)-d3(p)/(96*np.pi**2)*np.sqrt(2*np.pi/t))
T0,T1=1000.0,100000.0
h=1e-3; hd=0.05
tot_z=0; tot_c=0; cnt=Counter(); mind=(9e9,0); minL=(9e9,0); t0=time.time()
cur=T0
while cur<T1:
    step=0.004 if cur<20000 else 0.003
    end=min(cur+3_000_000*step,T1)
    ts=np.arange(cur,end,step)
    z=Z(ts); zp=(Z(ts+h)-Z(ts-h))/(2*h)
    s=np.sign(z); i=np.nonzero(s[:-1]*s[1:]<0)[0]
    g=ts[i]-z[i]*(ts[i+1]-ts[i])/(z[i+1]-z[i])
    sp=np.sign(zp); j=np.nonzero(sp[:-1]*sp[1:]<0)[0]; c=ts[j]+step/2
    tot_z+=len(g); tot_c+=len(c)
    if len(g)>2:
        k=np.searchsorted(c,g[1:])-np.searchsorted(c,g[:-1])
        cnt.update(k.tolist())
        gaps=np.diff(g); mid=(g[:-1]+g[1:])/2
        d=gaps*np.log(mid/(2*np.pi))/(2*np.pi)
        q=int(np.argmin(d))
        if d[q]<mind[0]: mind=(float(d[q]),float(mid[q]))
        zz_=Z(mid); zpm=(Z(mid+hd)-Z(mid-hd))/(2*hd); zppm=(Z(mid+hd)-2*zz_+Z(mid-hd))/hd**2
        L=zpm*zpm-zz_*zppm
        r=int(np.argmin(L))
        if L[r]<minL[0]: minL=(float(L[r]),float(mid[r]))
    cur=end
    P(f"  ... t={cur:.0f}  zeros {tot_z:,}  [{time.time()-t0:.0f}s]")
P(f"\nDONE  t in [{T0:g},{T1:g}]   wall {time.time()-t0:.0f}s")
P(f"  zeros {tot_z:,}   critical points {tot_c:,}")
P(f"  critical points per gap: {dict(sorted(cnt.items()))}")
P(f"  gaps with exactly 1: {cnt.get(1,0):,} / {sum(cnt.values()):,} = {cnt.get(1,0)/sum(cnt.values()):.8f}")
P(f"  anomalous: {sum(v for k,v in cnt.items() if k!=1):,}")
P(f"  min normalised gap  {mind[0]:.6f} at t={mind[1]:.3f}")
P(f"  min L1 (Laguerre)   {minL[0]:.6e} at t={minL[1]:.3f}   {'NEGATIVE!' if minL[0]<0 else 'positive'}")
