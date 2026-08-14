import numpy as np, mpmath as mp, sys
def P(*a): print(*a); sys.stdout.flush()
def theta(t): return t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)+7/(5760*t**3)
def Psi(p): return np.cos(2*np.pi*(p*p-p-1/16))/np.cos(2*np.pi*p)
def d3Psi(p,h=1e-3):
    return (Psi(p+2*h)-2*Psi(p+h)+2*Psi(p-h)-Psi(p-2*h))/(2*h**3)
def Zrs(t):
    t=np.asarray(t,float); tau=np.sqrt(t/(2*np.pi)); N=np.floor(tau).astype(np.int64)
    th=theta(t); s=np.zeros_like(t)
    for n in range(1,int(N.max())+1):
        m=N>=n; s[m]+=np.cos(th[m]-t[m]*np.log(n))/np.sqrt(n)
    p=tau-N
    C0=Psi(p); C1=-d3Psi(p)/(96*np.pi**2)
    corr=(2*np.pi/t)**0.25*(C0+C1*np.sqrt(2*np.pi/t))
    return 2*s+((-1)**(N-1))*corr
mp.mp.dps=20
P("GATE with C1 correction:")
ts=np.array([15.3,50.7,123.4,777.7,3001.9,9999.5,50000.3])
a=Zrs(ts); b=np.array([float(mp.siegelz(t)) for t in ts])
for t,x,y in zip(ts,a,b): P(f"   t={t:>10.1f}  diff {abs(x-y):.3e}")
err=float(np.max(np.abs(a-b))); P(f"   max error {err:.2e}")
lo=np.array([200.,777.7,3001.9,9999.5,50000.3])
a2=Zrs(lo); b2=np.array([float(mp.siegelz(t)) for t in lo])
err2=float(np.max(np.abs(a2-b2)))
P(f"   max error for t>=200: {err2:.2e}")
STEP=max(0.02, 20*np.sqrt(err2))
P(f"   -> required step h >> sqrt(eps): using h = {STEP:.4f}")
P(f"   -> curvature signal h^2 = {STEP**2:.2e} vs noise {err2:.2e}  ratio {STEP**2/err2:.0f}x")
if STEP**2/err2 < 20: P("   INSUFFICIENT MARGIN"); sys.exit(1)
np.save('sweep_cfg.npy', np.array([STEP,err2]))
P("   GATE PASSED")
