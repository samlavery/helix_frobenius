import numpy as np, mpmath as mp, time, sys
def P(*a): print(*a); sys.stdout.flush()
def theta(t): return t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)+7/(5760*t**3)
def Psi(p): return np.cos(2*np.pi*(p*p-p-1/16))/np.cos(2*np.pi*p)
def d3Psi(p,h=1e-3): return (Psi(p+2*h)-2*Psi(p+h)+2*Psi(p-h)-Psi(p-2*h))/(2*h**3)
def Zrs(t):
    t=np.asarray(t,float); tau=np.sqrt(t/(2*np.pi)); N=np.floor(tau).astype(np.int64)
    th=theta(t); s=np.zeros_like(t)
    for n in range(1,int(N.max())+1):
        m=N>=n; s[m]+=np.cos(th[m]-t[m]*np.log(n))/np.sqrt(n)
    p=tau-N
    return 2*s+((-1)**(N-1))*(2*np.pi/t)**0.25*(Psi(p)-d3Psi(p)/(96*np.pi**2)*np.sqrt(2*np.pi/t))
T0,T1,STEP=1000.0,30000.0,0.05
P(f"SWEEP t in [{T0:g},{T1:g}] step {STEP}   ({int((T1-T0)/STEP):,} points)")
P(f"  accuracy at t>=1000 ~ 6.5e-6 ; curvature signal h^2 = {STEP**2:.1e} ; margin {STEP**2/6.5e-6:.0f}x")
P(f"  detection reach: window width 2d must exceed ~2 steps => d >~ {STEP:.3f}\n")
t0=time.time(); segs=[]; nz=0
cur=T0
while cur<T1:
    end=min(cur+2_000_000*STEP,T1)
    ts=np.arange(cur,end,STEP); Z=Zrs(ts)
    lg=np.log(np.abs(Z)+1e-300)
    d2=lg[2:]-2*lg[1:-1]+lg[:-2]; tm=ts[1:-1]
    s=np.sign(Z); zc=ts[np.nonzero(s[:-1]*s[1:]<0)[0]]; nz+=len(zc)
    conv=d2>0; i=0
    while i<len(conv):
        if conv[i]:
            j=i
            while j+1<len(conv) and conv[j+1]: j+=1
            if j>i:
                a_,b_=tm[i],tm[j]; m=(ts>=a_)&(ts<=b_)
                segs.append((a_,b_,b_-a_,float(np.min(np.abs(Z[m]))),
                             int(np.sum((zc>a_)&(zc<b_)))))
            i=j+1
        else: i+=1
    cur=end
P(f"  completed in {time.time()-t0:.0f}s   sign changes (on-line zeros): {nz:,}")
P(f"  convex windows spanning >1 step: {len(segs):,}")
if segs:
    W=np.array([s[2] for s in segs]); F=np.array([s[3] for s in segs]); NZI=np.array([s[4] for s in segs])
    P(f"  widths  max {W.max():.4f}   99.9pct {np.percentile(W,99.9):.4f}   median {np.median(W):.4f}")
    P(f"  floors  max {F.max():.3e}  99.9pct {np.percentile(F,99.9):.3e}")
    P(f"  windows with NO zero inside: {(NZI==0).sum():,}")
    emp=[s for s in segs if s[4]==0]
    if emp:
        k=int(np.argmax([e[2] for e in emp]))
        P(f"  widest EMPTY window: [{emp[k][0]:.3f},{emp[k][1]:.3f}] width {emp[k][2]:.4f} floor {emp[k][3]:.3e}")
    P(f"\n  DH CALIBRATION: depth 0.3085 -> width 0.571, floor 0.341, 0 zeros inside")
    P(f"  zeta widest empty window width = {max([e[2] for e in emp]) if emp else 0:.4f}")
    P(f"\n  EXCLUSION over t in [{T0:g},{T1:g}] ({nz:,} zeros):")
    P(f"    no off-line pair with depth d > {max(STEP, (max([e[2] for e in emp]) if emp else 0)/2):.4f}")
