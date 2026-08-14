"""Curvature sweep: exclude off-line zeros of zeta from ON-LINE data.
Riemann-Siegel Z in numpy (gated against mpmath), then convex windows of log|Z|.
Calibration standard: DH's off-line pair -> width 2d, floor ~ d^2."""
import numpy as np, mpmath as mp, time, sys
def P(*a): print(*a); sys.stdout.flush()

def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def Zrs(t):
    t=np.asarray(t,dtype=np.float64)
    tau=np.sqrt(t/(2*np.pi)); N=np.floor(tau).astype(np.int64)
    th=theta(t); s=np.zeros_like(t)
    for n in range(1,int(N.max())+1):
        m=N>=n
        s[m]+=np.cos(th[m]-t[m]*np.log(n))/np.sqrt(n)
    p=tau-N
    C0=np.cos(2*np.pi*(p*p-p-1/16))/np.cos(2*np.pi*p)
    return 2*s+((-1)**(N-1))*(2*np.pi/t)**0.25*C0

P("GATE: Riemann-Siegel vs mpmath.siegelz")
mp.mp.dps=20
ts=np.array([15.3,50.7,123.4,777.7,3001.9,9999.5])
a=Zrs(ts); b=np.array([float(mp.siegelz(t)) for t in ts])
for t,x,y in zip(ts,a,b): P(f"   t={t:>9.1f}  RS {x:>12.7f}   mpmath {y:>12.7f}   diff {abs(x-y):.2e}")
err=np.max(np.abs(a-b))
P(f"   max abs error {err:.2e}  -> {'PASS' if err<1e-3 else 'FAIL'}\n")
assert err<1e-3

T0,T1,STEP=10.0,20000.0,0.001
P(f"SWEEP t in [{T0},{T1}] step {STEP}  ({int((T1-T0)/STEP):,} points)")
t0=time.time()
allseg=[]; nz=0
CH=2_000_000
tcur=T0
while tcur<T1:
    tend=min(tcur+CH*STEP,T1)
    ts=np.arange(tcur,tend,STEP)
    Z=Zrs(ts)
    lg=np.log(np.abs(Z)+1e-300)
    d2=lg[2:]-2*lg[1:-1]+lg[:-2]
    tm=ts[1:-1]
    conv=d2>0
    s=np.sign(Z); zc=ts[np.nonzero(s[:-1]*s[1:]<0)[0]]
    nz+=len(zc)
    i=0
    while i<len(conv):
        if conv[i]:
            j=i
            while j+1<len(conv) and conv[j+1]: j+=1
            a_,b_=tm[i],tm[j]
            if j>i:                      # width > 1 step
                m=(ts>=a_)&(ts<=b_)
                allseg.append((a_,b_,b_-a_,float(np.min(np.abs(Z[m]))),
                               int(np.sum((zc>a_)&(zc<b_)))))
            i=j+1
        else: i+=1
    tcur=tend
P(f"  done in {time.time()-t0:.0f}s   zeros (sign changes): {nz:,}")
P(f"  convex windows wider than one step: {len(allseg):,}")
if allseg:
    W=np.array([s[2] for s in allseg]); F=np.array([s[3] for s in allseg])
    P(f"  widths : max {W.max():.5f}   99.9th pct {np.percentile(W,99.9):.5f}")
    P(f"  floors : max {F.max():.3e}   99.9th pct {np.percentile(F,99.9):.3e}")
    k=np.argmax(W)
    P(f"  widest window: [{allseg[k][0]:.4f},{allseg[k][1]:.4f}] width {allseg[k][2]:.5f}"
      f"  floor {allseg[k][3]:.3e}  zeros inside {allseg[k][4]}")
    P(f"\n  DH calibration: width 0.5709, floor 0.341 for depth d=0.3085")
    P(f"  EXCLUSION: widest zeta window {W.max():.5f} => any off-line pair has 2d < that,")
    P(f"             i.e. depth d < {W.max()/2:.6f} for all t in [{T0},{T1}]")
