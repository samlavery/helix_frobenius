# att569 addendum (pre-registered): the C1 excess is a TRANSIENT LOCALIZED at the
# surgery height.  Windows [10,40] (contains gamma=25.01) vs [200,230] (far).
# PREDICTION: measurable C1/zeta deviations in window A at off-tooth frequencies;
# ratios = 1.000 in window B.  (Teeth persist identically in both.)
from mpmath import mp, mpc, zeta
import math, cmath
mp.dps = 15
g1 = 25.010857580145688763; b0 = 0.15
Zs = [complex(0.5+b0, g1), complex(0.5-b0, g1)]
Ps = [complex(0.5, g1), complex(0.5, g1)]
def QlogD(s):
    v = 0j
    for z in Zs: v += 1.0/(s - z)
    for p in Ps: v -= 1.0/(s - p)
    return v
def run(t0, t1):
    dt = 0.05; N = int((t1-t0)/dt)
    gz = [complex(zeta(mpc(2, t0+k*dt), derivative=1)/zeta(mpc(2, t0+k*dt))) for k in range(N+1)]
    gc = [gz[k] + QlogD(complex(2, t0+k*dt)) for k in range(N+1)]
    out = {}
    for name, w in [("ln2", math.log(2)), ("ln18", math.log(18)), ("ctrl2.75", 2.75)]:
        def sp(g):
            acc = 0j
            for k in range(N+1):
                t = t0+k*dt
                wnd = 0.5*(1-math.cos(2*math.pi*(t-t0)/(t1-t0)))
                acc += g[k]*cmath.exp(1j*w*t)*wnd
            return abs(acc*dt*2/(t1-t0))
        out[name] = (sp(gz), sp(gc))
    return out
for (a,b) in [(10.0,40.0), (200.0,230.0)]:
    r = run(a,b)
    print(f"window [{a:.0f},{b:.0f}]:")
    for k,(x,y) in r.items():
        print(f"  {k:>9} zeta {x:.4e}  C1 {y:.4e}  ratio {y/x:.3f}")
