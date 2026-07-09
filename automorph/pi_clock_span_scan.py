"""Span-dependence scan: measure the ln8-window feature at spans 50,100,200,400
using the SAME pipeline. If it's a real line it stays; if intermod sideband it
disperses/shifts. Also identify the 4pi/3 (~4.206) peak and the pi/3 bump."""
import math
import numpy as np

amp = np.load("pi_clock_amp.npy")
ln = np.load("pi_clock_ln.npy")
nz = amp != 0
amp = amp[nz].copy(); ln = ln[nz].copy()
dy = 0.01

def sweep(t_lo, t_hi):
    ny = int((t_hi - t_lo) / dy) + 1
    z = (amp * np.exp(-1j * t_lo * ln)).astype(np.complex128)
    stp = np.exp(-1j * dy * ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum(); z *= stp
    return np.abs(F)

def spec(absF, t_lo, t_hi):
    x = np.log(np.maximum(absF, np.percentile(absF, 1.0)))
    x -= x.mean()
    X = np.fft.rfft(x * np.hanning(len(x)))
    P = np.abs(X)**2
    om = 2*math.pi*np.fft.rfftfreq(len(x), d=dy)
    return P, om

def feat(P, om, target, core=0.02, bglo=0.09, bghi=0.28):
    dom = om[1]-om[0]
    res = 2*math.pi/(len(P)*2*dy)  # not used
    sel = np.abs(om - target) < max(core, 0.03)
    bg = (np.abs(om - target) > bglo) & (np.abs(om - target) < bghi)
    i = np.where(sel)[0]; imax = i[np.argmax(P[i])]
    # parabolic
    if 0 < imax < len(P)-1:
        y0,y1,y2 = P[imax-1],P[imax],P[imax+1]; d=(y0-2*y1+y2)
        delta = 0.5*(y0-y2)/d if d else 0.0
    else:
        delta = 0.0
    om_i = om[imax] + delta*dom
    return P[imax]/np.median(P[bg]), om_i, om[imax]

print("Span-dependence of the ln8-window feature (target = midpoint 2.0869):")
print("  also tracking exact ln8=2.07944 and 2pi/3=2.09440 separately")
print("  %-7s %-14s %-11s | %-11s | %-11s" % ("span","pk/bg@2.087","om_interp","pk/bg@ln8","pk/bg@2pi3"))
for (a,b) in [(50,150),(50,250),(50,350),(50,450),(50,650)]:
    absF = sweep(a,b)
    P, om = spec(absF, a, b)
    r0,oi0,ob0 = feat(P,om, 2.0869)
    r1,_,_ = feat(P,om, math.log(8), core=0.008)
    r2,_,_ = feat(P,om, 2*math.pi/3, core=0.008)
    print("  %-7s %-14.1f %-11.5f | %-11.1f | %-11.1f" % ("%d-%d"%(a,b), r0, oi0, r1, r2))

print("\nIdentify the ~4.206 peak (labeled 4pi/3 candidate):")
absF = sweep(50,450); P,om = spec(absF,50,450)
r,oi,ob = feat(P,om,4.206,core=0.02)
print("  peak at om_interp=%.5f  pk/bg=%.1f" % (oi, r))
print("  candidates near here:")
for lbl,val in [("ln(67)",math.log(67)),("ln4+ln7",math.log(4)+math.log(7)),
                ("ln(4*7)=ln28",math.log(28)),("ln(64)=6ln2",math.log(64)),
                ("2*ln9-... ",0),("ln7+ln9",math.log(7)+math.log(9)),
                ("ln63",math.log(63)),("4pi/3",4*math.pi/3),("ln65",math.log(65))]:
    if val: print("    %-14s = %.5f  (d=%.4f)" % (lbl,val,abs(val-oi)))

print("\nIdentify the pi/3 (~1.064) small bump and pi/2:")
for tgt,lbl in [(math.pi/3,"pi/3"),(math.pi/2,"pi/2")]:
    r,oi,ob = feat(P,om,tgt,core=0.03)
    # nearby log lines
    near=[]
    for k in range(2,20):
        if abs(math.log(k)-oi)<0.04: near.append(("ln%d"%k,math.log(k)))
    print("  %-5s: peak om_interp=%.5f pk/bg=%.1f  near: %s" % (lbl,oi,r,
          ", ".join("%s=%.4f"%(n,v) for n,v in near) or "none"))
