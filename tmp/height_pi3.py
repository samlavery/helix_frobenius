"""kClimb p y = exp y / p  with PITCH p = pi/3.
So the integer index at ordinate y is k = e^y / (pi/3) = 3 e^y / pi,
and the mu6 wall is k = 3 mod 6.  Test k mod 6 and frac(k).
"""
import mpmath as mp, numpy as np
K=150; mp.mp.dps=260
p = mp.pi/3
rows=[]
for i in range(1,K+1):
    g=mp.im(mp.zetazero(i)); k=mp.e**g/p
    rows.append((float(g), mp.frac(k), mp.frac(k/6)))
mp.mp.dps=340
bad=sum(1 for i in (1,75,150) if abs(mp.frac(mp.e**mp.im(mp.zetazero(i))/p)-rows[i-1][1])>mp.mpf(10)**-15)
print(f"N={K}, max gamma={rows[-1][0]:.1f}, precision failures={bad}")
fr=np.array([float(r[1]) for r in rows]); c6=np.array([float(r[2]) for r in rows])
n=len(fr); floor=1/np.sqrt(n)
print(f"noise floor={floor:.4f}")
for nm,x in [("frac(k)",fr),("k/6 mod 1",c6)]:
    for h in (1,2,3):
        c=abs(np.exp(2j*np.pi*h*x).mean()); print(f"  {nm:11s} h={h}: |c|={c:.4f} ({c/floor:.2f}x)")
hh,_=np.histogram(c6*6,bins=6,range=(0,6))
print(f"  cell counts {hh} exp {n/6:.1f}  chi2={((hh-n/6)**2/(n/6)).sum():.2f}")
near=np.minimum(fr,1-fr); print(f"  within 0.05 of a step edge: {(near<0.05).sum()} exp {0.1*n:.1f}")
