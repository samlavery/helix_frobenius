import mpmath as mp, numpy as np
K=150
mp.mp.dps=260
rows=[]
for k in range(1,K+1):
    g=mp.im(mp.zetazero(k)); Z=mp.e**g
    rows.append((k,float(g),mp.frac(Z),mp.frac(Z/6)))
# precision guard: recompute a sample at higher dps
mp.mp.dps=340
bad=0
for k in (1,50,100,150):
    g=mp.im(mp.zetazero(k)); f=mp.frac(mp.e**g)
    if abs(f-rows[k-1][2])>mp.mpf(10)**(-15): bad+=1
print(f"N={K} zeros, max gamma={rows[-1][1]:.1f}, precision-guard failures={bad}")
fr=np.array([float(r[2]) for r in rows]); c6=np.array([float(r[3]) for r in rows])
n=len(fr); floor=1/np.sqrt(n)
print(f"\nnoise floor 1/sqrt(n) = {floor:.4f}")
for name,x,mod in [("frac(Z) on [0,1)",fr,1.0),("Z/6 mod 1 (cell)",c6,1.0)]:
    for h in (1,2,3):
        c=abs(np.exp(2j*np.pi*h*x).mean())
        print(f"  {name:20s} harmonic {h}: |c|={c:.4f}  ({c/floor:.2f} x floor)")
h6,_=np.histogram(c6*6,bins=6,range=(0,6))
print(f"\n  cell counts {h6}  expected {n/6:.1f}   chi2={((h6-n/6)**2/(n/6)).sum():.2f} (5 df)")
near=np.minimum(fr,1-fr)
print(f"  zeros within 0.05 of an integer height: {(near<0.05).sum()} (expected {0.1*n:.1f})")
