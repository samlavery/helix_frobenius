"""Are zeros ONE PER CELL in the theta-cell system (Gram intervals)?
Gram point g_n: theta(g_n) = n*pi.  Cell n = (g_{n-1}, g_n].
N(t) = theta(t)/pi + 1 + S(t), so theta-cells are the cell system whose COUNT
matches the zero count one-for-one -- unlike integer/height cells.
"""
import mpmath as mp, numpy as np
mp.mp.dps = 30

def gram(n):
    # solve theta(g) = n*pi ; theta increasing for t > 6.29
    f = lambda t: mp.siegeltheta(t) - n*mp.pi
    lo = mp.mpf(7) if n <= 0 else mp.mpf(10)
    hi = mp.mpf(20) + 4*mp.pi*abs(n)/mp.log(max(abs(n),2))
    while f(hi) < 0: hi *= 2
    return mp.findroot(f, (lo, hi), solver='bisect', tol=mp.mpf(10)**-25)

NZ = 300
gam = [mp.im(mp.zetazero(k)) for k in range(1, NZ+1)]
gmax = gam[-1]
# Gram points covering the range
gs = []
n = -1
while True:
    g = gram(n)
    gs.append((n, g))
    if g > gmax: break
    n += 1
print(f"{NZ} zeros up to gamma={float(gmax):.2f};  {len(gs)} Gram points")

# count zeros per Gram interval (g_{n-1}, g_n]
edges = [float(g) for _, g in gs]
z = np.array([float(x) for x in gam])
cnt = np.histogram(z, bins=edges)[0]
inrange = cnt.sum()
print(f"zeros inside the Gram range: {inrange}")
from collections import Counter
c = Counter(cnt.tolist())
print(f"zeros per cell: {dict(sorted(c.items()))}")
viol = (cnt != 1).sum()
print(f"cells with exactly one zero: {(cnt==1).sum()}/{len(cnt)}  ({100*(cnt==1).sum()/len(cnt):.1f}%)")
print(f"Gram's law violations: {viol}  ({100*viol/len(cnt):.1f}%)")

# where inside the cell does the zero sit?  0 = left edge, 1 = right edge
pos=[]
for i in range(len(edges)-1):
    lo,hi = edges[i], edges[i+1]
    zs = z[(z>lo)&(z<=hi)]
    for x in zs: pos.append((x-lo)/(hi-lo))
pos=np.array(pos)
print(f"\nposition within cell: mean={pos.mean():.4f} (uniform 0.5)  std={pos.std():.4f}")
print(f"  |mean e^(2pi i pos)| = {abs(np.exp(2j*np.pi*pos).mean()):.4f}   floor={1/np.sqrt(len(pos)):.4f}")
h,_=np.histogram(pos,bins=10,range=(0,1))
print(f"  decile counts {h}   expected {len(pos)/10:.1f}")
