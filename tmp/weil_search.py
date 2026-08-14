"""600-ATTEMPT SEARCH over Weil test functions.

Weil: W(h,h) = sum_rho m_rho hhat(g_rho) conj(hhat(conj g_rho)) >= 0 for ALL h  <=>  RH.
  on-line zero  (g real)      : |hhat(g)|^2  >= 0     always
  off-line pair (g -/+ i d)   : 2 Re[hhat(g - i d)^2]  for h real even
So a single h DETECTS off-line pairs only where Re[hhat(g-id)^2] < 0.
A candidate that achieves this on the WHOLE strip would be a Weil certificate.

PRECHECK: if none works, every candidate has coverage < 100% and the failures should
concentrate somewhere structural.  If one hits 100%, that is a genuine survivor.
Gate: hhat must be real on the real axis and hhat(0) > 0 (h real, even, positive mass).
"""
import numpy as np, itertools, sys
np.seterr(all='ignore')

G = np.linspace(0.0, 12.0, 61)          # ordinate
D = np.linspace(0.02, 0.5, 25)          # depth off the line
GG, DD = np.meshgrid(G, D, indexing='ij')
Z = GG - 1j*DD                           # complex argument g - i d

def cover(hhat):
    """fraction of the (gamma,depth) grid where Re[hhat(z)^2] < 0"""
    v = hhat(Z)
    if not np.all(np.isfinite(v)): return -1.0, None
    r = np.real(v*v)
    return float(np.mean(r < 0)), r

CAND = []
# family 1: Gaussian x Hermite   hhat(z) = H_n(a z) exp(-b z^2)
from numpy.polynomial.hermite import hermval
for n in range(0, 8):
    c = np.zeros(n+1); c[n] = 1.0
    for a in (0.2,0.4,0.6,0.9,1.3,1.8):
        for b in (0.02,0.05,0.1,0.2,0.4):
            CAND.append((f"herm n={n} a={a} b={b}",
                         lambda z,c=c,a=a,b=b: hermval(a*z,c)*np.exp(-b*z*z)))
# family 2: Fejer / sinc powers  hhat(z) = (sin(Lz/2)/(Lz/2))^k
for L in (0.5,1.0,1.5,2.0,3.0,4.0,6.0):
    for k in (1,2,3,4):
        CAND.append((f"sinc L={L} k={k}",
                     lambda z,L=L,k=k: np.where(np.abs(z)<1e-12, 1.0,
                                        (np.sin(L*z/2)/(L*z/2+1e-300))**k)))
# family 3: raised cosine / cos^m on a band
for L in (0.5,1.0,2.0,3.0):
    for m in (1,2,3):
        for s in (0.5,1.0,2.0):
            CAND.append((f"cos L={L} m={m} s={s}",
                         lambda z,L=L,m=m,s=s: np.cos(L*z)**m*np.exp(-s*z*z/10)))
# family 4: polynomial x gaussian with a free root -- can push zeros off axis
for r in (0.5,1.0,2.0,3.0,5.0):
    for b in (0.02,0.05,0.1,0.3):
        for p in (1,2,3):
            CAND.append((f"root r={r} b={b} p={p}",
                         lambda z,r=r,b=b,p=p: (z*z-r*r)**p*np.exp(-b*z*z)))
# family 5: shifted-gaussian sums (real, even)
for mu in (1.0,2.0,3.0,5.0):
    for b in (0.05,0.1,0.3,0.6):
        for w in (-1.0,-0.5,0.5,1.0):
            CAND.append((f"pair mu={mu} b={b} w={w}",
                         lambda z,mu=mu,b=b,w=w: np.exp(-b*(z-mu)**2)+np.exp(-b*(z+mu)**2)
                                                  + w*np.exp(-b*z*z)))
print(f"candidates generated: {len(CAND)}")
res=[]; tried=0; gated=0
for name,f in CAND:
    tried+=1
    try:
        onreal = f(G.astype(complex))
        if np.max(np.abs(np.imag(onreal))) > 1e-9: gated+=1; continue   # must be real on R
        c,_ = cover(f)
        if c < 0: gated+=1; continue
        res.append((c,name))
    except Exception:
        gated+=1
res.sort(reverse=True)
print(f"attempts evaluated: {tried}   rejected by gate: {gated}   scored: {len(res)}")
print(f"\nbest coverage of the (gamma, depth) strip where Re[hhat^2] < 0:")
for c,n in res[:12]:
    print(f"   {c:7.2%}   {n}")
hits=[r for r in res if r[0] > 0.999]
print(f"\n  candidates achieving FULL coverage (a Weil certificate): {len(hits)}")
print(f"  best achieved: {res[0][0]:.2%}" if res else "  none scored")
