"""CLOSED FORM FOR c_k  (dwell + scale + warp + harmonic energy thresholds).
   dwell : occupancy N_n(G) ~ (#splits) * Pr[all rails deliver]
   scale : rail p pays (p-1) per carry; DC carry rate q_p = (p-1)/2p
   warp  : G = c log n  ->  rail p must carry at rate theta_p = c log p /((k-1)(p-1))
   HARMONIC ENERGY THRESHOLD of rail p:  E_p = (p-1)^2 / (2p log p)
        rail p is SILENT for c <= E_p, and RADIATES (pays entropy) above it.
   Budget = log n (the split entropy).  c_k solves  sum_p I(theta_p||q_p)/log p = 1."""
import math
from sympy import primerange
def I(t,q):
    if t<=q: return 0.0
    t=min(t,1-1e-15)
    return t*math.log(t/q)+(1-t)*math.log((1-t)/(1-q))
PS=[int(p) for p in primerange(2,5000)]
def theta(c,p,k): return c*math.log(p)/((k-1)*(p-1))
def budget(c,k=2): return sum(I(theta(c,p,k),(p-1)/(2*p))/math.log(p) for p in PS)
print("HARMONIC ENERGY THRESHOLDS  E_p = (p-1)^2/(2p log p)   (rail silent below E_p)")
for p in [2,3,5,7,11,13,17]:
    print(f"   p={p:>3}:  E_p = {(p-1)**2/(2*p*math.log(p)):.4f}")
print()
for k in (2,3,4):
    lo,hi=0.01,40.0
    for _ in range(200):
        m=(lo+hi)/2
        if budget(m,k)<1: lo=m
        else: hi=m
    rad=[p for p in PS if theta(lo,p,k)>(p-1)/(2*p)]
    print(f"k={k}:  c_k = {lo:.4f}   radiating rails = {rad[:10]}"
          f"   (DC floor {(k-1)/(2*math.log(2)):.4f})")
print(f"\nMEASURED c_2 (DC-first, 3 dyadic windows): 1.2344 / 1.2511 / 1.2403")
print(f"budget at measured c_2=1.2403 : {budget(1.2403,2):.4f}   (target 1.0)")
print("\nbudget curve:")
for c in (0.9,1.0,1.1,1.2,1.24,1.3,1.4,1.6):
    print(f"   c={c:.2f}  budget={budget(c,2):.4f}  radiating={[p for p in PS if theta(c,p,2)>(p-1)/(2*p)][:6]}")
