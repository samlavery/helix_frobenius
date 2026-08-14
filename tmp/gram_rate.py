"""Gram-law failure rate vs height.
Gram point g_n: theta(g_n) = n*pi.  Gram's law:  (-1)^n Z(g_n) > 0.
Failure rate is driven by S(t), whose variance ~ (1/2pi^2) log log t is UNBOUNDED,
so the rate must grow.  Question: does it stay below 1/3 (leaving room for the
2/3 density bound) or exceed it?
"""
import mpmath as mp, sys, time
mp.mp.dps = 15
def P(*a): print(*a); sys.stdout.flush()

def run(n0, cnt):
    t0=time.time(); bad=0; amb=0
    for n in range(n0, n0+cnt):
        g = mp.grampoint(n)
        Z = mp.siegelz(g)
        v = (-1)**n * Z
        if abs(Z) < 1e-8:                       # re-check near-zero at higher precision
            amb += 1
            with mp.workdps(30):
                g2=mp.grampoint(n); v=(-1)**n*mp.siegelz(g2)
        if v <= 0: bad += 1
    g_lo = mp.grampoint(n0); T=float(g_lo)
    lglg = math_loglog(T)
    P(f"  n0={n0:>9}  T~{T:>12.1f}  failures {bad:>4}/{cnt}  rate {bad/cnt:>7.2%}"
      f"   loglog T={lglg:.3f}  amb={amb}  [{time.time()-t0:.0f}s]")
    return bad/cnt, T

import math
def math_loglog(T): return math.log(math.log(T)) if T>math.e else 0.0

P("Gram-law failure rate by height  (Gram's law: (-1)^n Z(g_n) > 0)")
P(f"  {'':>9}  {'':>12}  target: is the rate < 1/3 = 33.3% ?")
res=[]
for n0,cnt in ((0,500),(1000,500),(10000,500),(100000,400),(1000000,300)):
    try:
        r,T = run(n0,cnt); res.append((n0,T,r))
    except Exception as e:
        P(f"  n0={n0}: {type(e).__name__}: {e}"); break
P("")
P("  summary:")
for n0,T,r in res:
    bar='#'*int(r*100)
    P(f"    n~{n0:<9} T~{T:<12.0f} rate {r:6.2%}  {bar}")
P(f"    1/3 threshold would be {'#'*33}")
