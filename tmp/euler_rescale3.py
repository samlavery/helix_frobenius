"""What is ACTUALLY free?
  d = 1                       FORCED: the delta weight is the zero count (rho=rho' term)
  F(a) = |a| for |a| <= 1     FORCED: Montgomery's theorem, unconditional
  F(a) = f(a) for |a| > 1     FREE: this is the unknown pair correlation
  F >= 0, and H <= 1          physical gates (H is a proportion)
So the ONLY freedom is the large-a tail. Scan it."""
import numpy as np
from scipy.integrate import quad
CAP=0.68185
def H(lam, tail):
    F=lambda a: abs(a) if abs(a)<=1 else tail(abs(a))
    I=quad(lambda a:(lam-abs(a))*F(a), -lam, lam, limit=400, points=[-1,0,1])[0]
    return 2.0 - (lam + I)/lam**2

print("GATE: tail = 1 (the conjectured continuation) must give the lam>=1 branch")
for lam in (1.0,1.5,2.0):
    got=H(lam, lambda a:1.0); want=3*lam**2/(1+3*lam**2)
    print(f"   lam={lam:4.2f}  H={got:.6f}   3lam^2/(1+3lam^2)={want:.6f}   "
          f"{'MATCH' if abs(got-want)<1e-6 else 'differ (different normalisation)'}")
print()
print("SCAN over constant tails f on |a|>1, and over lam.  Gate: 0 <= H <= 1.")
tries=0; best={}
rows=[]
for f in np.linspace(0.0,2.0,41):
    for lam in np.linspace(0.3,3.0,55):
        tries+=1
        h=H(lam, lambda a,f=f: f)
        if not (0.0 <= h <= 1.0):  continue        # PHYSICAL GATE
        rows.append((h,f,lam))
rows.sort(reverse=True)
print(f"  trials: {tries}   surviving the physical gate: {len(rows)}")
print(f"\n  {'H':>9}{'tail f':>9}{'lam':>7}   note")
for h,f,lam in rows[:10]:
    note='tail=1 is the CONJECTURED truth' if abs(f-1)<1e-9 else ('tail<1: F would dip BELOW the conjectured value' if f<1 else '')
    print(f"  {h:>9.5f}{f:>9.3f}{lam:>7.3f}   {note}")
print(f"\n  at the proven boundary lam=1, any tail: H = {H(1.0, lambda a:0.0):.5f} (tail irrelevant)")
print(f"  baseline 2/3 = {2/3:.5f}   cap = {CAP}")
print("\n  WHAT EACH TAIL BUYS (best H over lam):")
for f in (0.0,0.5,1.0,1.5):
    b=max((h for h,ff,l in rows if abs(ff-f)<1e-9), default=float('nan'))
    print(f"    tail f={f:4.2f}  best H = {b:.5f}   {'> cap' if b>CAP else ''}")
