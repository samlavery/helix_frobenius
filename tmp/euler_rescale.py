"""SCAN: rescale the Euler product, watch the second moment.

certificate  H = 2 - M2/M1,   M2/M1 = (1/lam^2) * int_{-lam}^{lam} (lam-|a|) F(a) da
Montgomery:  F(a) = |a|  for |a| <= 1  (THEOREM), and the lam<=1 wall is exactly
"F is known only there".  Rescaling the Euler product by c dilates frequencies
log n -> c log n, so F(a) -> F(a/c)/c with support |a| <= c.

GATE: at c = 1 this must reproduce H(lam) = 2 - 1/lam - lam/3 exactly.
"""
import numpy as np
from scipy.integrate import quad

def H_from_F(lam, F):
    I = quad(lambda a: (lam-abs(a))*F(a), -lam, lam, limit=400)[0]
    return 2.0 - I/lam**2

F_mont = lambda a: abs(a) if abs(a) <= 1 else 1.0        # |a| then flat (Mont/RS)
def F_scaled(c):
    return lambda a: (abs(a/c) if abs(a/c) <= 1 else 1.0)/c

print("GATE  c=1: does the integral reproduce 2 - 1/lam - lam/3 ?")
ok=True
for lam in (0.5,0.7,0.85,1.0):
    got=H_from_F(lam,F_mont); want=2-1/lam-lam/3
    good=abs(got-want)<1e-9; ok&=good
    print(f"   lam={lam:4.2f}  computed {got:.9f}  closed form {want:.9f}  {'PASS' if good else 'FAIL'}")
assert ok, "gate failed"

print("\nSCAN: rescale c, bandwidth lam.  known-support constraint: lam <= c")
cs   = np.concatenate([np.linspace(0.5,3.0,26), [np.pi/3, np.pi/6, np.pi/2, np.sqrt(3), np.pi]])
lams = np.linspace(0.2, 3.0, 29)
rows=[]; tries=0
for c in cs:
    for lam in lams:
        tries+=1
        if lam > c:  continue                      # F unknown beyond |a| <= c
        rows.append((H_from_F(lam,F_scaled(c)), c, lam))
rows.sort(reverse=True)
print(f"  trials evaluated: {tries}   admissible (lam<=c): {len(rows)}")
print(f"\n  {'H':>9}{'c':>9}{'lam':>7}   note")
CAP=0.68185
for H,c,lam in rows[:12]:
    nm=''
    for v,n in ((np.pi/3,'c=pi/3'),(np.pi/6,'c=pi/6'),(np.pi/2,'c=pi/2'),
                (np.sqrt(3),'c=sqrt3'),(np.pi,'c=pi')):
        if abs(c-v)<1e-9: nm=n
    flag='ABOVE CAP' if H>CAP else ''
    print(f"  {H:>9.5f}{c:>9.5f}{lam:>7.3f}   {nm:<8} {flag}")
print(f"\n  baseline H(1) = {2-1-1/3:.5f}   bandwidth-one cap = {CAP}")
print("\n  named scales:")
for v,n in ((np.pi/6,'pi/6'),(1.0,'unit 1'),(np.pi/3,'pi/3'),(np.pi/2,'pi/2'),
            (np.sqrt(3),'sqrt3'),(np.pi,'pi')):
    best=max((H for H,c,l in rows if abs(c-v)<1e-9), default=float('nan'))
    print(f"    c = {n:<7} {v:7.5f}   best H = {best:.5f}"
          f"   {'> cap' if best>CAP else ''}")
