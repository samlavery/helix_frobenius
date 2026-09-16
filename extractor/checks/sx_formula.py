"""Check the paper's printed S_x formula against the implementation's Clocks.S.

Paper prints:  S_x(t) = -(1/pi) sum_{n<=x^3} Lambda(n) w_x(n) / (sqrt(n) log n) * sin(t log n)
with w_x = 1 for n <= x, tapering to 0 by n = x^3.
Pre-registered: max |formula - Clocks.S| over the sample must be < 1e-12 (same arithmetic);
anything larger means the paper misdescribes the code.
"""
import sys, os, math
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'extractor'))
sys.path.insert(0, 'extractor')
import numpy as np
from helix_extractor import Clocks, prime_powers

x = 20
C = Clocks(x)

def S_paper(t, x):
    X = x**3
    idx, lam = prime_powers(X)
    n = idx.astype(float); L = math.log(x); lx2 = L*L
    w = np.ones_like(lam)
    mid = (idx > x) & (idx <= x*x); hi = idx > x*x
    w[mid] *= (np.log(X/n[mid])**2 - 2.0*np.log(x*x/n[mid])**2)/(2.0*lx2)
    w[hi]  *= np.log(X/n[hi])**2/(2.0*lx2)
    return -(1.0/math.pi)*np.sum(lam*w/(np.sqrt(n)*np.log(n))*np.sin(t*np.log(n)))

worst = 0.0
for t in [0.5, 1.0, 14.134725, 21.022, 50.0, 143.111, 500.0, 1419.4224]:
    a, b = S_paper(t, x), C.S(t)
    worst = max(worst, abs(a-b))
    print(f"  t={t:>12}   paper={a:+.15f}   code={b:+.15f}   diff={abs(a-b):.3e}")
print()
# weight endpoints, as the paper describes them
X = x**3
idx, lam = prime_powers(X); n = idx.astype(float); L=math.log(x); lx2=L*L
w = np.ones_like(lam)
mid=(idx>x)&(idx<=x*x); hi=idx>x*x
w[mid] *= (np.log(X/n[mid])**2 - 2.0*np.log(x*x/n[mid])**2)/(2.0*lx2)
w[hi]  *= np.log(X/n[hi])**2/(2.0*lx2)
print(f"  w_x at smallest n:   {w[0]:.6f}   (paper says 1 for n <= x)")
print(f"  w_x at largest n<=x^3: {w[-1]:.6f}  (paper says tapers to 0 by x^3)")
print(f"  max w = {w.max():.6f}, min w = {w.min():.6f}")
print()
print(f"worst |paper - code| = {worst:.3e}")
print("VERDICT:", "CONFIRMED" if worst < 1e-12 else "REFUTED")
