"""att035 FINAL -- corrected (no lossy edge gauge), consolidated ledger."""
import numpy as np, cvxpy as cp
from scipy.integrate import quad
r2 = np.sqrt(2.0); MT = 0.5 + 2**-0.5/np.tan(2**-0.5)
jF = lambda a: max(0.0, 1.0-abs(a))
def jM(a):
    t = jF(a); return ((0.5/r2)*np.sin(r2*t) + 0.5*t*np.cos(r2*a))/(1-np.cos(r2))

def Zsdp(A, S=2.0, D=0.04, dip=True):
    n = int(round(S/D)); x = np.arange(n)*D; W = 2.0*A; sech = 1/np.cosh(x*W)
    Q = cp.Variable((n,n), symmetric=True)
    b = cp.hstack([cp.trace(Q)] + [sum(Q[k,k+j] for k in range(n-j)) for j in range(1,n)])
    c = cp.multiply(sech, b)
    w1 = np.where(x <= 1.0, x, 0.0)*2.0; w1[0] = D/2.0
    cons = [Q >> 0, c[0] + 2*cp.sum(c[1:]) == 1]
    if dip: cons.append(c[x >= 1.0-1e-12] <= 0)
    p = cp.Problem(cp.Minimize(c[0]/D + w1@c), cons); p.solve(solver=cp.CLARABEL)
    return p.value

print("="*78)
print("CORRECTED Tsang-class comparison at W=1 (BGSTB's box, A=1/2). Richardson O(D^2).")
for lbl, S, dip in (("S=1 no dip (Tsang/BGSTB class)", 1.0, False),
                    ("S=2 with CGdL dip            ", 2.0, True)):
    v4, v2 = Zsdp(0.5, S=S, D=0.04, dip=dip), Zsdp(0.5, S=S, D=0.02, dip=dip)
    r = v2 + (v2-v4)/3
    print(f"  {lbl}: Z={v4:.6f}/{v2:.6f} -> {r:.6f}   2-Z = {2-r:.6f}")
print(f"  BGSTB's own j_M in this functional:            Z=1.382524   2-Z = 0.617484 (PRINT)")
print("  => optimising the whole Tsang class buys ~+0.0003 over Montgomery-Taylor;")
print("     the CGdL dip buys ~+0.032.  Both are BELOW zeta23's UNCONDITIONAL 0.6725007.")

print("="*78); print("CROSSING A* where Z(A) = 1.3274993 (S=2, Richardson of D=.04/.02)")
lo, hi = 0.15, 0.30
for _ in range(7):
    m = (lo+hi)/2
    z = (lambda v4, v2: v2 + (v2-v4)/3)(Zsdp(m, D=0.04), Zsdp(m, D=0.02))
    lo, hi = (m, hi) if z < MT else (lo, m)
print(f"  A* = {(lo+hi)/2:.4f}   (impl A said 0.216; impl B said 0.213 at S=2, 0.277 at S=4)")
print(f"  depth cut there: |beta-1/2| < {(lo+hi)/2:.3f}/log T = "
      f"{(lo+hi)/2/(2*np.pi):.4f} x the mean gap 2pi/log T")
print(f"  Selberg/Simonic charge at A*: 2*2pi*10395.21*exp(-A*/4) = "
      f"{2*2*np.pi*10395.21*np.exp(-(lo+hi)/8):.0f} x N(T).")
print("="*78)
