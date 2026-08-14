"""EMPIRICAL TEST of the carrier-scale hypothesis.

Corpus claim (compiled): eventArcs H = {k>=1 : e^{ikH} = -1}.
  pi3_arcs_eq   : eventArcs(pi/3) = {k : k = 3 mod 6}      -- mark REALIZED
  unit_arcs_empty: eventArcs(1)   = empty                   -- mark NEVER realized
  eventContribution = 1 at pi/3, 0 at 1  (by theorem, not by gate)
This is the "unit-1 is compatible with nothing" claim.  Test it, quantify it,
and then test what it buys: exact closure of the character banks on the cell.
"""
import numpy as np, mpmath as mp
from fractions import Fraction
mp.mp.dps = 40

print("="*74)
print("1. DOES THE CARRIER REALIZE THE ANTIPODAL MARK  e^{ikH} = -1 ?")
print("="*74)
K = 2_000_000
for name, H in [("pi/3", mp.pi/3), ("pi/6", mp.pi/6), ("pi/2", mp.pi/2), ("1 (unit)", mp.mpf(1))]:
    Hf = float(H)
    k = np.arange(1, K+1, dtype=np.float64)
    d = np.abs(np.cos(k*Hf) + 1.0) + np.abs(np.sin(k*Hf))   # |e^{ikH}+1| (L1 proxy)
    i = int(np.argmin(d))
    exact = [j for j in range(1, 25) if abs(float(mp.cos(j*H)+1)) < 1e-30 and abs(float(mp.sin(j*H))) < 1e-30]
    print(f"  H={name:9s} first EXACT k with e^{{ikH}}=-1: {exact[:4] if exact else 'NONE'}"
          f"   min|e^{{ikH}}+1| over k<={K:,}: {d[i]:.3e} at k={i+1}")

print("\n  unit-1: the near-misses are the continued-fraction convergents of pi.")
print("  (k*1 ~ odd multiple of pi requires k/odd ~ pi, i.e. rational approx to pi)")
cf = mp.pslq([mp.pi, 1], maxcoeff=10**6, maxsteps=10**6)
for q in [1, 3, 7, 15, 292]:  # cf of pi
    pass
p_over_q = [(3,1),(22,7),(333,106),(355,113),(103993,33102)]
for p,q in p_over_q:
    k = p  # k ~ p, odd multiple q of pi
    val = float(abs(mp.cos(k) + 1) + abs(mp.sin(k)))
    print(f"    pi ~ {p}/{q}: k={p:6d}  |e^{{ik}}+1| = {val:.3e}")

print("\n" + "="*74)
print("2. WHAT IT BUYS: exact closure of character banks on the cell")
print("="*74)
def chi3(n): 
    r=n%3; return 1 if r==1 else (-1 if r==2 else 0)
def triv(n): return 1
def eta(n):  return 1 if n%2==1 else -1
for cname, cf_ in [("chi3",chi3),("trivial",triv),("eta",eta)]:
    print(f"\n  {cname}")
    for hname, H in [("pi/3", mp.pi/3), ("pi/6", mp.pi/6), ("1 (unit)", mp.mpf(1))]:
        row=[]
        for N in (6,12,60,600,6000):
            s = sum(cf_(n)*mp.e**(1j*n*H) for n in range(1,N+1))
            row.append(f"N={N}:{float(abs(s)):.3e}")
        print(f"    H={hname:9s} |bank| = " + "  ".join(row))
