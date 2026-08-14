"""ATTEMPT 024 -- the SIGN of O_1 below the wall x Zeta23 Prop 5.6.

WHY THE SIGN, AND WHY BELOW THE WALL.  O1_LOSSY_NOTE.md establishes that Prop. 5.6's
|O_1| << L^2 X is loose by 6-20x and that what it discards is smooth, monotone and NEGATIVE --
destructive prime interference.  Collecting that looseness by EVALUATING O_1 needs
Hardy-Littlewood, which is the input 7.5(a) already names, so it is not available
unconditionally.  But there is one component of the looseness that needs no prime-pair
information at all: the SIGN.  An absolute-value bound spends the estimate twice; a one-sided
bound O_1 <= 0 plus |O_1| <= L^2 X on the other side is strictly stronger and costs nothing --
IF the sign is actually definite where the method operates.

And "where the method operates" is lambda <= 1, which is exactly where the note never looked:
every table in it is at lambda >= 1.75.  Below the wall the cubic main term is identically zero,
since l1 = l + 2log2 - 1 > l >= L, so (L - l1)_+ = 0.  The sign there is pure residual.

PAIRING.  house: DC-first -- the exact common mode of O_1, -(T/6pi)(L-l1)_+^3, derived and
validated in O1_LOSSY_NOTE.md, which tells us precisely that it contributes NOTHING below the
wall and therefore that the sub-wall sign is a separate, unmeasured object.  classical: the
paper's Prop. 5.6 off-diagonal bound and the explicit formula's prime side.  MECHANISM: the
common mode is what an absolute-value bound cannot see; having evaluated it exactly, the
residual sign is the only remaining free lunch, and it lives below the wall.

STATED NULL, pre-registered.  O_1 changes sign, or is positive, somewhere in
lambda in [0.5, 1.0] across the accessible (T, eta) grid.  Then one-sidedness is false, there
is nothing to prove, and the two-sided bound is the right one after all.
"""
import numpy as np, sys, time
from zeta23_prime import prime_powers
from zeta23_o1_fast import split_fast

def P(*a): print(*a); sys.stdout.flush()

P(__doc__.split("STATED NULL")[0].strip()[:0] if False else
  "ATTEMPT 024 -- sign of O_1 for lambda <= 1 (the operative regime).\n")

LAMS = [0.50, 0.60, 0.70, 0.80, 0.90, 0.95, 1.00]
GRID = [(300.0, 0.02), (600.0, 0.02), (600.0, 0.05), (1000.0, 0.02),
        (1500.0, 0.02), (2000.0, 0.02), (600.0, 0.10)]

P(f"  {'T':>6}{'eta':>6}{'lam':>6}{'L':>8}{'L/l1':>7}{'X':>8}{'d':>6}"
  f"{'D/L^2':>12}{'O1/L^2':>12}{'O1/D':>10}{'sign':>6}")
allneg = True
rows = []
for T, ETA in GRID:
    l = np.log(T/(2*np.pi)); l1 = l + 2*np.log(2) - 1
    for lam in LAMS:
        L = lam*l; w = ETA*L/2
        if ETA*L > 2*np.log(2):
            P(f"  {T:>6.0f}{ETA:>6.2f}{lam:>6.2f}   SKIP eta*L={ETA*L:.3f} > 2log2"); continue
        X = np.exp(L)
        lamv, u = prime_powers(X)
        t0 = time.time()
        d, sP2, D, O1, O2 = split_fast(T, L, w, lamv, u)
        s = "NEG" if O1 < 0 else ("POS" if O1 > 0 else "0")
        if O1 >= 0: allneg = False
        P(f"  {T:>6.0f}{ETA:>6.2f}{lam:>6.2f}{L:>8.3f}{L/l1:>7.3f}{X:>8.0f}{d:>6d}"
          f"{D/L**2:>12.3f}{O1/L**2:>12.5f}{O1/D:>10.5f}{s:>6}   [{time.time()-t0:.0f}s]")
        rows.append((T, ETA, lam, L/l1, D, O1))

P(f"\n  ALL NEGATIVE over the sub-wall grid: {allneg}")
neg = [r for r in rows if r[5] < 0]
P(f"  {len(neg)}/{len(rows)} negative; max O1/D = {max(r[5]/r[4] for r in rows):+.6f}"
  f"; min O1/D = {min(r[5]/r[4] for r in rows):+.6f}")

P("\n  MONOTONICITY IN lambda (does |O1|/D grow smoothly, as a common mode would?)")
for T, ETA in GRID[:4]:
    sub = [r for r in rows if r[0] == T and r[1] == ETA]
    if len(sub) < 3: continue
    P(f"    T={T:.0f} eta={ETA}: " + "  ".join(f"{r[2]:.2f}:{r[5]/r[4]:+.5f}" for r in sub))

P("\n  READING.  If O_1 <= 0 throughout the operative regime, Prop. 5.6's two-sided bound can")
P("  be replaced by a one-sided one at no cost in hypotheses -- the question is then whether")
P("  the sign is PROVABLE, which this measurement cannot settle, only motivate or kill.")
