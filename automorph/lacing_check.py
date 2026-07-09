"""Lacing check (owner's rope image, 2026-07-03): points as clocks on E(R).

Claims verified on house curves (float group law, exact statements checked to fp):
  (1) INTERLACED: a generator on the egg alternates components -- parity(nP) = n*parity(P)
      mod 2 (the component map is a Z/2 homomorphism).  37a1, P=(0,0) on the egg.
  (2) CONTINUOUS: multiples of 2P (identity component) stay on one side and wind around.
  (3) TORSION = CLOSED LACING: 11a1's 5-torsion point closes in exactly 5 steps.
  (4) NON-TORSION = DENSE LACING (irrational clock): min return distance keeps shrinking,
      never zero -- and record close-returns arrive at increasing times (CF-like ladder).
Scope: finite verified instances; the general statements are elementary group theory
(component homomorphism) + elliptic log irrationality (torsion <=> rational angle).
"""
import math

def make_curve(a1, a2, a3, a4, a6):
    # group law on y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6 (floats)
    def neg(P):
        if P is None: return None
        x, y = P
        return (x, -y - a1 * x - a3)
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if abs(x1 - x2) < 1e-12:
            if abs(y1 + y2 + a1 * x2 + a3) < 1e-9:
                return None
            lam = (3 * x1 * x1 + 2 * a2 * x1 + a4 - a1 * y1) / (2 * y1 + a1 * x1 + a3)
        else:
            lam = (y2 - y1) / (x2 - x1)
        x3 = lam * lam + a1 * lam - a2 - x1 - x2
        y3 = lam * (x1 - x3) - y1 - a1 * x3 - a3
        return (x3, y3)
    return add, neg

# --- 37a1: y^2 + y = x^3 - x  (disc 37 > 0: egg + unbounded component) -----------
add37, _ = make_curve(0, 0, 1, -1, 0)
# component split: Y^2 = x^3 - x + 1/4 has roots e1 < e2 < e3; egg = x in [e1,e2]
import numpy as np
roots = sorted(np.roots([1, 0, -1, 0.25]).real)
e1, e2, e3 = roots
egg = lambda P: (P is not None) and (P[0] <= e2 + 1e-9)

P = (0.0, 0.0)
print("(1)+(2) 37a1 lacing classes (e1,e2,e3 = %.4f, %.4f, %.4f):" % (e1, e2, e3))
Q = None
pattern_ok = True
for n in range(1, 41):
    Q = add37(Q, P)
    want_egg = (n % 2 == 1)          # P on egg, hom to Z/2 => parity alternates
    if egg(Q) != want_egg:
        pattern_ok = False
print("    P=(0,0) on egg: %s;  40 multiples alternate egg/unbounded: %s  [INTERLACED]"
      % (egg(P), "PASS" if pattern_ok else "FAIL"))
P2 = add37(P, P)
Q = None
cont_ok = True
for n in range(1, 41):
    Q = add37(Q, P2)
    if egg(Q):
        cont_ok = False
print("    2P=(%.4f,%.4f) on unbounded: 40 multiples all stay there: %s  [CONTINUOUS]"
      % (P2[0], P2[1], "PASS" if cont_ok else "FAIL"))

# --- (3) 11a1: y^2 + y = x^3 - x^2 - 10x - 20, T=(5,5) has order 5 ---------------
add11, _ = make_curve(0, -1, 1, -10, -20)
T = (5.0, 5.0)
Q = None
orbit = []
for n in range(1, 7):
    Q = add11(Q, T)
    orbit.append(Q)
closed = orbit[4] is None
print("(3) 11a1 torsion T=(5,5): 5T = O: %s  [CLOSED LACING, rational clock]"
      % ("PASS" if closed else "FAIL"))

# --- (4) 37a1 non-torsion: dense lacing, record returns --------------------------
# order-invariant angle on each component: atan2 around the component's own center
def angle(Pt):
    x, y = Pt
    Y = y + 0.5
    if x <= e2 + 1e-9:   # egg: center between e1,e2
        return math.atan2(Y, x - 0.5 * (e1 + e2))
    return math.atan2(Y, x - e3 - 1.0)  # unbounded: crude but order-consistent proxy

Q = None
pos = []
for n in range(1, 2001):
    Q = add37(Q, P)
    if not egg(Q):
        continue
    pos.append((n, angle(Q)))
base = pos[0][1]
records = []
best = 10.0
for n, a in pos[1:]:
    d = abs((a - base + math.pi) % (2 * math.pi) - math.pi)
    if d < best:
        best = d
        records.append((n, d))
print("(4) 37a1 non-torsion P: record close-returns to the start (egg angle):")
for n, d in records[:8]:
    print("      n=%5d   dist=%.6f" % (n, d))
print("    min never 0, records keep arriving -> dense lacing (irrational clock): %s"
      % ("PASS" if (len(records) >= 4 and records[-1][1] > 1e-9) else "FAIL"))
