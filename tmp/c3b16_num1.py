#!/usr/bin/env python3
"""
C3 batch 16 -- numerical block 1.  MINORANT PRE-TEST WITH EXPLICIT REJECTION GATES.

Nothing is formalised until it passes here.  Every candidate is carried all the way to the
ASSEMBLED integral lower bound and rejected if that assembly is nonpositive -- being a true
pointwise inequality is NOT sufficient.

  G0  REJECTION GATE: cos z >= 2 exp(-beta z^2) - 2
  G1  cos z >= exp(-beta z^2) on a strictly bounded phase interval: optimal (beta, z*)
  G2  piecewise Gaussian / linear envelopes
  G3  SIGNED-ANNULUS (cosine-lobe) decomposition -- uses the tail's CANCELLATION, not its mass
  M1  the annulus lower bound  Qwin a >= 2 c^2 (Tail c - Tail a)
  M2  Tail 0 = mass/2, and an explicit c with Tail c > mass/4
  RE  reach of every surviving criterion, against batch 15's 6.638679
"""
import numpy as np
np.seterr(all='ignore')

def simp_w(n):
    w = np.ones(n+1); w[1:-1:2] = 4.0; w[2:-1:2] = 2.0
    return w
def simp(y, h): return (h/3.0)*np.dot(simp_w(len(y)-1), y)

NN = np.arange(1, 15, dtype=np.float64)
def Phi(t):
    t = np.abs(np.asarray(t, dtype=np.float64))
    e2 = np.exp(2*t); out = np.zeros_like(t)
    for n in NN:
        expo = -np.pi*n*n*e2
        term = (2*np.pi**2*n**4*np.exp(4.5*t) - 3*np.pi*n**2*np.exp(2.5*t))
        out += np.where(expo > -700.0, term*np.exp(np.maximum(expo, -700.0)), 0.0)
    return 4*out

PL = 6.6; NPp = 26400
pg = np.linspace(-PL, PL, NPp+1); hp = 2*PL/NPp; wp = simp_w(NPp)
VMAX = 3.0; NVv = 24000
vg = np.linspace(0.0, VMAX, NVv+1); hv = VMAX/NVv
Rp = np.array([(hp/3.0)*np.dot(wp, pg**2*Phi(v+pg)*Phi(v-pg)) for v in vg])
def cum(w8):
    y = w8*Rp; c = np.zeros(NVv+1)
    for k in range(2, NVv+1, 2):
        c[k] = c[k-2] + (hv/3.0)*(y[k-2]+4*y[k-1]+y[k])
    c[1::2] = 0.5*(c[0:-1:2]+c[2::2]); return c
M0c, M2c = cum(np.ones_like(vg)), cum(vg**2)
S = M0c[-1]; MASS = 2*S
def idx(a): return int(round(min(max(a,0.0),VMAX)/hv))
def Qwin(a): return 2*M2c[idx(a)]
def Tail(a): return S - M0c[idx(a)]
def Rfun(v):
    return np.interp(np.minimum(np.abs(np.asarray(v,dtype=float)), VMAX), vg, Rp)

print("="*78); print("SETUP"); print("="*78)
print(f"  mass = cosMom R 0 = {MASS:.14e},   mass/4 = {MASS/4:.14e}")
print(f"  R decreasing on [0,inf)? {bool(np.all(np.diff(Rp) <= 1e-18))}")

# ------------------------------------------------------------------ G0
print(); print("="*78)
print("G0 -- REJECTION GATE:  cos z >= 2 exp(-beta z^2) - 2")
print("="*78)
zz = np.linspace(-40, 40, 400001)
for beta in [0.25, 0.5, 1.0, 2.0]:
    d = np.cos(zz) - (2*np.exp(-beta*zz**2) - 2)
    print(f"    beta={beta:>4}: min(cos - minorant) = {d.min():.6e}"
          f"  {'TRUE pointwise' if d.min() >= -1e-12 else 'FALSE pointwise'}")
print()
print("  Now the ASSEMBLED bound, which is what matters:")
print("    int_{-a}^{a} R cos(2xv) dv >= 2 int_{-a}^{a} R e^{-beta(2xv)^2} dv - 2 int_{-a}^{a} R")
print("  and with the window tail, the criterion left side is")
print("    K(a,x) = 2 G(a,x) - 2 W(a) - 2 Tail(a),   W(a) = int_{-a}^{a} R, G <= W.")
print("  Since G(a,x) <= W(a) ALWAYS, K <= -2 Tail(a) <= 0 for every a and x.")
print(f"{'a':>7} {'x':>7} {'2G - 2W':>16} {'-2 Tail':>14} {'K':>16} {'K>0?':>6}")
for a in [0.2, 0.5, 1.0]:
    for x in [0.0, 1.0, 3.0]:
        k = idx(a); k -= k % 2
        W = 2*simp(Rp[:k+1], hv)
        G = 2*simp(Rp[:k+1]*np.exp(-1.0*(2*x*vg[:k+1])**2), hv)
        K = 2*G - 2*W - 2*Tail(a)
        print(f"{a:>7.2f} {x:>7.2f} {2*G-2*W:>16.6e} {-2*Tail(a):>14.6e} {K:>16.6e} {str(K>0):>6}")
print("  VERDICT: the assembly is NONPOSITIVE at every (a,x), and identically 0 in the")
print("  central part at x = 0 where the truth is W(a) > 0.  The minorant is TRUE but")
print("  USELESS: it discards the entire mass.  **REJECTED, not formalised.**")

# ------------------------------------------------------------------ G1
print(); print("="*78)
print("G1 -- cos z >= exp(-beta z^2) on |z| <= z*: optimal (beta, z*)")
print("="*78)
print("  Near 0: cos z - e^{-beta z^2} = (beta - 1/2) z^2 + (1/24 - beta^2/2) z^4 + ...")
print("  so beta > 1/2 is NECESSARY.  For large z the inequality dies once cos z < 0,")
print("  so z* <= pi/2 always.  Measured z*(beta) = sup{Z : cos z >= e^{-beta z^2} on [0,Z]}:")
zs = np.linspace(0, np.pi/2, 200001)
print(f"{'beta':>8} {'z*(beta)':>12} {'z*/(pi/2)':>12}")
best = None
for beta in [0.51, 0.55, 0.6, 0.75, 1.0, 1.5, 2.0, 4.0, 8.0]:
    d = np.cos(zs) - np.exp(-beta*zs**2)
    bad = np.where(d < -1e-15)[0]
    zstar = zs[bad[0]-1] if len(bad) else np.pi/2
    print(f"{beta:>8.2f} {zstar:>12.8f} {zstar/(np.pi/2):>12.8f}")
print("  READING: z* increases with beta toward pi/2, but a larger beta makes the Gaussian")
print("  decay faster, so the assembled bound is a genuine trade-off; optimised in RE below.")

# ------------------------------------------------------------------ G3
print(); print("="*78)
print("G3 -- SIGNED-ANNULUS (cosine-lobe) decomposition")
print("="*78)
print("  Split [0,inf) at v_k = (2k+1) pi/(4x): cos(2xv) >= 0 on [0,v_0], <= 0 on [v_0,v_1], ...")
print("  With J_k = int_{lobe k} R |cos(2xv)| dv, cosMom R (2x) = 2 (J_0 - J_1 + J_2 - ...).")
print("  If R is DECREASING then (J_k) is decreasing and the alternating sum >= J_0 - J_1.")
print("  This uses the tail's CANCELLATION, not its mass -- the ingredient batches 14/15")
print("  identified as missing.  Structural hypothesis 'R decreasing' falsification-tested above.")
def lobeJ(x, k):
    if x <= 0: return None
    lo = 0.0 if k == 0 else (2*k-1)*np.pi/(4*x)
    hi = (2*k+1)*np.pi/(4*x)
    if lo >= VMAX: return 0.0
    hi = min(hi, VMAX)
    n = 4000
    u = np.linspace(lo, hi, n+1)
    return simp(Rfun(u)*np.abs(np.cos(2*x*u)), (hi-lo)/n)
print(f"{'x':>7} {'J0':>15} {'J1':>15} {'J2':>15} {'2(J0-J1)':>16} {'true cosMom':>16} {'>0?':>5}")
vfull = np.concatenate([-vg[:0:-1], vg]); Rfull = np.concatenate([Rp[:0:-1], Rp])
def Rhat(xi): return simp(Rfull*np.cos(xi*vfull), hv)
for x in [0.5, 1.0, 2.0, 4.0, 6.0, 8.0, 12.0, 20.0]:
    J0, J1, J2 = lobeJ(x,0), lobeJ(x,1), lobeJ(x,2)
    lb = 2*(J0-J1)
    print(f"{x:>7.2f} {J0:>15.6e} {J1:>15.6e} {J2:>15.6e} {lb:>16.6e} {Rhat(2*x):>16.6e} {str(lb>0):>5}")
def reach_lobe():
    lo, hi = 0.0, 60.0
    for _ in range(50):
        m = (lo+hi)/2
        if 2*(lobeJ(m,0)-lobeJ(m,1)) > 0: lo = m
        else: hi = m
    return lo
print(f"  REACH of the two-lobe bound: |x| <= {reach_lobe():.6f}")
print("  (batch 15's window criterion reached 6.638679)")

# ------------------------------------------------------------------ M1 / M2
print(); print("="*78)
print("M1 / M2 -- the ANNULUS lower bound for Qwin, and the explicit c")
print("="*78)
print("  CLAIM to pre-test:  Qwin a >= 2 c^2 (Tail c - Tail a)  for 0 <= c <= a")
print("  (on c <= |v| < a one has v^2 >= c^2, and that annulus carries 2(Tail c - Tail a)).")
print(f"{'c':>7} {'a':>7} {'Qwin a':>16} {'2c^2(Tc-Ta)':>16} {'holds?':>7}")
bad = 0
for c in [0.05, 0.1, 0.2, 0.3]:
    for a in [0.3, 0.5, 1.0]:
        if c > a: continue
        lhs = Qwin(a); rhs = 2*c*c*(Tail(c)-Tail(a))
        if rhs > lhs + 1e-15: bad += 1
        print(f"{c:>7.2f} {a:>7.2f} {lhs:>16.8e} {rhs:>16.8e} {str(rhs<=lhs+1e-15):>7}")
print(f"  violations: {bad} (must be 0)")
print()
print(f"  Tail(0) = {Tail(0.0):.14e}   mass/2 = {MASS/2:.14e}"
      f"   reldiff {abs(Tail(0.0)-MASS/2)/(MASS/2):.2e}")
print("  explicit c with Tail c > mass/4 (this is the ONE numeric fact the exclusion needs):")
print(f"{'c':>8} {'Tail c':>16} {'mass/4':>16} {'Tail c > mass/4':>17}")
for c in [0.02, 0.05, 0.08, 0.10, 0.12, 0.15]:
    print(f"{c:>8.2f} {Tail(c):>16.8e} {MASS/4:>16.8e} {str(Tail(c) > MASS/4):>17}")
cstar = None
for c in np.arange(0.005, 0.3, 0.005):
    if Tail(c) > MASS/4: cstar = c
print(f"  largest tested c with Tail c > mass/4: {cstar:.3f}")
if cstar:
    lb = 2*cstar**2*(Tail(cstar) - MASS/4)
    print(f"  => uniform lower bound  Qwin a >= 2 c^2 (Tail c - mass/4) = {lb:.8e}")
    print(f"     for every admissible a (4 Tail a <= mass, hence Tail a <= mass/4, hence a >= c)")
    print(f"  => GLOBAL cap  x^2 <= mass/(2 * {lb:.6e}) = {MASS/(2*lb):.6e},"
          f"  i.e. |x| <= {np.sqrt(MASS/(2*lb)):.6f}")
    print("     This is the missing adaptive-window exclusion, modulo that one numeric fact.")

# ------------------------------------------------------------------ RE
print(); print("="*78)
print("RE -- REACH of every surviving criterion")
print("="*78)
agrid = np.arange(0.01, 1.5001, 0.0025)
def K_quad(a, x): return 2*Qwin(a)*0 + (MASS - 2*Tail(a)) - 2*x*x*Qwin(a) - 2*Tail(a)
def K_gauss(a, x, beta, zstar):
    if 2*abs(x)*a > zstar: return -1e9
    k = idx(a); k -= k % 2
    G = 2*simp(Rp[:k+1]*np.exp(-beta*(2*x*vg[:k+1])**2), hv)
    return G - 2*Tail(a)
def reach(K, **kw):
    lo, hi = 0.0, 60.0
    for _ in range(45):
        m = (lo+hi)/2
        if max(K(a, m, **kw) for a in agrid) > 0: lo = m
        else: hi = m
    return lo
print(f"  quadratic window (batch 15):        |x| <= {reach(K_quad):.6f}")
for beta, zst in [(0.75, None), (1.0, None), (2.0, None), (4.0, None)]:
    d = np.cos(zs) - np.exp(-beta*zs**2)
    bad2 = np.where(d < -1e-15)[0]
    zstar = zs[bad2[0]-1] if len(bad2) else np.pi/2
    print(f"  Gaussian window beta={beta:<4} z*={zstar:.5f}: |x| <= "
          f"{reach(K_gauss, beta=beta, zstar=zstar):.6f}")
print(f"  two-lobe signed annulus:            |x| <= {reach_lobe():.6f}")
print("="*78)
