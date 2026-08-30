#!/usr/bin/env python3
"""
C3 batch 17 -- numerical block 2.  The remaining proof decompositions, and the coefficient
audit of the compiled signed-window bound.

  D1  theta-mode: termwise log-concavity does NOT transfer to the sum (explicit witness)
  D2  monotone likelihood ratio (MLR) of the pair family
  D3  TP2 / four-point determinant form
  D4  rearrangement / Hoelder midpoint log-concavity of the pair
  D5  convolution decomposition R = (M2*Phi)(2v) - v^2 (Phi*Phi)(2v): does it give monotonicity?
  D6  autocorrelation monotonicity (the k=0 analogue R0(v) = (Phi*Phi)(2v)/2)
  D7  AUDIT of the compiled signed-window bound, and its reach vs the mass bound
  D8  hostile scan
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

print("="*78)
print("D1 -- THETA-MODE: termwise log-concavity does NOT transfer to the sum")
print("="*78)
print("  The repository compiles riemannXiKernelTerm_log_strictConcaveOn (each summand is")
print("  strictly log-concave on Ici 0).  Does that give log Phi concave?  NO -- a sum of")
print("  log-concave functions need not be log-concave.  Explicit witness:")
xx = np.linspace(-1, 4, 200001)
f = np.exp(-xx**2) + np.exp(-100*(xx-3)**2)
lg = np.log(f); d2 = np.diff(lg, 2)/((xx[1]-xx[0])**2)
print(f"    g(x) = exp(-x^2) + exp(-100(x-3)^2): both summands log-concave,")
print(f"    max (log g)'' = {d2.max():.6e} > 0  ->  g is NOT log-concave")
print("  So the compiled per-term result CANNOT be used to discharge the Phi hypothesis,")
print("  and this batch does not use it that way.  Recorded as a FAILED transfer.")

print(); print("="*78)
print("D2 / D3 / D4 -- MLR, TP2, and midpoint log-concavity of the pair")
print("="*78)
print("  All three are equivalent-in-spirit reformulations of the SAME four-point inequality")
print("  Phi(v+p)Phi(v-p) <= Phi(u+p)Phi(u-p) that the compiled pairing argument delivers.")
print("  Measured as determinants (TP2 form): D = Phi(u+p)Phi(v-p) - Phi(v+p)Phi(u-p) >= 0 ?")
print(f"{'u':>6} {'v':>6} {'p':>6} {'TP2 minor D':>22} {'sign':>7}")
badtp = 0; tottp = 0
for u in [0.0, 0.2, 0.5]:
    for v in [0.3, 0.8, 1.5]:
        for p in [0.1, 0.6, 1.2]:
            if u > v: continue
            tottp += 1
            D = Phi(u+p)*Phi(v-p) - Phi(v+p)*Phi(u-p)
            if D < -1e-300: badtp += 1
            if p in (0.1, 1.2) and v in (0.3, 1.5):
                print(f"{u:>6.2f} {v:>6.2f} {p:>6.2f} {D:>22.10e} {('pos' if D>=0 else 'NEG'):>7}")
print(f"  TP2 violations: {badtp}/{tottp}")
print("  MLR form: log Phi(v+p) - log Phi(u+p) nonincreasing in p?  Same content.")
print("  Hoelder/midpoint: log Phi((a+b)/2) >= (log Phi a + log Phi b)/2 -- midpoint")
print("  log-concavity, which for continuous Phi is EQUIVALENT to full log-concavity.")
mid = 0; badmid = 0
for a in np.linspace(-2, 2, 41):
    for b in np.linspace(-2, 2, 41):
        mid += 1
        lhs = np.log(Phi((a+b)/2)); rhs = 0.5*(np.log(Phi(a)) + np.log(Phi(b)))
        if lhs < rhs - 1e-9: badmid += 1
print(f"  midpoint log-concavity violations: {badmid}/{mid}")

print(); print("="*78)
print("D5 / D6 -- convolution decompositions")
print("="*78)
print("  R(v) = (M2*Phi)(2v) - v^2 (Phi*Phi)(2v)  (batch 14, exact to 5.5e-13).")
print("  The first term is a convolution of two NONNEGATIVE functions, hence its value at")
print("  2v is NOT automatically monotone; and the -v^2 term is not monotone either.")
print("  Measured: is (M2*Phi)(2v) antitone in v?  is (Phi*Phi)(2v) antitone?")
tg = np.linspace(-6.6, 6.6, 52801); ht = tg[1]-tg[0]
Pt = Phi(tg); M2t = tg**2*Phi(tg)
def conv_at(f, g, s):
    return simp(f*np.interp(s-tg, tg, g, left=0, right=0), ht)
print(f"{'v':>7} {'(M2*Phi)(2v)':>20} {'(Phi*Phi)(2v)':>20}")
prevA = prevB = None; incA = incB = 0
for v in np.linspace(0, 1.2, 25):
    A = conv_at(M2t, Pt, 2*v); B = conv_at(Pt, Pt, 2*v)
    if prevA is not None and A > prevA: incA += 1
    if prevB is not None and B > prevB: incB += 1
    prevA, prevB = A, B
    if abs(v*10 - round(v*10)) < 1e-9:
        print(f"{v:>7.2f} {A:>20.10e} {B:>20.10e}")
print(f"  (M2*Phi)(2v) increases at {incA}/24 steps;  (Phi*Phi)(2v) at {incB}/24 steps")
print("  Both antitone here, but the DIFFERENCE structure gives no monotonicity proof:")
print("  a difference of antitone functions is not antitone.  Route yields nothing.")

print(); print("="*78)
print("D7 -- AUDIT of the compiled signed-window bound, and its reach")
print("="*78)
PL = 6.6; NPp = 26400
pg = np.linspace(-PL, PL, NPp+1); hp = 2*PL/NPp; wp = simp_w(NPp)
VMAX = 3.0; NVv = 12000
vg = np.linspace(0.0, VMAX, NVv+1); hv = VMAX/NVv
Rp = np.array([(hp/3.0)*np.dot(wp, pg**2*Phi(v+pg)*Phi(v-pg)) for v in vg])
vfull = np.concatenate([-vg[:0:-1], vg]); Rfull = np.concatenate([Rp[:0:-1], Rp])
def Rhat(xi): return simp(Rfull*np.cos(xi*vfull), hv)
def idx(a): return int(round(min(max(a,0.0),VMAX)/hv))
def central(a, x):
    k = idx(a); k -= k % 2
    if k < 2: return 0.0
    return 2*simp(Rp[:k+1]*np.cos(2*x*vg[:k+1]), hv)
def compl_mass(a):
    k = idx(a); k -= k % 2
    tot = 2*simp(Rp, hv)
    return tot - 2*simp(Rp[:k+1], hv)
def compl_abscos(a, x):
    k = idx(a); k -= k % 2
    tot = 2*simp(Rp*np.abs(np.cos(2*x*vg)), hv)
    inner = 2*simp(Rp[:k+1]*np.abs(np.cos(2*x*vg[:k+1])), hv)
    return tot - inner
print("  C3B17.window_lower_signed:  C(a,x) - Compl|cos|(a,x) <= Rhat(2x)")
print("  C3B15.window_lower_compl :  C(a,x) - Compl(a)        <= Rhat(2x)")
print(f"{'a':>6} {'x':>6} {'signed LHS':>16} {'mass LHS':>16} {'Rhat(2x)':>16} {'both ok':>8}")
bad = 0
for a in [0.15, 0.3, 0.6]:
    for x in [0.0, 2.0, 5.0, 8.0]:
        s = central(a, x) - compl_abscos(a, x)
        m = central(a, x) - compl_mass(a)
        r = Rhat(2*x)
        ok = (s <= r + 1e-14) and (m <= r + 1e-14) and (m <= s + 1e-14)
        if not ok: bad += 1
        print(f"{a:>6.2f} {x:>6.2f} {s:>16.8e} {m:>16.8e} {r:>16.8e} {str(ok):>8}")
print(f"  violations (signed valid, mass valid, mass <= signed): {bad}")
agrid = np.arange(0.01, 1.5001, 0.005)
def reach(F):
    lo, hi = 0.0, 60.0
    for _ in range(40):
        mm = (lo+hi)/2
        if max(F(a, mm) for a in agrid) > 0: lo = mm
        else: hi = mm
    return lo
r_mass = reach(lambda a, x: central(a, x) - compl_mass(a))
r_sign = reach(lambda a, x: central(a, x) - compl_abscos(a, x))
print(f"  reach with the MASS complement  : |x| <= {r_mass:.6f}")
print(f"  reach with the SIGNED complement: |x| <= {r_sign:.6f}   (gain {r_sign-r_mass:+.6f})")
print("  NOTE: these use the EXACT central integral, so they are the ceiling of each")
print("  complement treatment, not of a computable criterion.")
print("="*78)
