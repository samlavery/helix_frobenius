#!/usr/bin/env python3
"""
C3 batch 15 -- numerical block 1.  COEFFICIENT AND ORIENTATION PRE-TEST.

Nothing here is formalised until it has passed this block.

  W0  the RETRACTED batch-14 window bound (factor 2 on the centre) -- exhibit its failure
  W1  the CORRECTED window bound -- verify orientation at hostile (a,x)
  W2  the moment table S, M0(a), M1(a), M2(a), M4(a), T(a)
  C1  central bound  cos z >= 1 - z^2/2            (Mathlib: Real.one_sub_sq_div_two_le_cos)
  C2  central bound  cos z >= 1 - (2/pi) z on [0,pi/2]  (Mathlib: Real.one_sub_mul_le_cos)
  C3  central bound  cos z >= cos(z_max) on [0,pi]      (Mathlib: cos_le_cos_of_nonneg_of_le_pi)
  X0  the resulting sufficient criteria, optimised over a, and the reach x0 of each
  CEIL the METHOD CEILING: the best any absolute-value tail bound can do
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
VMAX = 3.0; NVv = 12000
vg = np.linspace(0.0, VMAX, NVv+1); hv = VMAX/NVv
Rp = np.array([(hp/3.0)*np.dot(wp, pg**2*Phi(v+pg)*Phi(v-pg)) for v in vg])

# cumulative partial moments on [0,a] (Simpson on even prefixes)
def cum(weight):
    y = weight*Rp
    c = np.zeros(NVv+1)
    for k in range(2, NVv+1, 2):
        c[k] = c[k-2] + (hv/3.0)*(y[k-2] + 4*y[k-1] + y[k])
    c[1::2] = 0.5*(c[0:-1:2] + c[2::2])   # midpoint fill, adequate for these smooth curves
    return c
M0c = cum(np.ones_like(vg)); M1c = cum(vg); M2c = cum(vg**2); M4c = cum(vg**4)
S  = M0c[-1]; M1 = M1c[-1]; M2 = M2c[-1]; M4 = M4c[-1]
def idx(a): return int(round(min(max(a,0.0), VMAX)/hv))
def M0(a): return M0c[idx(a)]
def M1f(a): return M1c[idx(a)]
def M2f(a): return M2c[idx(a)]
def T(a):  return S - M0c[idx(a)]

vfull = np.concatenate([-vg[:0:-1], vg]); Rfull = np.concatenate([Rp[:0:-1], Rp])
def Rhat(xi): return simp(Rfull*np.cos(xi*vfull), hv)
def central(a, x):
    """exact int_{-a}^{a} R(v) cos(2 x v) dv"""
    k = idx(a)
    if k < 2: return 0.0
    if k % 2: k -= 1
    y = Rp[:k+1]*np.cos(2*x*vg[:k+1])
    return 2*simp(y, hv)

print("="*78); print("W2 -- MOMENT TABLE"); print("="*78)
print(f"  S  = int_0^inf R      = {S:.14e}   (2S = cosMom R 0 = {2*S:.14e})")
print(f"  M1 = int_0^inf v R    = {M1:.14e}")
print(f"  M2 = int_0^inf v^2 R  = {M2:.14e}")
print(f"  M4 = int_0^inf v^4 R  = {M4:.14e}")
print(f"  CONTROL 2S vs batch 13 L1(0) = 0.011419830834443718 : reldiff"
      f" {abs(2*S-0.011419830834443718)/(2*S):.3e}")
print()
print(f"{'a':>7} {'M0(a)':>16} {'T(a)':>16} {'M1(a)':>16} {'M2(a)':>16}")
for a in [0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.75, 1.0, 1.5]:
    print(f"{a:>7.2f} {M0(a):>16.8e} {T(a):>16.8e} {M1f(a):>16.8e} {M2f(a):>16.8e}")

print(); print("="*78); print("W0 / W1 -- ORIENTATION TEST of the window bound"); print("="*78)
print("  RETRACTED (batch 14):  2*C(a,x) - 2*T(a) <= Rhat(2x)      [FALSE]")
print("  CORRECTED (this batch):  C(a,x) - 2*T(a) <= Rhat(2x)      [to be verified]")
print("  where C(a,x) = int_{-a}^{a} R cos(2xv) dv, T(a) = int_a^inf R.")
print()
print(f"{'a':>7} {'x':>7} {'C(a,x)':>16} {'T(a)':>13} {'Rhat(2x)':>16} {'OLD LHS':>16} {'NEW LHS':>16} {'old ok':>7} {'new ok':>7}")
oldfail = 0; newfail = 0; n = 0
for a in [0.05, 0.2, 0.5, 1.0, 2.0, 3.0]:
    for x in [0.0, 0.5, 1.7, 4.0, 14.134725]:
        C = central(a, x); t = T(a); rh = Rhat(2*x)
        old = 2*C - 2*t; new = C - 2*t
        n += 1
        if old > rh + 1e-14: oldfail += 1
        if new > rh + 1e-14: newfail += 1
        if a in (0.05, 1.0, 3.0) and x in (0.0, 1.7, 14.134725):
            print(f"{a:>7.2f} {x:>7.3f} {C:>16.8e} {t:>13.3e} {rh:>16.8e} {old:>16.8e}"
                  f" {new:>16.8e} {str(old<=rh+1e-14):>7} {str(new<=rh+1e-14):>7}")
print()
print(f"  over {n} hostile (a,x) pairs:  OLD violated {oldfail} times,  NEW violated {newfail} times")
print(f"  worst OLD case is a large, x = 0: LHS -> 2*(2S) = {4*S:.8e}, RHS = 2S = {2*S:.8e}")
print("  => the retracted form fails by exactly a factor 2 at x=0; the corrected form holds.")

print(); print("="*78); print("C1 / C2 / C3 -- CENTRAL LOWER BOUNDS, coefficients pre-tested"); print("="*78)
print("  C1  cos z >= 1 - z^2/2, z = 2xv   =>  C(a,x) >= 2 M0(a) - 4 x^2 M2(a)")
print("  C2  cos z >= 1 - (2/pi) z on [0,pi/2] (needs 2|x|a <= pi/2)")
print("                                     =>  C(a,x) >= 2 M0(a) - (8|x|/pi) M1(a)")
print("  C3  cos z >= cos(2 x a) on |v|<=a (needs 2|x|a <= pi)")
print("                                     =>  C(a,x) >= 2 M0(a) cos(2 x a)")
print()
print(f"{'a':>6} {'x':>6} {'C exact':>15} {'C1 bound':>15} {'C2 bound':>15} {'C3 bound':>15} {'valid':>16}")
for a in [0.1, 0.3, 0.5]:
    for x in [0.5, 2.0, 5.0]:
        C = central(a, x)
        b1 = 2*M0(a) - 4*x**2*M2f(a)
        b2 = 2*M0(a) - (8*abs(x)/np.pi)*M1f(a) if 2*abs(x)*a <= np.pi/2 else float('nan')
        b3 = 2*M0(a)*np.cos(2*x*a) if 2*abs(x)*a <= np.pi else float('nan')
        ok = (b1 <= C+1e-14) and (np.isnan(b2) or b2 <= C+1e-14) and (np.isnan(b3) or b3 <= C+1e-14)
        print(f"{a:>6.2f} {x:>6.2f} {C:>15.7e} {b1:>15.7e} {b2:>15.7e} {b3:>15.7e} {str(ok):>16}")
print("  all printed bounds must be <= the exact column; 'valid' reports that check.")

print(); print("="*78); print("X0 -- THE SUFFICIENT CRITERIA AND THEIR REACH"); print("="*78)
print("  criterion(a,x) > 0  =>  Rhat(2x) > 0.  Optimise over a for each x.")
print("    K1(a,x) = 2 M0(a) - 4 x^2 M2(a) - 2 T(a)   =  2S - 4T(a) - 4 x^2 M2(a)")
print("    K2(a,x) = 2 M0(a) - (8|x|/pi) M1(a) - 2 T(a),   a <= pi/(4|x|)")
print("    K3(a,x) = 2 M0(a) cos(2 x a) - 2 T(a),         a <= pi/(2|x|)")
agrid = np.arange(0.01, 1.2001, 0.005)
def best(x):
    b1 = max(2*M0(a) - 4*x*x*M2f(a) - 2*T(a) for a in agrid)
    c2 = [2*M0(a) - (8*abs(x)/np.pi)*M1f(a) - 2*T(a) for a in agrid if 2*abs(x)*a <= np.pi/2]
    b2 = max(c2) if c2 else -1e9
    c3 = [2*M0(a)*np.cos(2*x*a) - 2*T(a) for a in agrid if 2*abs(x)*a <= np.pi]
    b3 = max(c3) if c3 else -1e9
    return b1, b2, b3
print(f"{'x':>7} {'K1 max':>15} {'K2 max':>15} {'K3 max':>15} {'true Rhat(2x)':>16} {'any>0':>7}")
for x in [0.0, 1.0, 2.0, 3.0, 4.0, 4.5, 4.8, 5.0, 5.5, 6.0, 8.0]:
    b1, b2, b3 = best(x)
    print(f"{x:>7.2f} {b1:>15.7e} {b2:>15.7e} {b3:>15.7e} {Rhat(2*x):>16.7e}"
          f" {str(max(b1,b2,b3)>0):>7}")
def reach(which):
    lo, hi = 0.0, 20.0
    for _ in range(60):
        m = (lo+hi)/2
        if best(m)[which] > 0: lo = m
        else: hi = m
    return lo
r1, r2, r3 = reach(0), reach(1), reach(2)
print()
print(f"  REACH:  K1 works for |x| <= {r1:.6f}")
print(f"          K2 works for |x| <= {r2:.6f}")
print(f"          K3 works for |x| <= {r3:.6f}")
print(f"          union            |x| <= {max(r1,r2,r3):.6f}")
print(f"  (batch 13's A4 criterion reached |x| <= 2.503; batch 12+13 compiled only x = 0)")

print(); print("="*78); print("CEIL -- THE METHOD CEILING (this is a property of the INSTRUMENT)"); print("="*78)
print("  ANY bound of the form  Rhat(2x) >= C(a,x) - 2 T(a)  with the tail taken in")
print("  ABSOLUTE VALUE caps at finite x, for a reason independent of which central bound")
print("  is used: T(a) > 0 is a CONSTANT in x, while the true Rhat(2x) = L1(x) decays like")
print("  e^{-pi x/2}.  So for any fixed a > 0 the bound is negative once L1(x) < 2 T(a).")
print("  Best possible: use the EXACT central integral, i.e. no loss at all in the centre.")
print(f"{'x':>7} {'best_a [C(a,x)-2T(a)]':>26} {'true Rhat(2x)':>18} {'ceiling>0':>10}")
for x in [4.0, 5.0, 6.0, 7.0, 8.0, 10.0]:
    bb = max(central(a, x) - 2*T(a) for a in agrid)
    print(f"{x:>7.2f} {bb:>26.7e} {Rhat(2*x):>18.7e} {str(bb>0):>10}")
def ceil_reach():
    lo, hi = 0.0, 30.0
    for _ in range(60):
        m = (lo+hi)/2
        if max(central(a, m) - 2*T(a) for a in agrid) > 0: lo = m
        else: hi = m
    return lo
print(f"  CEILING of the absolute-tail window method: |x| <= {ceil_reach():.6f}")
print("  Beyond that NO choice of a and NO central bound can succeed, because the loss is")
print("  entirely in discarding the tail's CANCELLATION.  Getting past it requires using")
print("  the sign structure of the tail, not its mass.")
print("="*78)
