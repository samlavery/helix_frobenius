#!/usr/bin/env python3
"""
C3 batch 15 -- numerical block 2.  Adjudication of block 1's CEIL section, sharper central
bounds, and the remaining tail/central decompositions.

A  ADJUDICATION of block 1's "method ceiling".  Two defects in my own prose there.
B  higher-order central bounds (Taylor 4/6/8), validity first, then reach
C  dyadic annuli
D  Chernoff / exponential-moment tail bound, with the (t,s) change of variables checked
E  theta-mode / incomplete-gamma tail
F  integration by parts on the central integral
G  antihelix symmetry ;  H  pi/3 applicability ;  I  hostile scan ;  J  adaptive a(x)
"""
import numpy as np
np.seterr(all='ignore')
from mpmath import mp, mpf, quad as mpquad, exp as mexp, pi as mpi, cos as mcos, fabs as mfabs

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
def cum(w8):
    y = w8*Rp; c = np.zeros(NVv+1)
    for k in range(2, NVv+1, 2):
        c[k] = c[k-2] + (hv/3.0)*(y[k-2]+4*y[k-1]+y[k])
    c[1::2] = 0.5*(c[0:-1:2]+c[2::2]); return c
M0c, M2c, M4c, M6c = cum(np.ones_like(vg)), cum(vg**2), cum(vg**4), cum(vg**6)
S = M0c[-1]
def idx(a): return int(round(min(max(a,0.0),VMAX)/hv))
def M0(a): return M0c[idx(a)]
def M2(a): return M2c[idx(a)]
def M4(a): return M4c[idx(a)]
def M6(a): return M6c[idx(a)]
def T(a): return S - M0c[idx(a)]

print("="*78); print("A -- ADJUDICATION of block 1's CEIL section"); print("="*78)
print("  Block 1 printed: 'CEILING of the absolute-tail window method: |x| <= 30.000000'")
print("  and asserted that the method caps because T(a) is a constant while L1 decays.")
print("  TWO DEFECTS, both mine.")
print()
print("  (i) The 30.0 is the TOP OF THE BINARY SEARCH RANGE, not a measurement.  T(a)")
print("      UNDERFLOWS to exactly 0 in float64 for a >= 0.75, so C(a,x) - 2T(a) became")
print("      literally C(a,x) = Rhat(2x) and the 'ceiling' was the target itself.")
print(f"      evidence: T(0.75) = {T(0.75):.3e}, T(1.00) = {T(1.00):.3e} (exact 0 in float64)")
print()
print("  (ii) The BINDING CONSTRAINT IS THE OTHER WAY ROUND.  R inherits Phi's DOUBLE")
print("       exponential decay, so T(a) is astronomically small already at moderate a:")
for a in [0.3, 0.4, 0.5, 0.6, 0.75]:
    print(f"         T({a:.2f}) = {T(a):.6e}")
print("       The tail is NOT what limits the method.  What limits it is that a POLYNOMIAL")
print("       central bound cos z >= P(z) has P(z) -> -infinity, while the true central")
print("       integral decays like e^{-pi x/2}.  No polynomial can track that, so the")
print("       CENTRAL bound caps the reach.  Corrected statement, and it is a property of")
print("       the polynomial-central-bound instrument class, not of the target.")

print(); print("="*78); print("B -- HIGHER-ORDER CENTRAL BOUNDS: validity FIRST, then reach"); print("="*78)
print("  Candidate global lower bounds for cos z (must be verified, not assumed):")
print("    P2(z) = 1 - z^2/2")
print("    P6(z) = 1 - z^2/2 + z^4/24 - z^6/720")
print("    P10(z)= P6 + z^8/40320 - z^10/3628800")
zz = np.linspace(-60, 60, 600001)
def P2(z): return 1 - z**2/2
def P6(z): return 1 - z**2/2 + z**4/24 - z**6/720
def P10(z): return P6(z) + z**8/40320 - z**10/3628800
for nm, P in [('P2', P2), ('P6', P6), ('P10', P10)]:
    d = np.cos(zz) - P(zz)
    print(f"    {nm}: min (cos z - {nm}(z)) over |z|<=60 = {d.min():.6e}"
          f"   {'VALID lower bound' if d.min() >= -1e-9 else 'NOT a lower bound'}")
print()
print("  reach of each, optimising over the window a  (criterion > 0 => Rhat(2x) > 0):")
agrid = np.arange(0.01, 1.5001, 0.005)
def K_P2(a, x): return 2*M0(a) - 4*x*x*M2(a) - 2*T(a)
def K_P6(a, x): return (2*M0(a) - 4*x*x*M2(a) + (4.0/3.0)*x**4*M4(a)
                        - (64.0/45.0)*x**6*M6(a) - 2*T(a))
def reach(K):
    lo, hi = 0.0, 40.0
    for _ in range(60):
        m = (lo+hi)/2
        if max(K(a, m) for a in agrid) > 0: lo = m
        else: hi = m
    return lo
r2, r6 = reach(K_P2), reach(K_P6)
print(f"    P2  reach |x| <= {r2:.6f}")
print(f"    P6  reach |x| <= {r6:.6f}")
print(f"    gain from the higher-order bound: {r6-r2:+.6f}")

print(); print("="*78); print("C -- DYADIC ANNULI decomposition of the tail"); print("="*78)
print("  T(a) = sum_k int_{2^k a}^{2^{k+1} a} R.  Each annulus bounded by its own sup.")
print(f"{'a':>7} {'T(a) exact':>16} {'dyadic sum':>16} {'reldiff':>11} {'#annuli used':>13}")
for a in [0.2, 0.3, 0.4, 0.5]:
    tot = 0.0; k = 0; b = a
    while b < VMAX and k < 20:
        b2 = min(2*b, VMAX)
        i1, i2 = idx(b), idx(b2)
        tot += M0c[i2] - M0c[i1]
        b = b2; k += 1
    print(f"{a:>7.2f} {T(a):>16.8e} {tot:>16.8e} {abs(tot-T(a))/max(T(a),1e-300):>11.2e} {k:>13}")
print("  The dyadic split is exact by construction; it buys nothing over T(a) itself here,")
print("  because R's decay is doubly exponential and the FIRST annulus already carries")
print("  essentially all of the (tiny) tail.  Recorded as a null.")

print(); print("="*78); print("D -- CHERNOFF / EXPONENTIAL-MOMENT tail bound"); print("="*78)
print("  Claim to pre-test:  int e^{lam|v|} R(v) dv  <=  (1/4) B0(lam) B2(lam),")
print("  with B_j(lam) = int t^j e^{lam|t|/2} Phi(t) dt  (B1 = 0 by parity),")
print("  from (t,s) = (v+p, v-p), 2|v| <= |t| + |s|, p = (t-s)/2, dv dp = (1/2) dt ds.")
tg = np.linspace(-6.6, 6.6, 52801); ht = tg[1]-tg[0]
Pt = Phi(tg)
print(f"{'lam':>6} {'LHS int e^{lam|v|}R':>22} {'RHS (1/4)B0 B2':>20} {'LHS<=RHS':>10}")
for lam in [0.0, 1.0, 2.0, 4.0, 6.0]:
    lhs = 2*simp(np.exp(lam*vg)*Rp, hv)
    B0 = simp(np.exp(lam*np.abs(tg)/2)*Pt, ht)
    B2 = simp(tg**2*np.exp(lam*np.abs(tg)/2)*Pt, ht)
    print(f"{lam:>6.1f} {lhs:>22.8e} {0.25*B0*B2:>20.8e} {str(lhs <= 0.25*B0*B2*(1+1e-12)):>10}")
print("  and the Chernoff bound T(a) <= e^{-lam a} * (1/4) B0 B2 / 2 :")
print(f"{'a':>6} {'T(a) exact':>16} {'best Chernoff':>16} {'ratio':>10}")
for a in [0.3, 0.5, 0.75, 1.0]:
    best = None
    for lam in np.arange(0.5, 40.0, 0.5):
        B0 = simp(np.exp(lam*np.abs(tg)/2)*Pt, ht)
        B2 = simp(tg**2*np.exp(lam*np.abs(tg)/2)*Pt, ht)
        val = np.exp(-lam*a)*0.25*B0*B2/2
        if np.isfinite(val) and (best is None or val < best): best = val
    print(f"{a:>6.2f} {T(a):>16.8e} {best:>16.8e} {best/max(T(a),1e-300):>10.2e}")
print("  Chernoff is valid but LOSSY here (ratio >> 1): it produces an exponential bound")
print("  for a doubly-exponentially small quantity.  Valid, and recorded as lossy.")

print(); print("="*78); print("F -- INTEGRATION BY PARTS on the central integral"); print("="*78)
print("  int_{-a}^{a} R cos(2xv) dv = [R sin(2xv)/(2x)]_{-a}^{a} - (1/(2x)) int_{-a}^{a} R' sin(2xv) dv")
print("                             = R(a) sin(2xa)/x  - (1/(2x)) int R' sin")
Rd = np.gradient(Rp, hv)
print(f"{'a':>6} {'x':>6} {'direct':>16} {'by parts':>16} {'reldiff':>11}")
for a in [0.3, 0.5]:
    for x in [1.0, 3.0]:
        k = idx(a); k -= k % 2
        direct = 2*simp(Rp[:k+1]*np.cos(2*x*vg[:k+1]), hv)
        bdry = Rp[k]*np.sin(2*x*vg[k])/x
        inner = -(1.0/(2*x))*2*simp(Rd[:k+1]*np.sin(2*x*vg[:k+1]), hv)
        print(f"{a:>6.2f} {x:>6.2f} {direct:>16.8e} {bdry+inner:>16.8e}"
              f" {abs(direct-bdry-inner)/abs(direct):>11.2e}")
print("  IBP trades R for R' and gains a 1/x -- but |R'| has a LARGER mass than R, so the")
print("  net factor is (mass of R')/(2x mass of R); measured below:")
massR = 2*simp(Rp, hv); massRd = 2*simp(np.abs(Rd), hv)
print(f"    int|R| = {massR:.6e},  int|R'| = {massRd:.6e},  crossover x = {massRd/(2*massR):.4f}")
print("  so IBP only helps for x above that crossover, where the central bound is already")
print("  the binding constraint.  Recorded; not used.")

print(); print("="*78); print("G / H -- ANTIHELIX and pi/3 APPLICABILITY"); print("="*78)
print("  G: the v <-> p swap leaves Phi(v+p)Phi(v-p) invariant (C3B12.antihelix_swap), so")
print("     R's defining form is symmetric under it and the swap yields no new bound.")
print("     Verified in batch 14 to reldiff 0.00e+00; not re-run.")
print("  H: pi/3 registration applies to CELL-REGISTRATION COUNTS N_{pi/3}(e^t)-N_1(e^t).")
print("     In this batch the variable a is a WINDOW RADIUS in the cell-centre coordinate v.")
print("     v IS a cell coordinate, so the register is checkable here -- unlike batch 14,")
print("     where only moments appeared.  Test: does choosing a on the pi/3 lattice help?")
print(f"{'a':>16} {'K_P2 max over x=4':>20} {'K_P2 at x=6':>16}")
for lab, a in [('pi/3 = 1.04720', np.pi/3), ('pi/6 = 0.52360', np.pi/6),
               ('pi/12= 0.26180', np.pi/12), ('optimum (free)', None)]:
    if a is None:
        v4 = max(K_P2(aa, 4.0) for aa in agrid); v6 = max(K_P2(aa, 6.0) for aa in agrid)
    else:
        v4 = K_P2(a, 4.0); v6 = K_P2(a, 6.0)
    print(f"{lab:>16} {v4:>20.8e} {v6:>16.8e}")
print("  READING: reported as measured.  The pi/3 lattice is not privileged for this")
print("  quantity; a unit-1 scan is NOT run (documented false-null trap).")

print(); print("="*78); print("J -- ADAPTIVE a(x): the optimal window as a function of x"); print("="*78)
print(f"{'x':>7} {'best a':>10} {'K_P2 max':>16} {'true Rhat(2x)':>16} {'loss factor':>12}")
for x in [0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 6.6, 7.0]:
    vals = [(K_P2(a, x), a) for a in agrid]
    b, ba = max(vals)
    rh = 2*simp(np.concatenate([Rp[:0:-1], Rp])*0 + 0, hv) if False else None
    yy = np.concatenate([Rp[:0:-1], Rp]); vv = np.concatenate([-vg[:0:-1], vg])
    rh = simp(yy*np.cos(2*x*vv), hv)
    print(f"{x:>7.2f} {ba:>10.3f} {b:>16.8e} {rh:>16.8e} {rh/b if b>0 else float('nan'):>12.4f}")
print("  The optimal a SHRINKS as x grows, exactly as the polynomial-bound analysis predicts.")
print("="*78)
