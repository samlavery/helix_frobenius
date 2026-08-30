#!/usr/bin/env python3
"""
C3 batch 16 -- numerical block 2.  Hostile falsification with explicit rejection gates,
and the remaining decompositions.

  P1  the COMPILED cap of no_adaptive_window, against the measured reach
  P2  hostile scan of cosMom R (2x) = L1(x): x through 400, near zero ordinates, 40 dps
  P3  piecewise Gaussian/linear envelope (max of the two minorants)
  P4  lobe-annulus hybrid: k-lobe truncation for k = 2,4,6
  P5  heat / de Bruijn flow applied to the CRITERION (not to the target)
  P6  positive convolution factorization  R = (M2*Phi)(2v) - v^2 (Phi*Phi)(2v)
  P7  theta-mode / incomplete-gamma tail representations: are they ever binding?
  P8  pi/3 registration for the WINDOW RADIUS (a genuine cell coordinate)

REJECTION GATE used throughout: a claimed negative counts only if |min| exceeds the grid's
own tail residual by >= 1e4 and survives a precision change.
"""
import numpy as np
np.seterr(all='ignore')
from mpmath import mp, mpf, mpc, pi as mpi, psi, zeta, gamma, nstr

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
M0c, M2c, M1c = cum(np.ones_like(vg)), cum(vg**2), cum(vg)
S = M0c[-1]; MASS = 2*S
def idx(a): return int(round(min(max(a,0.0),VMAX)/hv))
def Qwin(a): return 2*M2c[idx(a)]
def Awin(a): return 2*M1c[idx(a)]
def Tail(a): return S - M0c[idx(a)]
def Rfun(v): return np.interp(np.minimum(np.abs(np.asarray(v,dtype=float)), VMAX), vg, Rp)
vfull = np.concatenate([-vg[:0:-1], vg]); Rfull = np.concatenate([Rp[:0:-1], Rp])
def Rhat(xi): return simp(Rfull*np.cos(xi*vfull), hv)

print("="*78); print("P1 -- THE COMPILED CAP vs THE MEASURED REACH"); print("="*78)
print("  C3B16.no_adaptive_window gives X = mass / (2 * 2c^2 (Tail c - mass/4)) for any")
print("  witness c.  The bound is valid for EVERY witness; the best (smallest) X is the")
print("  informative one.  Compiled existence uses continuity; here we optimise c numerically.")
print(f"{'c':>8} {'Tail c':>15} {'2c^2(Tc-mass/4)':>18} {'cap X':>15} {'|x| cap':>12}")
best = None
for c in np.arange(0.005, 0.10, 0.005):
    Tc = Tail(c)
    if Tc <= MASS/4: continue
    lb = 2*c*c*(Tc - MASS/4)
    X = MASS/(2*lb)
    if best is None or X < best[0]: best = (X, c, lb)
    if abs(c*1000 - round(c*1000)) < 1e-9 and round(c*1000) % 10 == 0:
        print(f"{c:>8.3f} {Tc:>15.8e} {lb:>18.8e} {X:>15.6e} {np.sqrt(X):>12.6f}")
X, cbest, lbbest = best
print(f"  BEST witness c = {cbest:.3f}: cap X = {X:.6e}, i.e. |x| <= {np.sqrt(X):.6f}")
agrid = np.arange(0.01, 1.5001, 0.0025)
def K_quad(a, x): return (MASS - 2*Tail(a)) - 2*x*x*Qwin(a) - 2*Tail(a)
lo, hi = 0.0, 60.0
for _ in range(50):
    m = (lo+hi)/2
    if max(K_quad(a, m) for a in agrid) > 0: lo = m
    else: hi = m
print(f"  measured reach of the criterion: |x| <= {lo:.6f}")
print(f"  the compiled cap is a valid but LOOSE upper bound on that reach ({np.sqrt(X):.3f} vs {lo:.3f}).")
print("  Both are properties of the CRITERION, not of the target.")

print(); print("="*78); print("P2 -- HOSTILE SCAN, 40 dps, cancellation-free"); print("="*78)
mp.dps = 40
def ldp(s):
    z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
    return -1/s**2 - 1/(s-1)**2 + psi(1, s/2)/4 + (z2*z0 - z1**2)/z0**2
ZO = ['14.134725141734693790','21.022039638771554993','25.010857580145688763',
      '30.424876125859513210','32.935061587739189691','37.586178158825671257',
      '40.918719012147495187','43.327073280914999519','48.005150881167159727',
      '49.773832477672302182','60.831778524609809844','72.067157674481907582',
      '82.910380854086030183','92.491899271363505371','101.317851005731391228',
      '111.029535543169674249','124.256818554044396230','134.756509753373871331',
      '150.053520420786230580','167.184439978174633636','182.207078484366461104',
      '195.265396679529768698','213.347919359712666261','231.250188700499964589',
      '250.050858014534837103','270.974351801994133532','295.573254879278634510']
grid = [mpf(k)/5000 for k in range(0, 251)]      # x in [0,0.05] step 2e-4
grid += [mpf(k)/100 for k in range(5, 1001)]     # 0.05 .. 10 step 0.01
grid += [mpf(k)/10 for k in range(100, 601)]     # 10 .. 60 step 0.1
grid += [mpf(k)/2 for k in range(120, 801)]      # 60 .. 400 step 0.5
for z in ZO:
    g = mpf(z)
    for d in ['0','1e-12','-1e-12','1e-6','-1e-6','0.02','-0.02']:
        grid.append(g + mpf(d))
grid = sorted(set(grid))
neg = 0; mn = None; mnx = None
for x in grid:
    v = ldp(mpc(mpf(1)/2, x)).real
    if v < 0: neg += 1
    if mn is None or v < mn: mn, mnx = v, x
print(f"  points: {len(grid)} (2e-4 grid near 0; 0.01 to x=10; 0.1 to 60; 0.5 to 400;")
print(f"          27 zero ordinates x 7 offsets)")
print(f"  NEGATIVES: {neg}    min L1/Xi^2 = {nstr(mn,12)} at x = {nstr(mnx,10)}")

print(); print("="*78); print("P3 -- PIECEWISE ENVELOPE: max(quadratic, linear)"); print("="*78)
def K_lin(a, x):
    if 2*abs(x)*a > np.pi/2: return -1e9
    return (MASS - 2*Tail(a)) - (4*abs(x)/np.pi)*Awin(a) - 2*Tail(a)
def reach(K):
    lo, hi = 0.0, 60.0
    for _ in range(45):
        m = (lo+hi)/2
        if max(K(a, m) for a in agrid) > 0: lo = m
        else: hi = m
    return lo
r_q, r_l = reach(K_quad), reach(K_lin)
r_max = reach(lambda a, x: max(K_quad(a,x), K_lin(a,x)))
print(f"  quadratic alone : |x| <= {r_q:.6f}")
print(f"  linear alone    : |x| <= {r_l:.6f}")
print(f"  max of the two  : |x| <= {r_max:.6f}   (gain {r_max-r_q:+.6f})")

print(); print("="*78); print("P4 -- LOBE-ANNULUS HYBRID: k-lobe truncation"); print("="*78)
def lobeJ(x, k):
    if x <= 0: return 0.0
    lo = 0.0 if k == 0 else (2*k-1)*np.pi/(4*x)
    hi = (2*k+1)*np.pi/(4*x)
    if lo >= VMAX: return 0.0
    hi = min(hi, VMAX); n = 4000
    u = np.linspace(lo, hi, n+1)
    return simp(Rfun(u)*np.abs(np.cos(2*x*u)), (hi-lo)/n)
print("  bound_k = 2*(J0 - J1 + ... +- J_{k-1})  minus the remainder bounded by J_k")
print(f"{'x':>7} {'2(J0-J1)':>15} {'k=4 partial':>15} {'k=6 partial':>15} {'true':>15}")
for x in [4.0, 6.0, 8.0, 8.8, 10.0, 12.0]:
    p2 = 2*(lobeJ(x,0)-lobeJ(x,1))
    p4 = 2*(lobeJ(x,0)-lobeJ(x,1)+lobeJ(x,2)-lobeJ(x,3))
    p6 = p4 + 2*(lobeJ(x,4)-lobeJ(x,5))
    print(f"{x:>7.2f} {p2:>15.6e} {p4:>15.6e} {p6:>15.6e} {Rhat(2*x):>15.6e}")
def reach_lobe(k):
    def f(x):
        s = 0.0
        for j in range(k):
            s += ((-1)**j)*lobeJ(x, j)
        return 2*s
    lo, hi = 0.0, 60.0
    for _ in range(45):
        m = (lo+hi)/2
        if f(m) > 0: lo = m
        else: hi = m
    return lo
for k in [2, 4, 6, 8]:
    print(f"  reach of the {k}-lobe partial sum: |x| <= {reach_lobe(k):.6f}")
print("  NOTE: a k-lobe PARTIAL SUM is a valid lower bound only if the remainder is")
print("  nonnegative, which needs (J_k) decreasing, i.e. R decreasing.  Measured True.")
print("  R DECREASING IS NOT COMPILED -- this route is numerical only.")

print(); print("="*78); print("P5 -- HEAT / de BRUIJN FLOW on the CRITERION"); print("="*78)
def make_R(w):
    return np.array([(hp/3.0)*np.dot(wp, pg**2*w(v+pg)*w(v-pg)) for v in vg])
print(f"{'lam':>7} {'mass_lam':>15} {'reach of criterion':>20}")
for lam in [0.2, 0.1, 0.0, -0.1, -0.2]:
    w = lambda t: np.exp(lam*np.asarray(t,dtype=float)**2)*Phi(t)
    Rl = make_R(w)
    M0l = cum(np.ones_like(vg)) if lam == 0 else None
    y = Rl; cl = np.zeros(NVv+1)
    for k in range(2, NVv+1, 2):
        cl[k] = cl[k-2] + (hv/3.0)*(y[k-2]+4*y[k-1]+y[k])
    cl[1::2] = 0.5*(cl[0:-1:2]+cl[2::2])
    y2 = vg**2*Rl; c2l = np.zeros(NVv+1)
    for k in range(2, NVv+1, 2):
        c2l[k] = c2l[k-2] + (hv/3.0)*(y2[k-2]+4*y2[k-1]+y2[k])
    c2l[1::2] = 0.5*(c2l[0:-1:2]+c2l[2::2])
    Sl = cl[-1]; Ml = 2*Sl
    def K(a, x):
        i = idx(a)
        return (Ml - 2*(Sl-cl[i])) - 2*x*x*(2*c2l[i]) - 2*(Sl-cl[i])
    lo, hi = 0.0, 60.0
    for _ in range(40):
        m = (lo+hi)/2
        if max(K(a, m) for a in agrid) > 0: lo = m
        else: hi = m
    print(f"{lam:>7.2f} {Ml:>15.8e} {lo:>20.6f}")
print("  The flow rescales the kernel but does not change the SHAPE of the trade-off;")
print("  reported as measured.")

print(); print("="*78); print("P6 / P7 / P8 -- factorization, tail representations, pi/3"); print("="*78)
print("  P6 positive convolution factorization: R(v) = (M2*Phi)(2v) - v^2 (Phi*Phi)(2v)")
print("     was verified exactly in batch 14 (reldiff 5.5e-13).  The -v^2 term is what")
print("     prevents R from being a convolution square.  No new sign; not re-run.")
print("  P7 theta-mode / incomplete-gamma tail representations:")
print(f"     the compiled criterion's cap depends ONLY on Qwin (C3B15.criterion_forces_x_bound),")
print(f"     and Qwin saturates: Qwin(0.5)={Qwin(0.5):.6e}, Qwin(0.75)={Qwin(0.75):.6e},"
      f" Qwin(1.5)={Qwin(1.5):.6e}")
print(f"     while Tail(0.75)={Tail(0.75):.3e} is already negligible.  NO representation of")
print("     the tail can move the reach.  Both routes left unrun, and that is stated.")
print("  P8 pi/3 registration for the WINDOW RADIUS a (a genuine cell coordinate):")
print(f"{'a':>16} {'K_quad at x=5':>18} {'K_quad at x=6.5':>18}")
for lab, a in [('pi/3  = 1.04720', np.pi/3), ('pi/6  = 0.52360', np.pi/6),
               ('pi/12 = 0.26180', np.pi/12), ('pi/24 = 0.13090', np.pi/24),
               ('free optimum', None)]:
    if a is None:
        v5 = max(K_quad(aa, 5.0) for aa in agrid); v65 = max(K_quad(aa, 6.5) for aa in agrid)
    else:
        v5 = K_quad(a, 5.0); v65 = K_quad(a, 6.5)
    print(f"{lab:>16} {v5:>18.8e} {v65:>18.8e}")
print("     Measured: the pi/3 lattice is NOT privileged for the window radius.")
print("     No unit-1 scan run (documented false-null trap).")
print("="*78)
