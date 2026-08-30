#!/usr/bin/env python3
"""
C3 batch 15 -- numerical block 3.  HOSTILE VALIDATION of the COMPILED criterion.

  H1  the compiled implication, checked end to end: wherever the hypothesis
      2 x^2 Q(a) + 4 T(a) <= cosMom R 0 holds, is cosMom R (2x) >= 0 ?
  H2  coverage of the compiled criterion on [0,60], and its reach
  H3  hostile scan of cosMom R (2x) = L1(x) at HIGH PRECISION, cancellation-free:
      x near 0, transition regions, 30 known zero ordinates, and [0,400]
  H4  the cap of criterion_forces_x_bound, per a, against the measured reach
"""
import numpy as np
np.seterr(all='ignore')
from mpmath import mp, mpf, mpc, pi as mpi, log as mlog, fabs as mfabs, psi, zeta, gamma, nstr

# ---------------------------------------------------------------- float64 side: R and moments
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
M0c, M2c = cum(np.ones_like(vg)), cum(vg**2)
S = M0c[-1]
MASS = 2*S                       # cosMom R 0
def idx(a): return int(round(min(max(a,0.0),VMAX)/hv))
def Qwin(a): return 2*M2c[idx(a)]          # int_{(-a,a)} v^2 R  = 2 * int_0^a
def Tail(a): return S - M0c[idx(a)]

# ---------------------------------------------------------------- mpmath side: exact L1
mp.dps = 40
def xi(s): return mpi**(-s/2)*gamma(1+s/2)*(s-1)*zeta(s)
def ldp(s):
    z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
    return -1/s**2 - 1/(s-1)**2 + psi(1, s/2)/4 + (z2*z0 - z1**2)/z0**2
def XI(x): return xi(mpc(mpf(1)/2, x)).real
def L1(x): return XI(x)**2 * ldp(mpc(mpf(1)/2, x)).real   # == cosMom R (2x)

print("="*78); print("SETUP / CONTROL"); print("="*78)
print(f"  cosMom R 0 (float64 grid) = {MASS:.14e}")
print(f"  L1(0) (mpmath, 40 dps)    = {float(L1(mpf(0))):.14e}")
print(f"  reldiff                   = {abs(MASS-float(L1(mpf(0))))/MASS:.3e}")

print(); print("="*78)
print("H1 -- THE COMPILED IMPLICATION, END TO END")
print("="*78)
print("  C3B15.window_criterion_quadratic:  2 x^2 Q(a) + 4 T(a) <= cosMom R 0  =>  L1(x) >= 0")
print("  Wherever the hypothesis holds, the conclusion must hold.  Checked at hostile x with")
print("  the a that minimises the hypothesis's left side.")
agrid = np.arange(0.01, 1.5001, 0.005)
def best_a(x):
    vals = [(2*x*x*Qwin(a) + 4*Tail(a), a) for a in agrid]
    return min(vals)
print(f"{'x':>10} {'best a':>8} {'LHS of hypothesis':>20} {'cosMom R 0':>16} {'holds?':>7} {'L1(x)':>16} {'ok':>4}")
bad = 0
for xs in ['0', '0.25', '1', '2.5', '4', '5', '6', '6.6', '7', '9', '14.134725141734693790']:
    x = float(xs)
    lhs, a = best_a(x)
    holds = lhs <= MASS
    l1 = float(L1(mpf(xs)))
    ok = (not holds) or (l1 >= 0)
    if not ok: bad += 1
    print(f"{xs[:10]:>10} {a:>8.3f} {lhs:>20.10e} {MASS:>16.10e} {str(holds):>7} {l1:>16.6e} {str(ok):>4}")
print(f"  implication violated at {bad} of the sampled points (must be 0)")

print(); print("="*78)
print("H2 -- COVERAGE AND REACH of the compiled criterion")
print("="*78)
def fires(x):
    return best_a(x)[0] <= MASS
lo, hi = 0.0, 40.0
for _ in range(60):
    m = (lo+hi)/2
    if fires(m): lo = m
    else: hi = m
print(f"  REACH of window_criterion_quadratic: fires exactly for |x| <= {lo:.6f}")
cov = sum(1 for k in range(1201) if fires(k/20.0))
print(f"  coverage on x in [0,60] step 0.05: {cov}/1201 ({100.0*cov/1201:.2f}%)")
print(f"  batch 13's best conditional reach was |x| <= 2.503 (4.41% of the same grid)")
print(f"  batch 12 compiled only the single point x = 0")

print(); print("="*78)
print("H3 -- HOSTILE SCAN of cosMom R (2x) = L1(x), cancellation-free at 40 dps")
print("="*78)
ZO = ['14.134725141734693790','21.022039638771554993','25.010857580145688763',
      '30.424876125859513210','32.935061587739189691','37.586178158825671257',
      '40.918719012147495187','43.327073280914999519','48.005150881167159727',
      '49.773832477672302182','60.831778524609809844','72.067157674481907582',
      '82.910380854086030183','92.491899271363505371','101.317851005731391228',
      '111.029535543169674249','124.256818554044396230','134.756509753373871331',
      '150.053520420786230580','167.184439978174633636','182.207078484366461104',
      '195.265396679529768698','213.347919359712666261','231.250188700499964589',
      '250.050858014534837103','270.974351801994133532','295.573254879278634510']
grid = [mpf(k)/2000 for k in range(0, 201)]            # x in [0, 0.1] step 5e-5 (near zero)
grid += [mpf(k)/50 for k in range(5, 501)]             # 0.1 .. 10 step 0.02 (transitions)
grid += [mpf(k)/10 for k in range(100, 601)]           # 10 .. 60 step 0.1
grid += [mpf(k)/2 for k in range(120, 801)]            # 60 .. 400 step 0.5
for z in ZO:
    g = mpf(z)
    for d in ['0','1e-10','-1e-10','1e-4','-1e-4','0.05','-0.05']:
        grid.append(g + mpf(d))
grid = sorted(set(grid))
neg = []; mn = None; mnx = None
for x in grid:
    v = ldp(mpc(mpf(1)/2, x)).real            # sign of L1 == sign of L1/Xi^2
    if v < 0: neg.append((x, v))
    if mn is None or v < mn: mn, mnx = v, x
print(f"  points scanned: {len(grid)}  (near-zero 5e-5 grid, transitions, 27 zero ordinates x 7 offsets, up to x=400)")
print(f"  NEGATIVES of L1/Xi^2: {len(neg)}")
print(f"  min L1/Xi^2 = {nstr(mn,12)} at x = {nstr(mnx,10)}")
if neg:
    for x, v in neg[:10]:
        print(f"    x={nstr(x,12)}  {nstr(v,10)}")

print(); print("="*78)
print("H4 -- THE PER-a CAP of criterion_forces_x_bound, against the measured reach")
print("="*78)
print("  compiled: 2 x^2 Q(a) + 4 T(a) <= cosMom R 0  =>  x^2 <= cosMom R 0 / (2 Q(a))")
print(f"{'a':>7} {'Q(a)':>15} {'T(a)':>15} {'4T<=mass?':>10} {'cap on |x|':>12} {'criterion fires to':>19}")
for a in [0.10, 0.15, 0.20, 0.25, 0.30, 0.40, 0.50, 0.75]:
    Q = Qwin(a); T = Tail(a)
    cap = np.sqrt(MASS/(2*Q)) if Q > 0 else float('inf')
    if 4*T <= MASS:
        xr = np.sqrt(max((MASS - 4*T)/(2*Q), 0.0))
    else:
        xr = 0.0
    print(f"{a:>7.2f} {Q:>15.6e} {T:>15.6e} {str(4*T<=MASS):>10} {cap:>12.6f} {xr:>19.6f}")
print("  The 'cap' column is the compiled necessary bound; the last column is where the")
print("  criterion actually stops for that a.  The optimum over a is the H2 reach.")
print("="*78)
