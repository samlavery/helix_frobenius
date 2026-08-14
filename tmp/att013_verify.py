"""ADVERSARIAL VERIFICATION of attempt 013 (Backlund/Trudgian x tape-law DC/AC split).

Independent re-derivation.  Nothing is copied from att013_backlund_slack.py: the log T
coefficient function is re-derived from the Phragmen-Lindelof + functional-equation structure,
the arc integrals use scipy adaptive quadrature (they used trapezoid on a fixed grid), the
Fourier transform of the Jensen kernel uses scipy's oscillatory-weight quadrature, and the
Jensen measurement is re-done with the local L (window centre) rather than the window label.

CHECK LIST
  V1  positive control: reproduce HSW Table 2 C1 = 0.103787 / 0.109410 / 0.111973 (k2=1/6)
      from a FIRST-PRINCIPLES log T coefficient function, not from transcribing (5.2).
  V2  Trudgian's own closed formula for a (transcribed by me from refs/trudgian.txt line 442).
  V3  the k2 -> 0 closed form g, the fraction, the floor over the admissible range rho > 2,
      and an EXACT algebraic identity check g == C1(k2=0).
  V4  zero-cache validation (Riemann-von Mangoldt count + mpmath spot-check of actual zeros).
  V5  Jensen input: mean vs LOCAL density (window centre!), sd, at several radii/grids.
      -> tests failure mode 6 (L at the edge vs the centre) on their "monotone convergence".
  V6  tape-law AC prediction with independent quadrature + cutoff audit; xi^-2 law check.
  V7  Jensen identity + drop-one-zero control at a DIFFERENT T, centre, radius than theirs.
  V8  max-statistic audit of the "saturation" claim.
"""
import numpy as np, math, os, sys
from math import log, pi, sqrt, atan, acos, cos, sin, hypot
from scipy.integrate import quad

TMP = os.path.dirname(os.path.abspath(__file__))
def P(*a): print(*a); sys.stdout.flush()
def H(t): P("\n" + "=" * 96); P(t); P("=" * 96)

# ---------------------------------------------------------------------------------------
H("V1  POSITIVE CONTROL -- C1(k2) rebuilt from first principles (PL + FE), not transcribed")
# ---------------------------------------------------------------------------------------
# On the Jensen circle the integrand of HSW's Ctilde1 is exactly the log T coefficient of the
# admissible bound for log|zeta(sigma+it)| (the +1 from |s-1| in a(s)=(s-1)zeta(s) integrates
# to pi over [0,pi] and is cancelled by the -log|a(c+iT)| term of Jensen's formula).
#   sigma >= 1        : 0                       (|zeta(1+it)| << (log t)^{c2})
#   1/2 <= sigma <= 1 : 2 k2 (1-sigma)          (Phragmen-Lindelof between k2 at 1/2 and 0 at 1)
#   0 <= sigma <= 1/2 : (1/2-sigma) + 2 k2 sigma (FE, reflected point in [1/2,1])
#   sigma <= 0        : (1/2-sigma)             (FE, reflected point >= 1)
def e_coeff(sig, k2):
    if sig >= 1.0:  return 0.0
    if sig >= 0.5:  return 2*k2*(1-sig)
    if sig >= 0.0:  return (0.5-sig) + 2*k2*sig
    return 0.5 - sig

def C1_firstprinciples(c, r, k2):
    d = c - 0.5; rho = r/d
    th = lambda y: acos(max(-1.0, min(1.0, (y-c)/r)))
    # break points where e is non-smooth: sigma = 1, 1/2, 0
    br = sorted({0.0, th(1.0), th(0.5), th(0.0), pi})
    tot = 0.0
    for lo, hi in zip(br[:-1], br[1:]):
        if hi <= lo: continue
        v, _ = quad(lambda t: e_coeff(c + r*cos(t), k2), lo, hi, limit=400, epsabs=1e-14, epsrel=1e-14)
        tot += v
    return tot / (2*pi*log(rho))

HSW_ROWS = [(1.000011314, 1.064340602, 0.103787),
            (1.025253504, 1.182375395, 0.109410),
            (1.035766557, 1.229059659, 0.111973)]
P(f"  {'c':>13}{'r':>13}{'mine k2=1/6':>14}{'published':>12}{'diff':>11}")
for c, r, pub in HSW_ROWS:
    mine = C1_firstprinciples(c, r, 1/6)
    P(f"  {c:>13.9f}{r:>13.9f}{mine:>14.6f}{pub:>12.6f}{mine-pub:>11.2e}")

# ---------------------------------------------------------------------------------------
H("V2  Trudgian's own closed formula for a, transcribed by me from refs/trudgian.txt")
# ---------------------------------------------------------------------------------------
# [T14] (6.1)ff:  a = [phi1*eta + (phi2-3pi/2)(1/2+eta) + phi3(1+eta)
#                      + r(1/2+eta)(cos phi1 + cos phi2 + cos phi3)] / (6 pi log r)
# with (Sec.4) phi1=asin(eta/R), phi2=asin(1/r), phi3=asin((1+eta)/R), R=r(1/2+eta).
def trudgian_a(eta, rr):
    d = 0.5+eta; R = rr*d
    p1 = math.asin(eta/R); p2 = math.asin(1.0/rr); p3 = math.asin((1.0+eta)/R)
    num = p1*eta + (p2 - 3*pi/2)*(0.5+eta) + p3*(1+eta) + R*(cos(p1)+cos(p2)+cos(p3))
    return num/(6*pi*log(rr))
ETA_T, RHO_T = 0.06, 2.08
aT = trudgian_a(ETA_T, RHO_T)
P(f"  a(eta=0.06, r=2.08) = {aT:.9f}    [T14] Theorem 1 prints 0.111")
# Trudgian's geometry as a (c,r) disc: centre c = 1+eta, radius R = rho*(1/2+eta)
cT, rT = 1.0+ETA_T, RHO_T*(0.5+ETA_T)
P(f"  my first-principles C1 at the same disc, k2=1/6 = {C1_firstprinciples(cT, rT, 1/6):.9f}")
P(f"  (difference {abs(C1_firstprinciples(cT,rT,1/6)-aT):.2e}) -> the arc structure agrees")

# ---------------------------------------------------------------------------------------
H("V3  the k2->0 closed form g, exact identity, fractions, and the admissible floor")
# ---------------------------------------------------------------------------------------
def g_closed(d, rho):
    v0 = sqrt(rho*rho - 1.0)
    return d*(v0 - atan(v0))/(2*pi*log(rho))
# ALGEBRAIC PROOF (checked numerically below):
#   (1/2pi) oint (1/2-sigma)_+ dtheta = (1/pi) int_{theta*}^{pi} (-d - r cos th) dth
#     = (1/pi)[-d arccos(1/rho) + d sqrt(rho^2-1)] = (d/pi)(v0 - arctan v0)
#   and the SAME number is (1/2pi) int_{-u0}^{u0} log(r/sqrt(d^2+u^2)) du = d(v0-arctan v0)/pi,
#   i.e. Jensen's formula: the k2=0 arc integral and the kernel mass are the same object.
for c, r, pub in HSW_ROWS + [(cT, rT, 0.111)]:
    d = c-0.5; rho = r/d
    g = g_closed(d, rho); c0 = C1_firstprinciples(c, r, 0.0)
    Ik, _ = quad(lambda u: log(r/sqrt(d*d+u*u)), -sqrt(r*r-d*d), sqrt(r*r-d*d), limit=400)
    P(f"  c={c:.6f} r={r:.6f} rho={rho:.6f}: g={g:.7f}  C1(k2=0)={c0:.7f}  "
      f"kernel-mass/2pi={Ik/(2*pi):.7f}  (all three equal: {max(abs(g-c0), abs(g-Ik/(2*pi))):.1e})")
    P(f"      g/C1(1/6) = {g/C1_firstprinciples(c,r,1/6):.4f}   "
      f"=> Lindelof would remove {100*(1-g/C1_firstprinciples(c,r,1/6)):.2f}% at FIXED geometry")
P("\n  admissibility (HSW (4.11)):  1+eta < c  =>  d > 1/2 ;  c-r < 1-c  =>  r > 2c-1 = 2d  =>  rho > 2")
P(f"  {'rho':>8}{'g(1/2,rho)':>13}{'C1(1/6)':>12}")
for rho in (2.0, 2.02, 2.05, 2.1, 2.1286, 2.2, 2.5, 3.0, 4.0):
    cc = 0.5 + 0.5 + 1e-9; d = cc-0.5
    P(f"  {rho:>8.4f}{g_closed(0.5, rho):>13.6f}{C1_firstprinciples(cc, rho*d, 1/6):>12.6f}")
P(f"  FLOOR over the admissible range (d->1/2, rho->2+): g = {g_closed(0.5,2.0):.6f}"
  f"  = {100*g_closed(0.5,2.0)/0.103787:.1f}% of HSW's 0.103787")

# ---------------------------------------------------------------------------------------
H("V4  zero-cache validation (Riemann-von Mangoldt count + mpmath spot-check)")
# ---------------------------------------------------------------------------------------
def theta_rs(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
FILES = [(1e3,'att010_zeros_1e+03.npy'), (1e4,'att010_zeros_1e+04.npy'),
         (1e5,'att010_zeros_1e+05.npy'), (1e6,'att010_zeros_1e+06.npy'),
         (1e7,'att010_zeros_1e+07.npy')]
Z = {}
for Tn, fn in FILES:
    p = os.path.join(TMP, fn)
    if os.path.exists(p): Z[Tn] = np.load(p)
P(f"  {'label T':>9}{'first':>15}{'last':>15}{'span':>10}{'#zeros':>8}{'RvM pred':>10}{'diff':>7}")
for Tn, g in sorted(Z.items()):
    pred = (theta_rs(g[-1]) - theta_rs(g[0]))/pi
    P(f"  {Tn:>9.0e}{g[0]:>15.4f}{g[-1]:>15.4f}{g[-1]-g[0]:>10.1f}{len(g)-1:>8d}{pred:>10.2f}"
      f"{len(g)-1-pred:>7.2f}")
P("  NOTE: the window LABEL is the window START, not its centre.  At T=1e3 the window runs")
P("        1001 -> 6199, so log(T_label/2pi)=5.07 but the window-mean of log(t/2pi) is ~6.3.")
try:
    import mpmath as mp
    mp.mp.dps = 25
    P("  mpmath spot-check |zeta(1/2+i gamma)| at cached zeros (should be ~0):")
    for Tn in (1e3, 1e6, 1e7):
        g = Z[Tn]
        for k in (0, len(g)//2):
            v = abs(mp.zeta(mp.mpc(0.5, g[k])))
            P(f"    T={Tn:.0e} gamma={g[k]:.9f}  |zeta| = {float(v):.3e}")
except Exception as ex:
    P(f"  mpmath unavailable: {ex}")

# ---------------------------------------------------------------------------------------
H("V5  Jensen input: DC vs the LOCAL zero density, and the AC sd -- my own measurement")
# ---------------------------------------------------------------------------------------
def jensen_series(gam, Ts, c, r):
    d = c - 0.5
    out = np.empty(len(Ts))
    for i, T in enumerate(Ts):
        dz = np.hypot(d, gam - T)
        m = dz < r
        out[i] = np.sum(np.log(r/dz[m]))
    return out

GEOMS = [("T14  ", cT, rT), ("HSW  ", HSW_ROWS[0][0], HSW_ROWS[0][1])]
meas_sd = {}
for lab, c, r in GEOMS:
    d = c-0.5; rho = r/d; u0 = sqrt(r*r-d*d); den = 2*log(rho); g = g_closed(d, rho)
    P(f"\n  {lab} c={c:.6f} r={r:.6f} rho={rho:.5f} u0={u0:.4f} 2log rho={den:.4f} g={g:.6f}")
    P(f"    {'label':>8}{'npts':>7}{'mean JS/2lr':>13}{'g*L(label)':>12}{'ratio_edge':>11}"
      f"{'g*<L(t)>':>11}{'ratio_ctr':>11}{'AC sd':>9}{'max':>9}")
    for Tn, gam in sorted(Z.items()):
        for npts in (4000, 20000):
            lo, hi = gam[0]+u0+1.0, gam[-1]-u0-1.0
            Ts = np.linspace(lo, hi, npts)
            v = jensen_series(gam, Ts, c, r)/den
            Lloc = np.log(Ts/(2*pi))
            P(f"    {Tn:>8.0e}{npts:>7d}{v.mean():>13.4f}{g*log(Tn/(2*pi)):>12.4f}"
              f"{v.mean()/(g*log(Tn/(2*pi))):>11.4f}{g*Lloc.mean():>11.4f}"
              f"{v.mean()/(g*Lloc.mean()):>11.4f}{v.std():>9.4f}{v.max():>9.4f}")
            if npts == 20000: meas_sd[(lab, Tn)] = (v.std(), v.mean(), v.max(), Ts, v)
    # sub-band check inside the widest window: does the local ratio stay 1 everywhere?
    gam = Z[1e3]
    P("    sub-band audit inside the T=1e3 window (ratio vs the LOCAL density):")
    edges = np.linspace(gam[0]+u0+1, gam[-1]-u0-1, 6)
    for a, b in zip(edges[:-1], edges[1:]):
        Ts = np.linspace(a, b, 4000)
        v = jensen_series(gam, Ts, c, r)/den
        Lloc = np.log(Ts/(2*pi)).mean()
        P(f"      t in [{a:7.1f},{b:7.1f}]  mean={v.mean():.4f}  g*L_local={g*Lloc:.4f}"
          f"  ratio={v.mean()/(g*Lloc):.4f}  sd={v.std():.4f}")

# radius sensitivity (noise audit they did not do): does the DC identity hold off-geometry?
P("\n  RADIUS / CENTRE SENSITIVITY (their audit varied only precision, not geometry):")
P(f"    {'c':>8}{'r':>8}{'rho':>8}{'T':>9}{'mean/(g*<L>)':>14}{'AC sd':>9}")
for c, r in ((1.06, 1.1648), (1.06, 1.40), (1.2, 1.60), (1.5, 2.20), (1.06, 2.50)):
    d = c-0.5; rho = r/d; u0 = sqrt(r*r-d*d); den = 2*log(rho); g = g_closed(d, rho)
    for Tn in (1e5, 1e7):
        gam = Z[Tn]
        Ts = np.linspace(gam[0]+u0+1, gam[-1]-u0-1, 6000)
        v = jensen_series(gam, Ts, c, r)/den
        P(f"    {c:>8.3f}{r:>8.4f}{rho:>8.4f}{Tn:>9.0e}"
          f"{v.mean()/(g*np.log(Ts/(2*pi)).mean()):>14.5f}{v.std():>9.4f}")

# ---------------------------------------------------------------------------------------
H("V6  tape-law AC prediction, independent quadrature (scipy oscillatory weight)")
# ---------------------------------------------------------------------------------------
def what_osc(xi, d, r, u0):
    """int_{-u0}^{u0} log(r/sqrt(d^2+u^2)) cos(u xi) du, adaptive oscillatory quadrature."""
    f = lambda u: log(r/sqrt(d*d+u*u))
    v, _ = quad(f, -u0, u0, weight='cos', wvar=xi, limit=300, epsabs=1e-13, epsrel=1e-13)
    return v

def prime_powers(X):
    X = int(X)
    s = np.ones(X+1, bool); s[:2] = False
    for i in range(2, int(X**0.5)+1):
        if s[i]: s[i*i::i] = False
    ns, lam = [], []
    for p in np.nonzero(s)[0]:
        pk = int(p)
        while pk <= X:
            ns.append(pk); lam.append(log(p)); pk *= int(p)
    o = np.argsort(ns)
    return np.array(ns, float)[o], np.array(lam, float)[o]

NS, LAM = prime_powers(1_000_000)
P(f"  prime powers up to 1e6: {len(NS)} terms")
for lab, c, r in GEOMS:
    d = c-0.5; rho = r/d; u0 = sqrt(r*r-d*d); den = 2*log(rho)
    wh = np.array([what_osc(log(n), d, r, u0) for n in NS])
    var = (LAM**2)*(wh**2)/NS/(2*pi*pi)
    P(f"\n  {lab} predicted sd(AC/2log rho):")
    row = []
    for X in (10, 100, 1e3, 1e4, 1e5, 1e6):
        m = NS <= X
        row.append(f"X={X:g}:{sqrt(var[m].sum())/den:.5f}")
    P("    cutoff audit  " + "  ".join(row))
    sd_pred = sqrt(var.sum())/den
    o = np.argsort(-var)
    P(f"    top lines: " + ", ".join(f"n={int(NS[i])}:{100*var[i]/var.sum():.1f}%" for i in o[:6]))
    P(f"    PREDICTED sd = {sd_pred:.5f}")
    for Tn in sorted(Z):
        if (lab, Tn) in meas_sd:
            sd = meas_sd[(lab, Tn)][0]
            P(f"      measured at T={Tn:.0e}: {sd:.5f}   ratio meas/pred = {sd/sd_pred:.4f}")
    # xi^-2 law: what(xi) * xi^2 / (2 u0 / r^2) should oscillate like -cos(u0 xi)
    P("    xi^-2 law check  (what(xi)*xi^2*r^2/(2u0)  vs  -cos(u0 xi)):")
    for xi in (2.0, 5.0, 10.0, 20.0, 50.0):
        lhs = what_osc(xi, d, r, u0)*xi*xi*r*r/(2*u0)
        P(f"      xi={xi:5.1f}  lhs={lhs:+.5f}   -cos(u0 xi)={-cos(u0*xi):+.5f}")

# ---------------------------------------------------------------------------------------
H("V7  Jensen identity + drop-one-zero control at a DIFFERENT T / centre / radius")
# ---------------------------------------------------------------------------------------
try:
    import mpmath as mp
    for (c, r, T, npts, dps) in ((1.13, 1.30, 100501.7, 192, 25),
                                 (1.06, 1.1648, 100501.7, 384, 30),
                                 (1.000011314, 1.064340602, 1000404.3, 256, 30)):
        mp.mp.dps = dps
        gam = Z[1e5] if T < 5e5 else Z[1e6]
        vals = [mp.log(abs(mp.zeta(mp.mpc(c, T) + r*mp.e**(1j*(2*mp.pi*k/npts))))) for k in range(npts)]
        cm = sum(vals)/npts
        lc = mp.log(abs(mp.zeta(mp.mpc(c, T))))
        dz = np.hypot(c-0.5, gam-T); m = dz < r
        js = float(np.sum(np.log(r/dz[m])))
        P(f"  c={c} r={r} T={T} npts={npts} dps={dps}: circle-mean-minus-centre="
          f"{float(cm-lc):.9f}  zero-sum={js:.9f}  residual={float(cm-lc)-js:.2e}  (#zeros={int(m.sum())})")
        ins = gam[m]
        if len(ins):
            gk = ins[0]
            keep = gam[gam != gk]
            dz2 = np.hypot(c-0.5, keep-T); m2 = dz2 < r
            js2 = float(np.sum(np.log(r/dz2[m2])))
            exp = log(r/hypot(c-0.5, gk-T))
            P(f"    drop-one control: residual={float(cm-lc)-js2:.6f}  expected={exp:.6f}"
              f"  diff={abs(float(cm-lc)-js2-exp):.2e}")
except Exception as ex:
    P(f"  mpmath step skipped: {ex}")

# ---------------------------------------------------------------------------------------
H("V8  max-statistic audit of the 'saturation' claim")
# ---------------------------------------------------------------------------------------
for lab, c, r in GEOMS:
    d = c-0.5; rho = r/d; g = g_closed(d, rho)
    for Tn in (1e6, 1e7):
        if (lab, Tn) not in meas_sd: continue
        sd, mean, mx, Ts, v = meas_sd[(lab, Tn)]
        n_eff = (Ts[-1]-Ts[0])/(2*pi/log(Tn/(2*pi)))   # ~ number of independent cells (zero spacings)
        P(f"  {lab} T={Tn:.0e}: mean={mean:.4f} sd={sd:.4f} max={mx:.4f}"
          f"  (max-mean)/sd = {(mx-mean)/sd:.2f}  independent cells ~ {n_eff:.0f}"
          f"  sqrt(2 ln cells) = {sqrt(2*log(n_eff)):.2f}")
        P(f"      C1_pub*log T = {(0.111 if lab.startswith('T14') else 0.103787)*log(Tn):.4f}"
          f"   g*<L> = {g*np.log(Ts/(2*pi)).mean():.4f}")
P("\nDONE.")
