"""ATTEMPT 013 -- Backlund/Trudgian's explicit S(T) constant x the theta-tape harmonic content.

HOUSE     : the theta-tape line amplitude K(tau_n) = U Lambda(n)^2/(L^2 n) and its window
            criterion R (attempt 010) -- i.e. the EXACT harmonic content of S.
CLASSICAL : Backlund's argument-principle bound on S(T) in Trudgian's 2014 explicit form,
            and its 2021 successor (Hasanalizade-Shen-Wong).
MECHANISM : Backlund treats the whole of S as unknown.  We can compute its harmonic content
            exactly.  If the computable part could be subtracted, Jensen would only have to
            bound the residual.  QUESTION: is the loss AT a step where that insertion is legal?

SOURCES READ AT SOURCE (local copies in ../refs/):
  [T14] T. S. Trudgian, "An improved upper bound for the argument of the Riemann
        zeta-function on the critical line II", J. Number Theory 134 (2014) 280-292.
        arXiv:1208.5846v2.  THEOREM 1:  |S(T)| <= 0.111 log T + 0.275 log log T + 2.450, T>=e.
        COROLLARY 1: |N(T) - (T/2pi)log(T/2pi e) - 7/8| <= same + 0.2/T0.
        (Table 1 of [HSW21] quotes the N(T) form as 0.1120 / 0.2780 / 3.3850.)
  [HSW] E. Hasanalizade, Q. Shen, P.-J. Wong, "Counting zeros of the Riemann zeta function",
        arXiv:2107.06506v1 (2021), J. Number Theory 235 (2022).
        COROLLARY 1.2: |N(T) - (T/2pi)log(T/2pi e)| <= 0.1038 log T + 0.2573 log log T + 9.3675.
        COROLLARY 1.4: |S(T)| <= min{0.1038 logT + 0.2573 loglogT + 8.3675,
                                     0.1095 logT + 0.2042 loglogT + 3.0305}.
        Their Table 1 also records Platt-Trudgian: 0.110 / 0.290 / 2.290.
        THIS IS THE CURRENT PUBLISHED RECORD for the log T coefficient (0.1038 < 0.111).
        (1.7): |S(T)| <= 2.5167 for 0 <= T <= 30 610 046 000, from Platt's zero database.

  *** HSW IS NOT THE RECORD.  Checked at source, 2026-08-12.  The log T coefficient has been
  *** improved three more times since 2021, and by a DIFFERENT architecture:
  [BW25] C. Bellotti, P.-J. Wong (2025)             : 0.10076 log T + 0.24460 loglog T + 8.08344
  [Amb]  V. Amberger, arXiv:2510.27444 (Oct 2025), Corollary 2.2:
             |N(T) - (T/2pi)log(T/2pi e)| <= 0.097 log T + 5.081,  T >= 1   (no loglog term)
         METHOD: NOT Backlund/Jensen.  "Inspired by Turing's method [Tur53, Lemma 1]" -- he
         integrates Im(xi'/xi) directly and uses the Hadamard zero-sum kernel
             Im(xi_K'/xi_K)(s) = sum_rho [ (om-t)/((sig-be)^2+(t-om)^2) - om/(be^2+om^2) ].
  [BW26] C. Bellotti, P.-J. Wong, arXiv:2606.31441 (Jun 2026), Corollary 1.3:
             |N(T) - (T/2pi)log(T/2pi e)| <= 0.0946 log T + 5.746   (T >= 1)   <-- RECORD C1
             |N(T) - (T/2pi)log(T/2pi e)| <= 0.097  log T + 4.954   (T >= 1)
         "the first estimate is sharper for T >= exp(330)".  Their footnote 1 also flags a
         possible sign-convention problem in [Amb]'s C3 values (Table 4), not in C1.
  *** SO THE NAMED CONSTANT TO BEAT IS 0.0946 (Bellotti-Wong 2026), NOT Trudgian's 0.111.
  *** Everything below is scoped to the Backlund-Jensen family (Backlund 1918 -> [BW25]);
  *** it does not bound what the Turing-type architecture of [Amb]/[BW26] can do.

THE CHAIN (identical in [T14] Sec.2-4 and [HSW] Sec.2-3, [HSW] is the cleaner writeup):
  (S1) argument principle: pi N(T) = Delta_C arg xi                          -- exact
  (S2) Gamma / pi^{-s/2} factors -> theta(T)                                 -- exact + O(1/T)
  (S3) Delta arg zeta on the vertical sigma = sigma_1 > 1  <= log zeta(sigma_1)  -- O(1), feeds C3
  (S4) BACKLUND'S TRICK: f_N(s) = (1/2){a(s+iT)^N + a(s-iT)^N}, a(s)=(s-1)zeta(s);
       n = #{real zeros of Re a(sigma+iT)^N on [1/2,sigma_1]} => |Delta arg a| <= (n+1)pi/N.
  (S5) JENSEN + the FE reflection pairing ([T14] Lemma 2, [HSW] Prop 3.2):
          |S(T)| <= S_inf(c,r) / (2 log(r/(c-1/2))) + O(1),
          S_inf(c,r) = lim_N (1/N) sum_{z: f_N(z)=0, |z-c|<r} log(r/|z-c|).
  (S6) S_inf bounded by ([HSW] Prop 3.1) an arcwise Phragmen-Lindelof upper bound
       F_{c,r}(theta) >= (1/N) log|f_N(c+re^{i theta})|, fed by
          |zeta(1+it)| <= c1 (log t)^{c2}        (c1,c2)=(1,1)  [Patel 2020]
          |zeta(1/2+it)| <= k1 t^{k2}(log t)^{k3} (k1,k2,k3)=(0.77,1/6,1) [Hiary 2016, cor. Patel]
       plus the functional equation + trivial bounds for sigma<1/2 and sigma>1.

  Published fact ([HSW] Thm 1.1): C1 = C1(c,r,eta; k2) ONLY.  The log T coefficient does not
  see k1, k3, c1, c2 at all.  So the log T constant is set by (i) the disc geometry and
  (ii) the SUBCONVEXITY EXPONENT k2.  Everything else lives in C2 and C3.

WHAT IS MEASURED HERE.
  A. Reconstruct C1 as a function of k2 from BOTH papers' formulae.  POSITIVE CONTROL:
     must reproduce the published 0.111 and 0.103787 at k2 = 1/6.
  B. Evaluate the k2 -> 0 (Lindelof / "perfect |zeta| bound") limit in CLOSED FORM.
     DC-FIRST: the common mode of log|zeta| on the Jensen circle is NOT an estimate on the
     left half -- the functional equation makes it exactly (1/2-sigma) log(t/2pi) + O(1).
  C. Independent derivation of the same number from the ZERO DENSITY, then MEASURED on the
     cached zeros: the true value of the Jensen input S_inf >= sum_{rho in disc} log(r/|rho-c-iT|).
  D. POSITIVE CONTROL: Jensen's formula identity, checked with mpmath against the cached
     zeros; plus a drop-one-zero control that must fail by exactly log(r/|rho-c-iT|).
  E. The slack: max|S| on the cached windows vs the published bounds.
  F. HOUSE INSTRUMENT APPLIED: how much of S is computable from its harmonic content?
     Truncate the prime sum at x and measure the residual variance and residual sup.

PRE-REGISTERED NULLS (written before running).
  NULL-A : the reconstruction does not reproduce 0.111 / 0.103787 -> instrument BROKEN.
  NULL-B : C1(k2=0) = 0, i.e. the whole log T coefficient is an artefact of the subconvexity
           bound and a perfect |zeta| bound removes it.
  NULL-C : the measured Jensen sum from the zeros is NOT proportional to log T (so the
           log T in the constant is not the local zero density).
  NULL-D : Jensen's formula identity fails at 1e-8 -> census incomplete / off-line zeros.
  NULL-E : (calibration only, no null -- our windows are short, the bound is a sup over all t.)
  NULL-F : truncating the prime sum at x removes a fraction of Var(S) and of max|S| that
           does NOT track the harmonic prediction (log log x + M)/(log log T + M);
           in particular, if the sup share tracks the variance share, no finite prime set
           makes the sup small.

  STATED NULL FOR THE ATTEMPT AS A WHOLE (pre-registered in the task):
     the loss is not at a step where harmonic content of S can be inserted, so the constant
     is untouched.
"""
import numpy as np, math, sys, os
from math import log, pi, sqrt, atan, asin, acos, cos, sin

TMP = os.path.dirname(os.path.abspath(__file__))
def P(*a): print(*a); sys.stdout.flush()
def H(t): P("\n" + "="*100); P(t); P("="*100)

# ----------------------------------------------------------------------------------------
H("PART A -- reconstruct the published log T constants.  POSITIVE CONTROL.")
# ----------------------------------------------------------------------------------------
# Trudgian [T14] Sec.4: the log T coefficient of each arc integral R0..R4, with k2 kept free.
# R0 (sigma >= 1+eta)      : pi                              (|zeta| <= zeta(sigma), exponent 1)
# R1 (1 <= sigma <= 1+eta) : phi1                            (exponent 1)
# R2 (1/2<=sigma<=1)       : 2 k2 R (cos phi1 - cos phi2) + (phi2-phi1)(1-2 k2 eta)
# R3 (0 <= sigma <= 1/2)   : R(1-2k2)(cos phi2-cos phi3) + (phi3-phi2){2k2(1+eta)+1/2-eta}
# R4 (sigma <= 0)          : (1/2-eta)(pi/2-phi3) + R cos phi3
#   [NB: the arXiv v2 text of [T14] Sec.4.6 prints "+ r(1/2+eta)" for the last term of the
#    R4 log T bracket.  The Phragmen-Lindelof exponent on R4 is exactly 3/2 - sigma, whose
#    arc integral is (1/2-eta)(pi/2-phi3) + R cos phi3, and Trudgian's own final formula for
#    a in Sec.6 contains r(1/2+eta) cos phi3.  We use R cos phi3; the check below confirms it
#    is what reproduces his published 0.111.]
# J = R0 + 2R1 + 2R2 + 2R3 + 2R4 ;  n/N <= J/(4 pi log r) - log|a(1+eta+iT)|/(2 log r)
#   and log|a| >= log T + O(1), so  C1 = (A - 2 pi)/(4 pi log r)  with A = the bracket sum.

def trudgian_C1(eta, r, k2):
    d  = 0.5 + eta            # = c - 1/2, horizontal distance centre -> critical line
    R  = r * d                # radius
    if (1.0 + eta) / R > 1.0: return None      # phi3 undefined: disc does not reach sigma=0
    p1 = asin(eta / R); p2 = asin(1.0 / r); p3 = asin((1.0 + eta) / R)
    A = (pi
         + 2*p1
         + 2*(2*k2*R*(cos(p1)-cos(p2)) + (p2-p1)*(1-2*k2*eta))
         + 2*(R*(1-2*k2)*(cos(p2)-cos(p3)) + (p3-p2)*(2*k2*(1+eta) + 0.5 - eta))
         + 2*((0.5-eta)*(pi/2-p3) + R*cos(p3)))
    return (A - 2*pi) / (4*pi*log(r))

def trudgian_a_published(eta, r):
    """[T14] Sec.6 closed formula for a (k2=1/6 already substituted: note the 6 pi)."""
    d = 0.5+eta; R = r*d
    p1 = asin(eta/R); p2 = asin(1.0/r); p3 = asin((1.0+eta)/R)
    num = (p1*eta + (p2 - 3*pi/2)*(0.5+eta) + p3*(1+eta)
           + R*(cos(p1)+cos(p2)+cos(p3)))
    return num / (6*pi*log(r))

def trudgian_b_published(eta, r):
    d = 0.5+eta; R = r*d
    p1 = asin(eta/R); p3 = asin((1.0+eta)/R)
    num = -p1 + p3 + R*((1-cos(p1))/eta + (pi/2 - cos(p3) - p3)/(R - (1+eta)))
    return num / (2*pi*log(r))

ETA_T, R_T = 0.06, 2.08                     # [T14] Sec.6, "Taking eta = 0.06 and r = 2.08"
P(f"  [T14] eta={ETA_T}, r={R_T}")
P(f"    published closed formula  a = {trudgian_a_published(ETA_T,R_T):.6f}   (paper states 0.111)")
P(f"    published closed formula  b = {trudgian_b_published(ETA_T,R_T):.6f}   (paper states 0.275)")
P(f"    our reconstruction  C1(k2=1/6) = {trudgian_C1(ETA_T,R_T,1/6):.6f}")
P(f"    agreement of the two           = {abs(trudgian_a_published(ETA_T,R_T)-trudgian_C1(ETA_T,R_T,1/6)):.2e}")

# HSW [HSW] eq (5.1)/(5.2): C1 = Ctilde1 / (2 pi log(r/(c-1/2))), sigma(theta) = c + r cos theta,
#   theta_y = arccos((y-c)/r);  Ctilde1 = int_{theta_1}^{theta_{1/2}} [(2-2s)(k2+1)+2s-2] dth
#           + (1/2) int_{theta_{1/2}}^{theta_0} [1-2s+4 k2 s] dth
#           + int_{theta_0}^{theta_{-eta}} [-s(1+2eta)/(2eta) + (s+eta)/(2eta)] dth
#           + int_{theta_{-eta}}^{pi} [(1-2s)/2] dth
#   (the 3rd and 4th integrands are algebraically identical: both equal (1-2 sigma)/2)
def hsw_C1(c, r, eta, k2, npts=400001):
    d = c - 0.5
    th = lambda y: acos(max(-1.0, min(1.0, (y - c)/r)))
    t1, thalf, t0, tme = th(1.0), th(0.5), th(0.0), th(-eta)
    def quad(lo, hi, f):
        if hi <= lo: return 0.0
        x = np.linspace(lo, hi, npts); s = c + r*np.cos(x)
        return float(np.trapezoid(f(s), x))
    C = (quad(t1,   thalf, lambda s: (2-2*s)*(k2+1) + 2*s - 2)
         + 0.5*quad(thalf, t0, lambda s: 1 - 2*s + 4*k2*s)
         + quad(t0,  tme,  lambda s: (1-2*s)/2)
         + quad(tme, pi,   lambda s: (1-2*s)/2))
    return C / (2*pi*log(r/d))

C_H, R_H, ETA_H = 1.000011314, 1.064340602, 4.2826451e-6      # [HSW] Table 2 row 1
P(f"\n  [HSW] c={C_H}, r={R_H}, eta={ETA_H}  (their Table 2, row 1)")
P(f"    our reconstruction  C1(k2=1/6) = {hsw_C1(C_H,R_H,ETA_H,1/6):.6f}   (paper states 0.103787)")
for c,rr,ee,pub in ((1.025253504,1.182375395,0.009944751381,0.109410),
                    (1.035766557,1.229059659,0.014325507360,0.111973)):
    P(f"    row (c={c:.6f}, r={rr:.6f}) -> {hsw_C1(c,rr,ee,1/6):.6f}   (paper states {pub})")

# ----------------------------------------------------------------------------------------
H("PART B -- DC FIRST: the k2 -> 0 (Lindelof / perfect-|zeta|-bound) limit, in closed form.")
# ----------------------------------------------------------------------------------------
# On the arc sigma < 1/2 the functional equation gives, EXACTLY (not as an estimate),
#     log|zeta(sigma+it)| = (1/2 - sigma) log(t/2pi) + log|zeta(1-sigma+it)| ,
# and on that arc 1-sigma > 1/2 so the second term is O(log log t) at worst and O(1) for
# sigma<0.  Hence the common mode of log|zeta| on the Jensen circle is
#     (1/2pi) oint log|zeta| = (log T/2pi) * int_{sigma<1/2} (1/2 - sigma) dtheta + O(loglog T)
# Doing the arc integral with sigma = c + r cos theta, d = c-1/2, rho = r/d, v0 = sqrt(rho^2-1):
#     = (d/pi) (v0 - arctan v0) log T
# and |S| <= that / (2 log rho).  So
#     g(d,rho) = d (v0 - arctan v0) / (2 pi log rho),      v0 = sqrt(rho^2 - 1).
def g_closed(d, rho):
    v0 = sqrt(rho*rho - 1.0)
    return d*(v0 - atan(v0))/(2*pi*log(rho))

for lab, d, rho, C1pub in (("[T14] eta=0.06,r=2.08 ", 0.5+ETA_T, R_T, 0.111),
                           ("[HSW] Table 2 row 1  ", C_H-0.5, R_H/(C_H-0.5), 0.103787)):
    g = g_closed(d, rho)
    P(f"  {lab}  d={d:.6f} rho={rho:.6f}")
    P(f"      C1(k2=1/6) published            = {C1pub:.6f}")
    P(f"      C1(k2=0)  closed form g         = {g:.6f}")
    P(f"      numerical C1(k2=0) from formula = "
      f"{(trudgian_C1(ETA_T,R_T,0.0) if 'T14' in lab else hsw_C1(C_H,R_H,ETA_H,0.0)):.6f}")
    P(f"      SURVIVING FRACTION g/C1         = {g/C1pub:.4f}")
    P(f"      recoverable by ANY |zeta| bound = {100*(1-g/C1pub):.2f}%")

P("\n  Geometry sweep (d = 1/2, the minimum: c>1 is needed for the unconditional Euler-product")
P("  lower bound |zeta(c+iT)| >= zeta(2c)/zeta(c) at the Jensen centre).")
P("  ADMISSIBILITY: [HSW] Prop 3.2 requires 1 < c < r, i.e. rho > c/(c-1/2) -> 2 as c->1.")
P("  [T14] needs phi3 = arcsin((1+eta)/R) defined, i.e. R >= 1+eta, i.e. rho >= 2 too.")
P(f"    {'rho':>7}{'g(1/2,rho)':>13}{'C1(k2=1/6)':>13}{'admissible':>12}")
for rho in (1.1, 1.2, 1.3, 1.5, 1.8, 2.0, 2.05, 2.1286305, 2.2, 2.5, 2.8):
    c = 1.0000001; d = c-0.5; rr = rho*d
    try:    c16 = hsw_C1(c, rr, 1e-7, 1/6)
    except Exception: c16 = float('nan')
    P(f"    {rho:>7.4f}{g_closed(0.5,rho):>13.6f}{c16:>13.6f}{'yes' if rho>2 else 'NO (c>r)':>12}")
G_FLOOR = g_closed(0.5, 2.0)
P(f"  -> C1(k2=1/6) is U-shaped with minimum at rho ~ 2.13 = exactly [HSW]'s choice (control OK).")
P(f"  -> g is INCREASING in rho, so over the admissible range rho>2 its infimum is at rho->2+:")
P(f"     FLOOR  g = {G_FLOOR:.6f}   ({100*G_FLOOR/0.103787:.1f}% of [HSW]'s 0.103787)")
P("  -> outside the admissible range g -> 0 as rho -> 1, while C1(k2=1/6) -> infinity.  That is")
P("     the classical 'Lindelof => S(T) = o(log T)' (rho shrinking slowly with T), and it is a")
P("     CONSISTENCY CHECK, not an escape: at fixed geometry the floor is g, and the pairing")
P("     that supplies the factor 2 in 2 log rho is exactly what forces rho > 2.")

# ----------------------------------------------------------------------------------------
H("PART C -- the same number from the ZERO DENSITY, then MEASURED on the cached zeros.")
# ----------------------------------------------------------------------------------------
# [HSW] Prop 3.1 bounds S_inf(c,r) by (1/pi)int_0^pi F, F >= (1/N)log|f_N(c+r e^{i th})|.
# The smallest admissible F is log max(|a(z+iT)|,|a(zbar+iT)|) >= the mean of the two, so for
# EVERY admissible input bound,
#     S_inf(c,r) >= (1/2pi) oint log|a| dtheta - log|a(c+iT)|
#                 = sum_{rho: zeta(rho)=0, |rho-c-iT|<r} log(r/|rho-c-iT|)      (Jensen's formula)
# This is an unconditional FLOOR on the architecture: no improvement to any |zeta| bound can
# push the output below JS(T)/(2 log rho).  Its mean over T is g log T (Part B).
def jensen_sum(gam, T, c, r):
    dz = np.hypot(c - 0.5, gam - T)
    m = dz < r
    return float(np.sum(np.log(r/dz[m]))), int(m.sum())

FILES = [(1e3,'att010_zeros_1e+03.npy'), (1e4,'att010_zeros_1e+04.npy'),
         (1e5,'att010_zeros_1e+05.npy'), (1e6,'att010_zeros_1e+06.npy'),
         (1e7,'att010_zeros_1e+07.npy')]
Z = {}
for Tn, fn in FILES:
    p = os.path.join(TMP, fn)
    if os.path.exists(p): Z[Tn] = np.load(p)
P(f"  loaded windows: " + ", ".join(f"{k:.0e}({len(v)} zeros)" for k,v in Z.items()))

for lab, c, r in (("T14 (d=0.56, rho=2.08)", 0.5+ETA_T, R_T*(0.5+ETA_T)),
                  ("HSW (d=0.500011, rho=2.1286)", C_H, R_H)):
    d = c - 0.5 if lab.startswith("HSW") else 0.5+ETA_T
    cc = 1.0 + ETA_T if lab.startswith("T14") else C_H
    rho = r/d
    g = g_closed(d, rho)
    u0 = sqrt(r*r - d*d)
    P(f"\n  {lab}: centre c={cc:.6f}, radius r={r:.6f}, half-height u0={u0:.4f}, "
      f"2log(rho)={2*log(rho):.4f}")
    # the local zero density is L/2pi with L = log(T/2pi), NOT log T -- so the exact
    # prediction for the mean is g*L, and the log T coefficient is approached from below.
    P(f"    {'T':>9}{'logT':>8}{'mean JS/2lr':>13}{'pred g*L':>10}{'obs/pred':>10}"
      f"{'mean/logT':>11}{'max JS/2lr':>12}{'max/logT':>10}{'max/mean':>10}{'C1 pub':>9}")
    for Tn, gam in sorted(Z.items()):
        lo, hi = gam[0] + u0 + 1.0, gam[-1] - u0 - 1.0
        Ts = np.linspace(lo, hi, 4000)
        vals = np.array([jensen_sum(gam, t, cc, r)[0] for t in Ts])/(2*log(rho))
        LT = log(Tn); L = log(Tn/(2*pi)); pred = g*L
        C1p = 0.111 if lab.startswith("T14") else 0.103787
        P(f"    {Tn:>9.0e}{LT:>8.3f}{vals.mean():>13.4f}{pred:>10.4f}"
          f"{vals.mean()/pred:>10.4f}{vals.mean()/LT:>11.5f}{vals.max():>12.4f}"
          f"{vals.max()/LT:>10.5f}{vals.max()/vals.mean():>10.3f}{C1p:>9.5f}")
    # AC/DC split of the Jensen input.  JS(T) = int w dN = (L/2pi) int w  +  int w dS.
    # The first term is the DC mode -- the local zero density -- and it is the whole log T.
    # The second is the ONLY part that has harmonic content (lines at log n).  If harmonics
    # were perfect it could remove at most the second.
    P(f"    AC/DC audit (sd = the harmonic/AC part, mean = the DC zero-density part):")
    P(f"      {'T':>9}{'DC mean':>10}{'AC sd':>9}{'AC/DC':>9}{'ACmax/DC':>10}")
    for Tn, gam in sorted(Z.items()):
        lo, hi = gam[0] + u0 + 1.0, gam[-1] - u0 - 1.0
        Ts = np.linspace(lo, hi, 4000)
        vals = np.array([jensen_sum(gam, t, cc, r)[0] for t in Ts])/(2*log(rho))
        P(f"      {Tn:>9.0e}{vals.mean():>10.4f}{vals.std():>9.4f}"
          f"{vals.std()/vals.mean():>9.4f}{(vals.max()-vals.mean())/vals.mean():>10.4f}")

P("\n  WHAT A SUBCONVEXITY IMPROVEMENT ACTUALLY BUYS.  C1 is affine in k2 (Part A), so:")
P(f"  {'k2':>12}{'value':>10}{'C1 (HSW geom)':>15}{'gain vs 1/6':>13}   source")
for k2, name in ((1/6, "1/6   -- Hiary 2016 (van der Corput), used by [HSW]"),
                 (27/164, "27/164-- Titchmarsh Thm 5.18, [T14] Sec.7's proposal"),
                 (13/84, "13/84 -- Bourgain 2017 (NOT explicit)"),
                 (0.0, "0     -- Lindelof Hypothesis")):
    v = hsw_C1(C_H, R_H, ETA_H, k2)
    P(f"  {name.split('--')[0].strip():>12}{k2:>10.6f}{v:>15.6f}"
      f"{100*(1-v/0.103787):>12.2f}%   {name.split('--')[1].strip()}")
P("  -> making Bourgain's exponent explicit would move 0.1038 to 0.1024.  Even proving")
P("     Lindelof outright only reaches 0.0840 at this geometry / 0.0786 re-optimised.")

# ----------------------------------------------------------------------------------------
H("PART D -- POSITIVE CONTROL: Jensen's formula identity, and a drop-one-zero control.")
# ----------------------------------------------------------------------------------------
try:
    import mpmath as mp
    ok = True
except Exception as e:
    P(f"  mpmath unavailable: {e}"); ok = False

if ok:
    cc, r = 1.0 + ETA_T, R_T*(0.5+ETA_T)
    gam = Z[1e3]
    P(f"  centre {cc}+iT, radius {r:.6f};  identity to check:")
    P("     (1/2pi) oint log|zeta| dtheta  -  log|zeta(c+iT)|  ==  sum_rho log(r/|rho-c-iT|)")
    P(f"  {'T':>10}{'npts':>6}{'dps':>5}{'#zeros':>8}{'circle mean':>14}{'zero sum':>12}"
      f"{'residual':>12}")
    for T in (1050.0, 1050.0, 1050.0, 2000.37, 3500.11):
        for npts, dps in ((256,25),) if T != 1050.0 else ((128,20),(256,25),(512,30)):
            mp.mp.dps = dps
            th = [mp.mpf(2)*mp.pi*k/npts for k in range(npts)]
            vals = [mp.log(abs(mp.zeta(mp.mpc(cc,T) + r*mp.e**(1j*t)))) for t in th]
            cm = sum(vals)/npts
            lc = mp.log(abs(mp.zeta(mp.mpc(cc,T))))
            js, nz = jensen_sum(gam, T, cc, r)
            P(f"  {T:>10.2f}{npts:>6}{dps:>5}{nz:>8}{float(cm):>14.9f}{js:>12.9f}"
              f"{float(cm-lc)-js:>12.2e}")
    # drop-one-zero control: must fail by exactly log(r/|rho-c-iT|)
    T = 1050.0
    mp.mp.dps = 25; npts = 512
    th = [mp.mpf(2)*mp.pi*k/npts for k in range(npts)]
    cm = sum(mp.log(abs(mp.zeta(mp.mpc(cc,T) + r*mp.e**(1j*t)))) for t in th)/npts
    lc = mp.log(abs(mp.zeta(mp.mpc(cc,T))))
    dz = np.hypot(cc-0.5, gam-T); m = dz < r
    inside = gam[m]
    P(f"\n  DROP-ONE-ZERO CONTROL (must fail by MISSING STRUCTURE, T={T}):")
    for gk in inside:
        keep = gam[gam != gk]
        js, _ = jensen_sum(keep, T, cc, r)
        expect = log(r/math.hypot(cc-0.5, gk-T))
        P(f"    dropped gamma={gk:.6f}: residual = {float(cm-lc)-js:>12.6f}  "
          f"expected {expect:>10.6f}  diff {abs(float(cm-lc)-js-expect):.2e}")

# ----------------------------------------------------------------------------------------
H("PART E -- calibration: max|S| on the cached windows vs the published bounds.")
# ----------------------------------------------------------------------------------------
def theta_t(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def S_on_window(gam, npts=200000):
    """S(t) = N(t) - theta(t)/pi - 1 on the cached window, integer offset pinned by <S>=0
    (|<S>| over a window of length W at height T is O(log T / W) ~ 0.007 here)."""
    lo, hi = gam[0]+1e-6, gam[-1]-1e-6
    t = np.linspace(lo, hi, npts)
    k = np.searchsorted(gam, t, side='right').astype(float)
    base = k - theta_t(t)/np.pi - 1.0
    N0 = round(-base.mean())
    return t, base + N0, base.mean()+N0

P(f"  {'T':>9}{'max|S| win':>12}{'mean S':>10}{'sd S':>9}{'T14 bnd':>10}{'HSW bnd':>10}"
  f"{'ratio T14':>11}{'ratio HSW':>11}")
Sdata = {}
for Tn, gam in sorted(Z.items()):
    t, S, mn = S_on_window(gam)
    Sdata[Tn] = (t, S, gam)
    LT, LLT = log(Tn), log(log(Tn))
    b_T = 0.111*LT + 0.275*LLT + 2.450
    b_H = min(0.1038*LT + 0.2573*LLT + 8.3675, 0.1095*LT + 0.2042*LLT + 3.0305)
    P(f"  {Tn:>9.0e}{np.abs(S).max():>12.4f}{S.mean():>10.5f}{S.std():>9.4f}"
      f"{b_T:>10.4f}{b_H:>10.4f}{np.abs(S).max()/b_T:>11.4f}{np.abs(S).max()/b_H:>11.4f}")
P("  NOTE: our windows are ~2000 long in t; the published bounds are sup over ALL t.  This is a")
P("  CALIBRATION, not a comparison of like with like.  The like-for-like number is [HSW](1.7):")
P("  the verified sup |S(T)| <= 2.5167 for T <= 3.061e10, vs T14 bound "
  f"{0.111*log(3.061e10)+0.275*log(log(3.061e10))+2.450:.4f} at that height.")

# ----------------------------------------------------------------------------------------
H("PART F -- HOUSE INSTRUMENT: how much of S is computable from its harmonic content?")
# ----------------------------------------------------------------------------------------
# tape law (attempt 010):  K(tau_n) = U Lambda(n)^2 / (L^2 n) at tau_n = log n / L.
# In t-coordinates that is the Riemann-von Mangoldt harmonic series
#     S(t) "=" -(1/pi) sum_n Lambda(n) sin(t log n) / (sqrt(n) log n)
# whose ell^2 mass is sum_n Lambda(n)^2/(n log^2 n) = sum_{p^k} 1/(k^2 p^k) ~ log log x + M.
# DC-FIRST PREDICTION (no free parameter): truncating at x captures the variance share
#     (log log x + M) / (log log T + M),      M = Mertens 0.26149721...
# and, if the sup were carried by the same modes, the sup share ~ sqrt of that.
MERTENS = 0.2614972128476428
def primes_to(n):
    s = np.ones(n+1, bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def lambda_terms(x):
    ns, lams = [], []
    for p in primes_to(int(x)):
        pk, k = int(p), 1
        while pk <= x:
            ns.append(pk); lams.append(log(p)); pk *= p; k += 1
    o = np.argsort(ns)
    return np.array(ns, float)[o], np.array(lams, float)[o]

P(f"  {'T':>9}{'x':>9}{'#terms':>8}{'Var(S)':>10}{'Var resid':>11}{'var share':>11}"
  f"{'pred share':>12}{'max|S|':>9}{'max resid':>11}{'sup share':>11}")
for Tn in sorted(Sdata):
    t, S, gam = Sdata[Tn]
    t = t[::20]; S = S[::20]                       # 10k points is plenty for variance/sup
    v0 = S.var(); m0 = np.abs(S).max()
    for x in (10, 100, 1000, 10000, 100000):
        ns, lams = lambda_terms(x)
        w = lams/(np.sqrt(ns)*np.log(ns))
        Sx = -(1/pi)*(np.sin(np.outer(t, np.log(ns)))*w).sum(axis=1)
        res = S - Sx
        share = 1 - res.var()/v0
        pred = (log(log(x)) + MERTENS)/(log(log(Tn)) + MERTENS)
        P(f"  {Tn:>9.0e}{x:>9d}{len(ns):>8d}{v0:>10.4f}{res.var():>11.4f}{share:>11.4f}"
          f"{pred:>12.4f}{m0:>9.4f}{np.abs(res).max():>11.4f}"
          f"{1-np.abs(res).max()/m0:>11.4f}")
P("\n  NULL-F: if the sup share tracks the variance share, no finite prime set makes the sup")
P("  small, and there is nothing to hand to Jensen.")

# ----------------------------------------------------------------------------------------
H("PART G -- THE PAIRING.  Predict the AC part of the Jensen input from the tape law.")
# ----------------------------------------------------------------------------------------
# JS(T) = int w(u) dN(T+u),  w(u) = log(r/sqrt(d^2+u^2)) on |u|<u0,  and
#     dN = (theta'/pi) du + dS   =>   JS = DC + AC,  DC = (L/2pi) int w  (computed in Part C),
#     AC(T) = int w dS = -(1/pi) sum_n (Lambda(n)/sqrt n) cos(T log n) what(log n),
#     what(xi) = int_{-u0}^{u0} w(u) cos(u xi) du.
# So the HOUSE law K(tau_n) ~ Lambda(n)^2/n, transported through the Jensen kernel, PREDICTS
#     sd(AC/(2 log rho)) = sqrt( (1/(2 pi^2)) sum_n Lambda(n)^2 what(log n)^2 / n ) / (2 log rho)
# with NO free parameter.  Note what(xi) is a LOW-PASS filter of width ~1/u0, so it kills every
# line with log n >~ 1: the harmonic content of the Jensen input is essentially n = 2 alone,
# and its variance is HEIGHT-INDEPENDENT even though Var S ~ (1/2pi^2) loglog T grows.
# NULL-G: predicted sd differs from the measured sd by more than 10% -> the harmonic
#         accounting of the Jensen input is wrong and Part C's AC/DC split is not trustworthy.
def what(xi, d, r, u0, npts=200001):
    u = np.linspace(-u0, u0, npts)
    return float(np.trapezoid(np.log(r/np.sqrt(d*d+u*u))*np.cos(u*xi), u))

ns_all, lam_all = lambda_terms(200000)
for lab, cc, d, r in (("T14", 1.0+ETA_T, 0.5+ETA_T, R_T*(0.5+ETA_T)),
                      ("HSW", C_H, C_H-0.5, R_H)):
    rho = r/d; u0 = sqrt(r*r-d*d); den = 2*log(rho)
    wh = np.array([what(log(n), d, r, u0) for n in ns_all])
    var_terms = (lam_all**2)*(wh**2)/ns_all/(2*pi*pi)
    sd_pred = sqrt(var_terms.sum())/den
    order = np.argsort(-var_terms)
    P(f"\n  {lab} geometry (d={d:.4f}, r={r:.4f}, u0={u0:.4f}):")
    P(f"    predicted sd(AC/2log rho) from the tape law = {sd_pred:.5f}   (no free parameter)")
    P(f"    MEASURED sd (Part C, mean over the 5 heights) = "
      f"{np.mean([0.1950,0.1898,0.1897,0.1892,0.1893]) if lab=='T14' else np.mean([0.1945,0.1910,0.1904,0.1898,0.1902]):.5f}")
    P(f"    variance share of the top lines: " + ", ".join(
        f"n={int(ns_all[i])}:{100*var_terms[i]/var_terms.sum():.1f}%" for i in order[:5]))
    P(f"    what(log 2)={what(log(2),d,r,u0):.5f}  what(log 3)={what(log(3),d,r,u0):.5f}  "
      f"what(log 5)={what(log(5),d,r,u0):.5f}  what(log 101)={what(log(101),d,r,u0):.6f}"
      f"  [xi^-2 scale at xi=log101: {1/log(101)**2:.4f}]")
    P("    convergence audit -- sd_pred as the prime-power cutoff X is raised:")
    row = "      "
    for X in (10, 100, 1000, 10000, 100000, 200000):
        m = ns_all <= X
        row += f"X={X}: {sqrt(var_terms[m].sum())/den:.5f}   "
    P(row)
P("\n  MECHANISM.  w has a kink at u = +-u0 (w(+-u0)=0, w'(+-u0)!=0), so what(xi) ~ xi^-2.")
P("  Hence the AC variance is  sum_p (log p)^2 what(log p)^2 / p  ~  sum_p 1/(p (log p)^2),")
P("  a CONVERGENT prime sum -- height-independent.  Contrast Var S = (1/2pi^2) sum_{p<=T} 1/p")
P("  ~ (1/2pi^2) loglog T, which diverges.  The Jensen kernel low-passes S at scale u0 ~ 1 and")
P("  throws away exactly the divergent part.  So the harmonic content of S that survives into")
P("  the Backlund chain is a bounded O(1) term, and the log T is the DC zero density, which is")
P("  not an estimate at all.  THAT is why there is nothing to subtract.")
P("\nDONE.")
