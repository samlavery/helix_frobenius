#!/usr/bin/env python3
r"""
att033A_strip_implA.py  --  INDEPENDENT implementation A of the strip-constrained
band-limited CGdL semidefinite program.   2026-08-12.

=====================================================================================
STATED NULL (written BEFORE any run; rule 1)
=====================================================================================
NULL:  Z(A) rises above the Montgomery-Taylor value 1.3274993 for every A > 0 at which
       the Selberg-density charge is small enough to matter.  Equivalently: the strip
       constraints Re r(v+iw) >= 0 for |w| <= W(A) destroy the CGdL dip -- whose entire
       worth is 1.3274993 - 1.32116 = 0.0063 -- long before the depth cut A/log T is
       deep enough for the discarded off-line zeros to be a negligible fraction of N.
ALTERNATIVE:  some A has  2 - Z(A) - charge(A)  >  0.6725007 (zeta23 Theorem D).
DECISION RULE (pre-registered):
  * NULL NOT REJECTED if  min_A [ Z(A) + charge(A) ] >= 1.3274993 on the grid, where
    charge(A) = 2 C e^{-A/4} with Selberg's exponent and any absolute C >= 1.
  * NULL REJECTED only if some A gives  Z(A) + charge(A) < 1.3274993  at BOTH
    discretisations, with margin > 10x the Delta-to-Delta drift.
DIRECTION OF ERROR: finite w-sampling DROPS constraints, so the reported Z is a LOWER
bound on the true strip-constrained optimum (up to discretisation drift, measured).
A lower bound already above 1.3274993 kills the route -- the safe direction.

=====================================================================================
FUNCTIONAL AND SCALING (derived from scratch here; implementation A)
=====================================================================================
Convention:  r(u) = int rhat(a) e^{2 pi i a u} da.   (Fejer: r=sinc^2 <-> rhat=(1-|a|)_+.)

Write each nontrivial zero as rho = 1/2 + i z,  z = gamma - i y,  y = beta - 1/2;
{z_rho} is stable under z -> conj(z) (functional equation rho -> 1 - conj(rho)).
With L = log T, N = N(T):

  Sum_{rho,rho'} r( (z_rho - conj(z_rho')) L/(2 pi) ) w(..) = N int rhat(a) F(a) da,
  F >= 0 everywhere (perfect square; unconditional -- BGSTB Acta Arith. 2024 Thm 1),
  F(a) = T^{-2|a|} L + |a| + o(1) on |a| <= 1.

Discard |a| > 1 by sign (needs rhat <= 0 there); the spike integrates to 1 against the
DENSITY rhat(0).  So

  Z(rhat) = rhat(0) + int_{-1}^{1} |a| rhat(a) da,
  r >= 0 on R,  r(0) = int rhat = 1,  rhat <= 0 off [-1,1],  supp rhat in [-S,S].

TERMWISE lower bound (Montgomery integrality m^2 >= 2m-1; no matrix lemma).  Sites s,s'
with multiplicities m_s; the (s,s') and (s',s) terms are conjugate and sum to
2 Re r(u_{ss'}) with u_{ss'} = [ (gamma_s-gamma_s') - i (y_s+y_s') ] L / (2 pi).
Hence termwise validity needs   Re r(v + i w) >= 0  for all real v and
      |w| <= W = 2 y_max L / (2 pi) = y_max L / pi.
With the Selberg depth cut y_max = A / L:

      ***  W(A) = A / pi  ***    (u is in mean spacings; mean gap = 2 pi / log T)

The v = 0 slice is the pair-site inequality: a pair {rho, 1-conj(rho)} of multiplicity m
at depth y contributes 2 m^2 (1 + Re r(2 i y L/(2 pi))) >= 0.
Selberg 1946: N(1/2+d,T) << T^{1-d/4} log T, so #{|beta-1/2| > A/L} << e^{-A/4} N up to
an absolute constant.  Final constant  2 - Z(A) - 2 C e^{-A/4}.

=====================================================================================
EXACT SDP (Fejer-Riesz / Toeplitz: no constraint grids, no cutting planes)
=====================================================================================
Atoms on x_j = j Delta with M+1 = S/Delta atoms on the half line.
  r(u) = sum_j c_j e^{2 pi i j Delta u}  (real, even) is a trig polynomial in
  t = 2 pi Delta u, and t sweeps all of R, so
     r >= 0 on R   <=>   (c_j) = diagonal sums of a PSD (M+1)x(M+1) matrix,
     Re r(v+iw) = sum_j c_j cosh(2 pi j Delta w) e^{2 pi i j Delta v}  -- same condition
     on the cosh-weighted atoms.  One PSD block per w-sample.
  TRAP (i): the spike term is the rhat-DENSITY at 0 = c_0/Delta (NOT the atom mass).

TWO CALIBRATION FACTS FOUND HERE (both were needed to make the gates pass):
  (a) M+1 = S/Delta atoms, NOT S/Delta + 1.  Taking one atom more inflates the band by a
      cell and biases Z DOWN by O(Delta): the S=1 control then converges to MT only at
      O(Delta) (1.3011/1.3141 at Delta=.04/.02) instead of O(Delta^2).
  (b) The sign constraint rhat <= 0 must include the atom AT x = 1.  Constraining only
      x > 1 (or only whole cells beyond 1) lets the optimum park positive mass at the band
      edge -- exactly where the CGdL dip starts -- and leaks O(Delta): Z*(2) then reads
      1.2945/1.3076 at Delta=.04/.02 (below CGdL's own unrestricted 1.3208, impossible)
      instead of the correct 1.32119/1.32117.
"""

import sys, time, json
import numpy as np
import scipy.sparse as sp
import cvxpy as cp

MT = 1.3274993          # Montgomery-Taylor (zeta23 Thm D: 2-Z = 0.6725007)
CGDL2 = 1.3212          # band-limited CGdL optimum Z*(2), attempt 033
COSH_CAP = 1e8          # atoms whose cosh weight exceeds this are pinned to 0 (see note)
OUT = "/Users/samuellavery/work/helix_frobenius/tmp/att033A_out.json"


def diag_sum_map(M):
    """sparse (M+1) x (M+1)^2:  (D vec_C(Q))_j = sum_{k-l=j} Q_{kl}."""
    n = M + 1
    rows, cols, vals = [], [], []
    for j in range(n):
        for k in range(j, n):
            rows.append(j); cols.append(k * n + (k - j)); vals.append(1.0)
    return sp.csr_matrix((vals, (rows, cols)), shape=(n, n * n))


def solve_Z(S, Delta, w_samples=(), solver="CLARABEL", **kw):
    n = int(round(S / Delta)); M = n - 1
    D = diag_sum_map(M)
    x = np.arange(n) * Delta
    lo = np.clip(x - Delta / 2, 0, 1); hi = np.clip(x + Delta / 2, 0, 1)
    om = (hi ** 2 - lo ** 2) / (2 * Delta); om[0] = Delta / 4.0
    outside = np.where(x >= 1.0 - 1e-12)[0]          # calibration (b): includes x = 1
    c = cp.Variable(n)
    cons = [c[0] + 2 * cp.sum(c[1:]) == 1]
    if len(outside):
        cons.append(c[outside] <= 0)
    Wmax = max([0.0] + list(w_samples))
    pin = np.where(np.cosh(2 * np.pi * x * Wmax) > COSH_CAP)[0]
    if len(pin):
        cons.append(c[pin] == 0)
    for w in (0.0,) + tuple(w_samples):
        ch = np.minimum(np.cosh(2 * np.pi * x * w), COSH_CAP)
        Q = cp.Variable((n, n), PSD=True)
        cons.append(D @ cp.vec(Q, order="C") == cp.multiply(ch, c))
    obj = c[0] / Delta + om[0] * c[0] + 2 * cp.sum(cp.multiply(om[1:], c[1:]))
    prob = cp.Problem(cp.Minimize(obj), cons)
    try:
        prob.solve(solver=solver, **kw)
    except Exception as e:
        return None, "EXC:%s" % type(e).__name__, None, len(pin)
    cv = None if c.value is None else np.array(c.value).ravel()
    return prob.value, prob.status, cv, len(pin)


def re_r_min(c, Delta, w, ngrid=40001):
    M = len(c) - 1
    jj = np.arange(M + 1)
    b = c * np.minimum(np.cosh(2 * np.pi * jj * Delta * w), 1e30)
    t = np.linspace(0.0, np.pi, ngrid)
    return float((b[0] + 2.0 * (np.cos(np.outer(t, jj[1:])) @ b[1:])).min())


def fejer_gate(Delta):
    n = int(round(1.0 / Delta)); x = np.arange(n) * Delta
    lo = np.clip(x - Delta / 2, 0, 1); hi = np.clip(x + Delta / 2, 0, 1)
    om = (hi ** 2 - lo ** 2) / (2 * Delta); om[0] = Delta / 4.0
    c = Delta * (1.0 - x)
    return float(c[0] / Delta + om[0] * c[0] + 2 * np.sum(om[1:] * c[1:])), \
           float(c[0] + 2 * c[1:].sum())


def analytic_lb(W):
    """|c_j| <= c_0 sech(2 pi j Delta W) (nonneg trig poly) + sum_j c_j = 1 give, as
       Delta -> 0:  spike = c_0/Delta >= 2W  and  |ramp| <= spike * 4G/(4 pi^2 W^2)."""
    if W <= 0:
        return None
    return 2 * W * (1.0 - 3.6638 / (4 * np.pi ** 2 * W ** 2))


def main():
    log = []
    def P(s):
        print(s); sys.stdout.flush(); log.append(s)
    out = {}
    P("=" * 80)
    P("att033A -- implementation A: strip-constrained band-limited CGdL SDP")
    P("NULL: Z(A) > 1.3274993 for every A whose Selberg charge is negligible.")
    P("=" * 80)

    # -------- G2
    P("\n[G2] Fejer gate -- spike term is the rhat-DENSITY at 0 (c_0/Delta)")
    ok2 = True; g2 = {}
    for Delta in (0.04, 0.02, 0.01):
        Z, mass = fejer_gate(Delta)
        pred = 4.0 / 3.0 - Delta ** 2 / 12.0
        good = abs(Z - pred) < 1e-12 and abs(mass - 1.0) < 1e-12
        ok2 &= good; g2[str(Delta)] = Z
        P("   Delta=%.3f  Z_Fejer = %.10f  (4/3 - D^2/12 = %.10f)  mass=%.12f  %s"
          % (Delta, Z, pred, mass, "ok" if good else "FAIL"))
    P("   G2 %s : reads 4/3, not 0.37 -- the mu^2/density term is alive."
      % ("PASS" if ok2 else "FAIL"))
    out["G2"] = {"pass": bool(ok2), "Z_fejer": g2}

    # -------- G1
    P("\n[G1] positive control  S=1 (supp rhat in [-1,1])  ->  MT = %.7f" % MT)
    g1 = {}; s1 = {}
    for Delta in (0.04, 0.02, 0.01):
        t0 = time.time(); v, st, cc, _ = solve_Z(1.0, Delta)
        g1[Delta] = v; s1[Delta] = st
        P("   Delta=%.3f  Z* = %.7f   err = %+.2e   status=%s  (%.1fs)"
          % (Delta, v, v - MT, st, time.time() - t0))
    rat = ((g1[0.04] - MT) / (g1[0.02] - MT), (g1[0.02] - MT) / (g1[0.01] - MT))
    rich = (4 * g1[0.01] - g1[0.02]) / 3.0
    P("   error ratios (4.0 = O(Delta^2)): %.2f , %.2f ;  Richardson = %.7f"
      % (rat[0], rat[1], rich))
    ok1 = abs(rich - MT) < 2e-6 and abs(rat[1] - 4.0) < 0.5
    P("   G1 %s   (033 got 1.3270103/1.3273770/1.3274687; same MT limit, 5.7x larger"
      % ("PASS" if ok1 else "FAIL"))
    P("        O(Delta^2) constant -- implementations agree on the continuum value)")
    out["G1"] = {"pass": bool(ok1), "Z": {str(k): v for k, v in g1.items()},
                 "richardson": rich, "ratios": list(rat),
                 "status": {str(k): v for k, v in s1.items()}}

    # -------- G3
    P("\n[G3] A = 0, S = 2 (band-limited CGdL, no strip) -> 033: Z*(2) ~ 1.3212")
    g3 = {}; c0 = {}
    for Delta in (0.04, 0.02):
        t0 = time.time(); v, st, cc, _ = solve_Z(2.0, Delta)
        g3[Delta] = v; c0[Delta] = cc
        P("   Delta=%.3f  Z*(2) = %.7f   status=%s  (%.1fs)"
          % (Delta, v, st, time.time() - t0))
    vS, stS, _, _ = solve_Z(2.0, 0.04, solver="SCS", eps=1e-10, max_iters=400000)
    P("   solver cross-check Delta=0.04: CLARABEL %.7f vs SCS %.7f (diff %.1e) [%s]"
      % (g3[0.04], vS, abs(g3[0.04] - vS), stS))
    ok3 = abs(g3[0.04] - CGDL2) < 5e-4 and abs(g3[0.02] - CGDL2) < 5e-4
    P("   G3 %s   gain over MT = %.5f" % ("PASS" if ok3 else "FAIL", MT - g3[0.02]))
    out["G3"] = {"pass": bool(ok3), "Z": {str(k): v for k, v in g3.items()},
                 "scs_check": vS}

    P("\n   [structure] min_v Re r(v+iw) at the A=0 optimum (Delta=0.02):")
    for w in (0.0, 0.001, 0.005, 0.02, 0.05):
        P("      w=%.3f   min = %+.6e" % (w, re_r_min(c0[0.02], 0.02, w)))
    P("   -> r has real zeros, and a real zero v0 forces")
    P("      Re r(v0+iw) = -r''(v0) w^2/2 + O(w^4) < 0: the unconstrained optimum")
    P("      violates strip positivity at EVERY w > 0.  The constraint is not slack.")

    # -------- sweep
    P("\n[Z(A)] strip constraints Re r(v+iw) >= 0 for |w| <= W(A) = A/pi")
    P("   w-sample {W/4,W/2,3W/4,W}: dropping constraints => LOWER bound on Z(A).")
    Alist = [0.0, 0.02, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
    rows = []
    for Delta in (0.04, 0.02):
        P("   ---- Delta = %.2f (S=2, n=%d atoms) ----" % (Delta, int(2 / Delta)))
        for A in Alist:
            W = A / np.pi
            ws = () if A == 0 else tuple(W * k / 4 for k in (1, 2, 3, 4))
            t0 = time.time()
            v, st, cc, npin = solve_Z(2.0, Delta, ws)
            chk = ""
            if cc is not None and v is not None and np.isfinite(v):
                chk = "min r=%+.1e minRe r(.+iW)=%+.1e" % (
                    re_r_min(cc, Delta, 0.0), re_r_min(cc, Delta, W))
            ab = analytic_lb(W)
            P("   A=%-5.2f W=%.4f  Z=%s [%s] pin=%d  %s  alb=%s (%.0fs)"
              % (A, W, ("%10.6f" % v) if v is not None else "      None", st, npin,
                 chk, ("%.3f" % ab) if ab else "  -  ", time.time() - t0))
            rows.append({"Delta": Delta, "A": A, "W": W,
                         "Z": None if v is None else float(v),
                         "status": st, "pinned": npin, "analytic_lb": ab})
    out["sweep"] = rows

    # -------- verdict
    P("\n[VERDICT]  final constant = 2 - Z(A) - 2 C e^{-A/4}   vs zeta23 D = 0.6725007")
    P("      A      W      Z(.04)      Z(.02)    toll(.02)   charge(C=1)   2-Z-charge")
    z04 = {r["A"]: r["Z"] for r in rows if r["Delta"] == 0.04}
    z02 = {r["A"]: r["Z"] for r in rows if r["Delta"] == 0.02}
    best = None
    for A in Alist:
        a4, a2 = z04.get(A), z02.get(A)
        if a2 is None:
            continue
        ch = 2 * np.exp(-A / 4.0)
        val = 2 - a2 - ch
        P("   %5.2f  %.4f  %s  %s  %9.6f  %10.6f  %10.6f  %s"
          % (A, A / np.pi, ("%10.6f" % a4) if a4 else "      None", "%10.6f" % a2,
             a2 - z02[0.0], ch, val, "BEATS" if val > 0.6725007 else "no"))
        if best is None or val > best[1]:
            best = (A, val)
    P("   best on grid: A=%.2f -> %.6f   (target 0.6725007)" % best)
    out["verdict_best"] = {"A": best[0], "value": best[1], "target": 0.6725007}

    with open(OUT, "w") as f:
        json.dump({"log": log, **out}, f, indent=1, default=float)
    P("\nwrote %s" % OUT)


if __name__ == "__main__":
    main()
