#!/usr/bin/env python3
"""
att034_verifyA.py -- ADVERSARIAL INDEPENDENT VERIFICATION of the strip-constrained
CGdL / Tsang pair-correlation SDP.  Written from scratch; shares no code with
att033A_strip_implA.py, att034b_stripB.py, att035_*.py.

STATED NULLS (written before running):
  V0  (spike):   the objective's first term is the ghat-DENSITY at 0.  NULL: it is the
                 atom MASS; then Z(S=1,A=0) will NOT converge to 1.3274993 but to
                 something Delta-dependent / divergent.
  V1  (control): S=1, A=0 SDP -> 1.3274992963 with error O(Delta^2).
                 REJECT the implementation if the error order is not ~2 or the limit
                 differs from the closed form by more than the extrapolation residual.
  V2  (exactness of {r>=0}):  Toeplitz/Fejer-Riesz PSD parametrisation is EXACT, not a
                 relaxation.  Test: min over a fine u-grid of the reconstructed r(u)
                 must be >= -1e-9 (feasible), AND the SDP value must not sit BELOW a
                 published feasible point (BGSTB) -- if it does, the parametrisation
                 is a relaxation (too big a class) or a bug.
  V3  (strip on a grid?):  the single slice |w| = A/pi is claimed to imply all
                 |w| <= A/pi.  NULL: it does not, and intermediate w are violated.
                 Test: reconstruct Re r(v+iw) for a fine 2-D grid of (v,w).
  V4  (headline): Z(0)=1.32117 at S=2, Z(0.5)=1.350256 at S=2, A*=0.208, Z(A=0.5,S=1)
                 whole-class = 1.382229.
CONVENTION (mine, fixed once):
  r(u) = int rhat(alpha) e^{2 pi i alpha u} dalpha,  rhat even real, supp in [-S,S].
  Montgomery functional:  Z = [ rhat(0) + int_{-1}^{1} |alpha| rhat(alpha) dalpha ] / r(0).
  Strip: Re r(v + i w) >= 0 for |w| <= A/pi   <=>   rhat(alpha) cosh(2 pi alpha w) is
  positive definite.  Parametrise rhat(alpha) = hhat(alpha) sech(2 A alpha) with hhat
  positive definite (h >= 0).  Then 2 pi w_max = 2 A, i.e. w_max = A/pi.
"""
import sys
import numpy as np
import cvxpy as cp
from scipy.integrate import quad
from scipy.optimize import brentq

np.set_printoptions(precision=10, suppress=False)
SQ2 = np.sqrt(2.0)

# ----------------------------------------------------------------------------
# P1 : closed forms
# ----------------------------------------------------------------------------
def p1():
    MT = 0.5 + (1.0/SQ2)/np.tan(1.0/SQ2)
    cstar = SQ2*np.tan(1/SQ2)/(SQ2 + np.tan(1/SQ2))
    print("P1  Montgomery-Taylor 1/c*_1 = 1/2 + 2^{-1/2}cot(2^{-1/2}) = %.10f" % MT)
    print("P1  zeta23 (7.4) c*_1 = %.10f   (printed 0.7532960...), 1/c*_1 = %.10f"
          % (cstar, 1/cstar))
    print("P1  2 - 1/c*_1 = %.10f   (zeta23 Theorem D prints 0.67250...)" % (2-MT))
    return MT

# ----------------------------------------------------------------------------
# P2 : reproduce BGSTB's TWO printed proportions from my own functional
#      Z = [ j(0) + 2 int_0^1 a j(a) sech(2A a) da ] / [ 2 int_0^S j sech(2A a) da ],  A=1/2
# ----------------------------------------------------------------------------
def jF(a):
    a = np.abs(a)
    return np.where(a <= 1.0, 1.0 - a, 0.0)

def jM(a):
    f = jF(a)
    return (1.0/(1.0-np.cos(SQ2)))*( (1.0/(2*SQ2))*np.sin(SQ2*f) + 0.5*f*np.cos(SQ2*a) )

def Zfun_smooth(j, A, S=1.0):
    num_spike = float(j(np.array(0.0)))
    I1 = quad(lambda a: a*float(j(np.array(a)))/np.cosh(2*A*a), 0, min(1.0, S),
              limit=400, epsabs=1e-14, epsrel=1e-13)[0]
    I0 = quad(lambda a: float(j(np.array(a)))/np.cosh(2*A*a), 0, S,
              limit=400, epsabs=1e-14, epsrel=1e-13)[0]
    return (num_spike + 2*I1)/(2*I0), num_spike, 2*I1, I0

def p2():
    print("\nP2  BGSTB (arXiv 2306.04799) reproduction, A = 1/2  <=>  sech(alpha)")
    for name, j, pr_prop, pr_I1, pr_I0, pr_j0 in [
        ("Fejer     ", jF, 0.608612927, 0.2913876354, 0.4640648392, 1.0),
        ("Mont-Taylr", jM, 0.617483786, 0.2832624869, 0.4663199124, 1.0061271908)]:
        Z, j0, I1, I0 = Zfun_smooth(j, 0.5, 1.0)
        print("  %s j(0)=%.10f (printed %.10f)  2*int a j sech=%.10f (printed %.10f)"
              % (name, j0, pr_j0, I1, pr_I1))
        print("             int j sech=%.10f (printed %.10f)  Z=%.10f  2-Z=%.10f (printed %.9f)  diff=%.2e"
              % (I0, pr_I0, Z, 2-Z, pr_prop, abs((2-Z)-pr_prop)))
    return

# ----------------------------------------------------------------------------
# THE SDP.  Fejer-Riesz / Toeplitz-PSD, EXACT parametrisation of {h >= 0}.
#   atoms x_k = k*Delta, k = 0..m-1, x_{m-1} = S  (so m = round(S/Delta)+1)
#   b_k = sum_i Q[i,i+k],  Q >= 0 real symmetric m x m   <=>   h(u)=sum_k b_k e(k D u) >= 0
#   c_k = b_k * sech(2 A x_k)
#   r(0) = c_0 + 2 sum_{k>=1} c_k = 1                       (normalisation)
#   objective = c_0/Delta + 2 sum_{k>=1, x_k<=1} x_k c_k     (spike = DENSITY)
#   dip       = c_k <= 0 for x_k > 1
# spike_mode: 'density' (c_0/Delta) or 'mass' (c_0)  -- V0 test
# ----------------------------------------------------------------------------
def solve_sdp(S, A, Delta, spike_mode='density', nonneg_rhat=False,
              solver='CLARABEL', verbose=False, edge_gauge=False, m_extra=0):
    # m = round(S/Delta) generator atoms == MIDPOINT rule for the continuum profile f
    # on an interval of length S.  m_extra=+1 puts full weight on both endpoints
    # (trapezoid-with-full-ends) and is O(Delta) LOSSY -- see the quadrature audit.
    m = int(round(S/Delta)) + m_extra
    x = Delta*np.arange(m)
    if edge_gauge:                       # deliberately reproduce the reported bug
        m -= 1
        x = x[:m]
    sech = 1.0/np.cosh(2*A*x)
    Q = cp.Variable((m, m), symmetric=True)
    b = [cp.sum(cp.diag(Q, k)) for k in range(m)]
    c = [b[k]*sech[k] for k in range(m)]
    cons = [Q >> 0]
    r0 = c[0] + 2*cp.sum(cp.hstack(c[1:])) if m > 1 else c[0]
    cons.append(r0 == 1)
    tol = 1e-12
    for k in range(m):
        if x[k] > 1.0 + tol:
            cons.append(c[k] <= 0)
    if nonneg_rhat:
        for k in range(m):
            if x[k] <= 1.0 + tol:
                cons.append(c[k] >= 0)
    spike = c[0]/Delta if spike_mode == 'density' else c[0]
    lin = [2*x[k]*c[k] for k in range(1, m) if x[k] <= 1.0 + tol]
    obj = spike + (cp.sum(cp.hstack(lin)) if lin else 0)
    prob = cp.Problem(cp.Minimize(obj), cons)
    prob.solve(solver=solver, verbose=verbose)
    if Q.value is None:
        return None, None, None, prob.status
    Qv = Q.value
    bv = np.array([np.trace(Qv, offset=k) for k in range(m)])
    cv = bv*sech
    return prob.value, cv, x, prob.status

def richardson(v1, d1, v2, d2, order=2):
    """extrapolate v(Delta) = v + C Delta^order from two Deltas"""
    r = (d1/d2)**order
    return (r*v2 - v1)/(r - 1.0)

# ----------------------------------------------------------------------------
# feasibility audit of a returned solution: r(u) >= 0 and Re r(v+iw) >= 0
# ----------------------------------------------------------------------------
def audit(cv, x, A, Delta, nv=20001, nw=41):
    """r(u) = c_0 + 2 sum_{k>=1} c_k cos(2 pi x_k u);   period 1/Delta in u."""
    u = np.linspace(0, 1.0/Delta, nv)
    R = cv[0] + 2*(cv[1:][None, :]*np.cos(2*np.pi*np.outer(u, x[1:]))).sum(axis=1)
    minr = R.min()
    # strip: Re r(v+iw) = c_0 + 2 sum c_k cos(2 pi x_k v) cosh(2 pi x_k w)
    wmax = A/np.pi
    worst = np.inf
    worst_w = None
    for w in np.linspace(0, wmax, nw):
        ck = cv[1:]*np.cosh(2*np.pi*x[1:]*w)
        Rw = cv[0] + 2*(ck[None, :]*np.cos(2*np.pi*np.outer(u, x[1:]))).sum(axis=1)
        mm = Rw.min()
        if mm < worst:
            worst, worst_w = mm, w
    return minr, worst, worst_w

# ----------------------------------------------------------------------------
def main():
    MT = p1()
    p2()

    print("\n" + "="*78)
    print("QUADRATURE AUDIT: m = round(S/Delta) (midpoint) vs +1 (full-weight ends)")
    print("="*78)
    for D in [0.04, 0.02, 0.01]:
        a, _, _, _ = solve_sdp(1.0, 0.0, D, m_extra=0)
        b_, _, _, _ = solve_sdp(1.0, 0.0, D, m_extra=1)
        print("  Delta=%.4f   m=S/D : %.8f (err %+.2e)   m=S/D+1 : %.8f (err %+.2e)"
              % (D, a, a-MT, b_, b_-MT))

    print("\n" + "="*78)
    print("V0/V1  POSITIVE CONTROL:  S=1, A=0.  Expect 1.3274992963, order Delta^2.")
    print("="*78)
    rows = []
    for D in [0.08, 0.04, 0.02, 0.01, 0.005]:
        v, cv, x, st = solve_sdp(1.0, 0.0, D)
        mr, ms, mw = audit(cv, x, 0.0, D)
        rows.append((D, v))
        print("  Delta=%.4f  Z=%.8f   err=%+.3e   status=%s   min_u r(u)=%.2e"
              % (D, v, v-MT, st, mr))
    print("  --- observed convergence order (successive Deltas halved) ---")
    for i in range(len(rows)-2):
        e1 = rows[i][1]-MT; e2 = rows[i+1][1]-MT; e3 = rows[i+2][1]-MT
        if abs(e2) > 0 and abs(e3) > 0:
            print("    Delta %.3f->%.3f->%.3f : ratios %.3f, %.3f  => order %.3f"
                  % (rows[i][0], rows[i+1][0], rows[i+2][0], e1/e2, e2/e3,
                     np.log2(abs(e2/e3))))
    r2 = richardson(rows[-2][1], rows[-2][0], rows[-1][1], rows[-1][0], 2)
    print("  Richardson(order2) from Delta=%.3f,%.3f : %.9f   (target %.9f, diff %.2e)"
          % (rows[-2][0], rows[-1][0], r2, MT, r2-MT))

    print("\n" + "="*78)
    print("V0  SPIKE TEST (trap (i)): objective with MASS instead of DENSITY at 0")
    print("="*78)
    for D in [0.04, 0.02, 0.01]:
        v, cv, x, st = solve_sdp(1.0, 0.0, D, spike_mode='mass')
        print("  Delta=%.4f  Z_massSpike=%s  status=%s (density-spike -> %.7f)"
              % (D, ("%.8f" % v) if v is not None else "None", st, MT))
    print("  -> if the spike is read as a MASS the value collapses and is Delta-blind;")
    print("     this is the mu^2/DC term being deleted.  Confirms trap (i).")

    print("\n" + "="*78)
    print("V2  EDGE-GAUGE BUG REPRODUCTION (the reported gate failure), S=1, A=0.5")
    print("="*78)
    for D in [0.04, 0.02, 0.01]:
        v1, _, _, _ = solve_sdp(1.0, 0.5, D, edge_gauge=True)
        v2, _, _, _ = solve_sdp(1.0, 0.5, D, edge_gauge=False)
        print("  Delta=%.4f  with edge gauge %.6f   without %.6f   cost %+.6f"
              % (D, v1, v2, v1-v2))

    print("\n" + "="*78)
    print("V2/V4  WHOLE-TSANG-CLASS at A=1/2, S=1  (must be <= BGSTB's MT value)")
    print("="*78)
    Zmt, _, _, _ = Zfun_smooth(jM, 0.5, 1.0)
    Zfe, _, _, _ = Zfun_smooth(jF, 0.5, 1.0)
    print("  feasible points:  Fejer Z=%.7f   Montgomery-Taylor Z=%.7f" % (Zfe, Zmt))
    vals = []
    for D in [0.04, 0.02, 0.01]:
        v, cv, x, st = solve_sdp(1.0, 0.5, D)
        mr, ms, mw = audit(cv, x, 0.5, D)
        vals.append((D, v))
        print("  Delta=%.4f  Z=%.7f  status=%s  min_u r=%.2e  min strip Re r=%.2e (w*=%.4f)"
              % (D, v, st, mr, ms, mw))
    print("  Richardson -> %.7f" % richardson(vals[-2][1], vals[-2][0], vals[-1][1], vals[-1][0]))
    # with the extra BGSTB constraint j >= 0 (rhat >= 0 on [-1,1])
    v, cv, x, st = solve_sdp(1.0, 0.5, 0.01, nonneg_rhat=True)
    print("  same but with BGSTB's extra pointwise j>=0 constraint: Z=%.7f" % v)

    print("\n" + "="*78)
    print("V3  STRIP FEASIBILITY OVER ALL |w| <= A/pi  (is the single slice enough?)")
    print("="*78)
    for A in [0.25, 0.5, 1.0]:
        v, cv, x, st = solve_sdp(2.0, A, 0.02)
        mr, ms, mw = audit(cv, x, A, 0.02, nv=8001, nw=81)
        print("  A=%.2f S=2 Delta=0.02 : Z=%.6f  min_u r=%.3e   min_{v,w} Re r=%.3e at w=%.4f (w_max=%.4f)"
              % (A, v, mr, ms, mw, A/np.pi))

    print("\n" + "="*78)
    print("V4  HEADLINE:  Z(A) at S=2 (the CGdL dip band)")
    print("="*78)
    Zof = {}
    for A in [0.0, 0.1, 0.15, 0.2, 0.208, 0.25, 0.3, 0.5, 1.0, 1.5, 2.0]:
        out = []
        for D in [0.04, 0.02]:
            v, cv, x, st = solve_sdp(2.0, A, D)
            out.append((D, v, st))
        rich = richardson(out[0][1], out[0][0], out[1][1], out[1][0])
        Zof[A] = rich
        print("  A=%-6.3f  Z(.04)=%.6f  Z(.02)=%.6f  Rich=%.6f   2-Z=%.6f   [%s]"
              % (A, out[0][1], out[1][1], rich, 2-rich, out[1][2]))
    np.save('/Users/samuellavery/work/helix_frobenius/tmp/att034_verifyA_ZA.npy',
            np.array(sorted(Zof.items())))

    print("\n  crossing A* where Z(A) = %.7f :" % MT)
    ks = sorted(Zof)
    zs = [Zof[k] for k in ks]
    f = lambda a: np.interp(a, ks, zs) - MT
    try:
        Astar = brentq(f, 0.0, 0.5)
        print("    A* = %.4f  (linear interp on the Richardson curve)" % Astar)
    except Exception as e:
        print("    bracket failed:", e)

    print("\n" + "="*78)
    print("V4  band sensitivity at A=0: S = 1, 1.5, 2, 3, 4")
    print("="*78)
    for S in [1.0, 1.5, 2.0, 3.0, 4.0]:
        out = []
        for D in [0.04, 0.02]:
            v, cv, x, st = solve_sdp(S, 0.0, D)
            out.append((D, v))
        print("  S=%.2f  Z(.04)=%.7f  Z(.02)=%.7f  Rich=%.7f  2-Z=%.7f"
              % (S, out[0][1], out[1][1],
                 richardson(out[0][1], out[0][0], out[1][1], out[1][0]),
                 2-richardson(out[0][1], out[0][0], out[1][1], out[1][0])))

if __name__ == '__main__':
    main()
