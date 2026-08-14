#!/usr/bin/env python3
r"""
IMPLEMENTATION B  -- strip-constrained CGdL constant Z(A), computed by an
EXACT REDUCTION TO A SINGLE BOUNDARY SLICE (Phragmen-Lindelof), independent
of implementation A's multi-slice w-grid SDP.

================================ SCALING ==================================
alpha  : Montgomery's variable; F(alpha) band of knowledge is |alpha| <= 1.
u      : scaled ordinate difference,  u = (gamma - gamma') * log T.
g(u)   = int ghat(alpha) e^{i alpha u} d alpha,  ghat even and real.
zeros  : rho = 1/2 + delta + i t,  gamma_rho = -i(rho-1/2) = t - i delta.
pairing: BGSTB / Montgomery form uses gamma_rho - conj(gamma_rho'), so

    u = v + i w,   v = (t-t') log T,   w = -(delta+delta') log T.

With the depth cutoff |delta| <= A/log T (deeper zeros charged to Selberg),
the cross terms need   Re g(v + i w) >= 0   for all real v and |w| <= W := 2A.

Re g(v+iw) = c_0 + 2 sum_{j>=1} c_j cosh(x_j w) cos(x_j v),  x_j = j*Delta,
c_j = ghat(x_j)*Delta the atomised even measure on [0,S].

========================= THE EXACT REDUCTION (B) ==========================
ghat compactly supported and integrable => g is bounded on the closed strip
|Im u| <= W (|g| <= e^{SW} ||ghat||_1).  Re g is harmonic there and continuous
up to the boundary.  A BOUNDED harmonic function on a strip that is >= 0 on
both boundary lines is >= 0 inside (Poisson representation / Phragmen-
Lindelof).  ghat even real => Re g(v+iw) is EVEN in w.  Hence

    Re g >= 0 on the whole strip   <=>   Re g(v + iW) >= 0 for all real v.

ONE slice, exactly -- no w-grid, no w-sampling relaxation.  Substituting
b_j := c_j cosh(x_j W) turns that single slice into "b is a nonnegative
cosine polynomial", i.e. an exact Toeplitz/Fejer-Riesz PSD condition, and the
whole problem becomes the ORIGINAL CGdL problem with sech weights:

    minimize   b_0/Delta + 2 sum_{0<x_j<=1} x_j sech(x_j W) b_j
    s.t.       b_0 + 2 sum_{j>=1} sech(x_j W) b_j = 1          (g(0)=1)
               b_j <= 0   for x_j in [1,S]                     (CGdL dip)
               b_0 + 2 sum b_j cos(j theta) >= 0  on the circle (Toeplitz PSD)

W=0 gives sech=1, i.e. the plain band-limited CGdL problem.  W -> infinity
kills every weight except j=0 and Z -> infinity, matching the Liouville fact
that Re g >= 0 on ALL of C forces g constant (so ghat = delta_0, ghat(0)=oo).

=============================== GATES =====================================
G1  S=1 (no dip), W=0  ->  Montgomery-Taylor 1.3274993 (order in Delta)
G2  Fejer gate: the explicit feasible point ghat=(1-|a|)_+ reads 4/3
G3  S=2, W=0           ->  ~1.3212
G4  solver status + primal feasibility audit at every reported point
G5  (B-specific) the single-slice reduction is validated: inner slices of the
    B optimiser are nonnegative, and B agrees with a multi-slice solve.

STATED NULL (pre-registered, before running): the strip constraints destroy
the dip before the Selberg charge is negligible, i.e. min_A [Z(A)+C e^{-A/4}]
> 1.3274993.
"""
import numpy as np
import cvxpy as cp
import time
import sys

MT = 0.5 + (1/np.sqrt(2)) / np.tan(1/np.sqrt(2))   # 1.3274992963...


# ---------------------------------------------------------------- utilities
def sech(x):
    return 1.0 / np.cosh(x)


def audit(cv, xs, W, nv=40001, nw=41):
    """min of Re g(v+iw) over a fine (v,w) grid, and TV data. cv = c_j atoms."""
    n = len(xs) - 1
    th = np.linspace(0, np.pi, nv)                 # theta = Delta*v, one period
    CO = np.cos(np.outer(th, np.arange(n + 1)))
    wts = np.ones(n + 1); wts[1:] = 2.0
    worst = np.inf; wstar = 0.0
    for w in (np.linspace(0, W, nw) if W > 0 else [0.0]):
        gw = CO @ (wts * np.cosh(xs * w) * cv)
        m = gw.min()
        if m < worst:
            worst, wstar = m, w
    return worst, wstar


# ------------------------------------------------------- B primal (Toeplitz)
def solveB(W, Delta=0.02, S=2.0, dip=True, solver="CLARABEL", verbose=False):
    """Exact single-boundary-slice SDP.  Returns (Z, c_atoms, xs, status)."""
    n = int(round(S / Delta))
    xs = np.arange(n + 1) * Delta
    sh = sech(xs * W)
    t0 = time.time()

    Q = cp.Variable((n + 1, n + 1), PSD=True)
    b = cp.hstack([cp.sum(cp.diag(Q, j)) for j in range(n + 1)])

    obj_w = np.zeros(n + 1)
    obj_w[0] = 1.0 / Delta
    for j in range(1, n + 1):
        if xs[j] <= 1.0 + 1e-12:
            obj_w[j] = 2.0 * xs[j] * sh[j]
    nrm_w = np.ones(n + 1) * 2.0 * sh; nrm_w[0] = 1.0

    cons = [nrm_w @ b == 1.0]
    if dip and S > 1.0:
        idx = [j for j in range(1, n) if xs[j] >= 1.0 - 1e-12]
        if idx:
            cons.append(b[idx] <= 0)
    else:
        # supp ghat subset [0,1]:  kill atoms beyond 1
        idx = [j for j in range(1, n + 1) if xs[j] > 1.0 + 1e-12]
        if idx:
            cons.append(b[idx] == 0)
    # EDGE GAUGE: top grid atom set to zero.  Removes the O(Delta) endpoint
    # quadrature exploit (an atom sitting exactly on the support edge is cheap
    # per unit mass and is not a limit of continuous densities); restores the
    # O(Delta^2) rate.  Audited by varying S.
    cons.append(b[n] == 0)

    prob = cp.Problem(cp.Minimize(obj_w @ b), cons)
    try:
        val = prob.solve(solver=solver, verbose=verbose)
    except Exception as e:                                    # noqa
        try:
            val = prob.solve(solver="SCS", eps=1e-9, max_iters=200000)
        except Exception:
            return None, None, xs, "FAIL"
    if Q.value is None:
        return None, None, xs, prob.status
    bv = np.array([float(np.sum(np.diag(Q.value, j))) for j in range(n + 1)])
    cv = bv * sh
    return val, cv, xs, f"{prob.status} [{time.time()-t0:.1f}s]"


# -------------------------------------------- B primal, Lukacs form (2nd cert)
def solveB_lukacs(W, Delta=0.05, S=2.0, dip=True, solver="CLARABEL"):
    """Same problem, positivity certified by Lukacs on [-1,1] in the Chebyshev
    basis instead of Fejer-Riesz on the circle.  Independent SDP shape."""
    n = int(round(S / Delta))
    xs = np.arange(n + 1) * Delta
    sh = sech(xs * W)
    # p(theta) = b_0 + 2 sum b_j cos(j theta) = P(x), x = cos theta, deg n.
    # Chebyshev coefficients of P: t_0 = b_0, t_j = 2 b_j.
    # Lukacs: P >= 0 on [-1,1] <=> P = sigma0 + (1-x^2) sigma1, sigma SOS.
    d0 = n // 2
    d1 = (n - 2) // 2 if n >= 2 else -1
    G0 = cp.Variable((d0 + 1, d0 + 1), PSD=True)
    G1 = cp.Variable((d1 + 1, d1 + 1), PSD=True) if d1 >= 0 else None

    # Chebyshev products: T_i T_j = (T_{i+j} + T_{|i-j|})/2
    def cheb_of_gram(G, d, shift_1mx2):
        coef = [0] * (n + 1)
        expr = [0.0] * (n + 1)
        for i in range(d + 1):
            for j in range(d + 1):
                for (k, w) in ((i + j, 0.5), (abs(i - j), 0.5)):
                    expr[k] = expr[k] + w * G[i, j]
        if shift_1mx2:
            # (1-x^2) = (1 - (T_0+T_2)/2) = (T_0 - T_2)/2
            out = [0.0] * (n + 1)
            for k in range(n + 1):
                if expr[k] is 0.0 and not isinstance(expr[k], cp.Expression):
                    continue
            # multiply series sum_k expr[k] T_k by (T_0 - T_2)/2
            for k in range(n + 1):
                e = expr[k]
                if isinstance(e, float) and e == 0.0:
                    continue
                out[k] = out[k] + 0.5 * e
                for (m, w) in ((k + 2, -0.25), (abs(k - 2), -0.25)):
                    if m <= n:
                        out[m] = out[m] + w * e
            expr = out
        return expr

    e0 = cheb_of_gram(G0, d0, False)
    e1 = cheb_of_gram(G1, d1, True) if G1 is not None else [0.0] * (n + 1)
    tcoef = [e0[k] + e1[k] for k in range(n + 1)]
    b = [tcoef[0]] + [tcoef[k] / 2.0 for k in range(1, n + 1)]

    obj = b[0] / Delta + sum(2.0 * xs[j] * sh[j] * b[j]
                             for j in range(1, n + 1) if xs[j] <= 1.0 + 1e-12)
    cons = [b[0] + sum(2.0 * sh[j] * b[j] for j in range(1, n + 1)) == 1.0]
    for j in range(1, n + 1):
        if dip and S > 1.0 and xs[j] >= 1.0 - 1e-12:
            cons.append(b[j] <= 0)
        if (not dip or S <= 1.0) and xs[j] > 1.0 + 1e-12:
            cons.append(b[j] == 0)
    prob = cp.Problem(cp.Minimize(obj), cons)
    try:
        val = prob.solve(solver=solver)
    except Exception:
        val = prob.solve(solver="SCS", eps=1e-8, max_iters=100000)
    return val, prob.status


# ------------------------------------------------------- B dual (moment LP)
def dualB(W, Delta=0.02, S=2.0, dip=True, ngrid=4000, solver="highs"):
    r"""Lower bound on the same discrete primal, from the DUAL moment problem.

    Dual: find a nonnegative measure nu on the circle (theta in [0,pi]) with
        Psi_j := int cos(j theta) d nu(theta)
        Psi_0            = 1/Delta - Z
        Psi_j*sech_j     = x_j - Z*sech_j     for 0 < x_j <= 1     [wait: see below]
    Derivation in b-coordinates (the variables actually constrained):
        objective coefficient  o_j,  normalisation coefficient  m_j,
        L = o.b - int p(theta) dnu + lam (m.b - 1) + sum_{dip} eta_j b_j
        p(theta) = b_0 + 2 sum_{j>=1} b_j cos(j theta)
      coefficient of b_0 :  o_0 - nu_tot + lam         = 0
      coefficient of b_j :  o_j - 2 Psi_j  + lam m_j   = 0   (j not in dip)
      coefficient of b_j :  o_j - 2 Psi_j  + lam m_j + eta_j = 0, eta_j >= 0
                            (dip: b_j <= 0)   =>  2 Psi_j - lam m_j - o_j >= 0
      dual value = -lam,  maximise.
    Restricting nu to a finite theta-grid is a RESTRICTION of the dual feasible
    set, so any feasible point gives a VALID LOWER BOUND on the discrete primal.
    """
    from scipy.optimize import linprog
    n = int(round(S / Delta))
    xs = np.arange(n + 1) * Delta
    sh = sech(xs * W)
    o = np.zeros(n + 1); o[0] = 1.0 / Delta
    for j in range(1, n + 1):
        if xs[j] <= 1.0 + 1e-12:
            o[j] = 2.0 * xs[j] * sh[j]
    m = 2.0 * sh; m[0] = 1.0
    if not dip or S <= 1.0:
        free = [j for j in range(1, n + 1) if xs[j] > 1.0 + 1e-12]   # b_j == 0
    else:
        free = []
    dipset = set(j for j in range(1, n + 1)
                 if dip and S > 1.0 and xs[j] >= 1.0 - 1e-12)

    th = np.linspace(0, np.pi, ngrid)
    C = np.cos(np.outer(np.arange(n + 1), th))       # (n+1, ngrid)
    # variables: nu (ngrid, >=0), lam (free)
    # equalities  j=0 : nu_tot   - lam = o_0        -> C[0]@nu - lam = o_0
    #             j>=1 non-dip, non-free : 2 Psi_j - lam m_j = o_j
    # inequality  j in dip : 2 Psi_j - lam m_j >= o_j   -> -(...) <= -o_j
    # j in free (b_j == 0): no constraint (b_j fixed 0, drop)
    Aeq, beq, Aub, bub = [], [], [], []
    row = np.concatenate([C[0], [-1.0]]); Aeq.append(row); beq.append(o[0])
    for j in range(1, n + 1):
        if j in free or j == n:      # b_n == 0 (edge gauge): free multiplier
            continue
        row = np.concatenate([2.0 * C[j], [-m[j]]])
        if j in dipset:
            Aub.append(-row); bub.append(-o[j])
        else:
            Aeq.append(row); beq.append(o[j])
    cobj = np.zeros(ngrid + 1); cobj[-1] = 1.0      # minimise lam  ( = -Z )
    bounds = [(0, None)] * ngrid + [(None, None)]
    res = linprog(cobj, A_ub=np.array(Aub) if Aub else None,
                  b_ub=np.array(bub) if Aub else None,
                  A_eq=np.array(Aeq), b_eq=np.array(beq),
                  bounds=bounds, method=solver)
    if not res.success:
        return None, res.message
    return -res.fun, res.status


# =========================================================== gate / run code
def fejer_gate(Delta=0.01, S=2.0):
    """G2: the explicit Fejer feasible point read through the SAME objective."""
    n = int(round(S / Delta))
    xs = np.arange(n + 1) * Delta
    cv = np.where(xs <= 1.0, np.maximum(0.0, 1.0 - xs) * Delta, 0.0)
    nrm = cv[0] + 2 * cv[1:].sum()
    cv = cv / nrm
    Zf = cv[0] / Delta + 2 * sum(xs[j] * cv[j] for j in range(1, n + 1)
                                 if xs[j] <= 1.0 + 1e-12)
    mn, _ = audit(cv, xs, 0.0, nv=20001, nw=1)
    return Zf, nrm, mn


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "gates"
    print(f"# Montgomery-Taylor (zeta23 (7.4), at source): 1/c1* = {MT:.7f},"
          f"  2-1/c1* = {2-MT:.7f}", flush=True)

    if what == "gates":
        print("\n=== G2  Fejer gate (must read 4/3 = 1.3333333) ===", flush=True)
        for D in [0.04, 0.02, 0.01, 0.005]:
            Zf, nrm, mn = fejer_gate(D)
            print(f"  Delta={D:.3f}: Z_Fejer = {Zf:.7f}   (mass before norm "
                  f"{nrm:.6f}, min g = {mn:+.2e})", flush=True)

        print("\n=== G1  S=1, W=0 -> Montgomery-Taylor 1.3274993 ===", flush=True)
        prev = None
        for D in [0.08, 0.04, 0.02, 0.01]:
            Z, cv, xs, st = solveB(0.0, Delta=D, S=1.0, dip=False)
            mn, _ = audit(cv, xs, 0.0, nv=20001, nw=1)
            err = MT - Z
            r = f"  ratio={prev/err:.2f}" if prev else ""
            print(f"  Delta={D:.3f}: Z = {Z:.7f}  err = {err:.2e}{r}"
                  f"  min g = {mn:+.1e}  [{st}]", flush=True)
            prev = err

        print("\n=== G3  S=2, W=0 (dip) -> ~1.3212 ===", flush=True)
        for D in [0.08, 0.04, 0.02]:
            Z, cv, xs, st = solveB(0.0, Delta=D, S=2.0, dip=True)
            mn, _ = audit(cv, xs, 0.0, nv=20001, nw=1)
            print(f"  Delta={D:.3f}: Z = {Z:.7f}  2-Z = {2-Z:.7f}"
                  f"  min g = {mn:+.1e}  [{st}]", flush=True)

    elif what == "curve":
        Delta = float(sys.argv[2]) if len(sys.argv) > 2 else 0.04
        S = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0
        print(f"\n=== Z(A), Delta={Delta}, S={S};  W = 2A strip half-width ===",
              flush=True)
        print("     A       W      Z(A)      2-Z(A)   min Re g on strip   status",
              flush=True)
        for A in [0.0, 0.05, 0.1, 0.15, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0]:
            W = 2 * A
            Z, cv, xs, st = solveB(W, Delta=Delta, S=S, dip=True)
            if Z is None:
                print(f"  {A:5.2f}  {W:5.2f}   FAILED  [{st}]", flush=True)
                continue
            mn, wst = audit(cv, xs, W)
            print(f"  {A:5.2f}  {W:5.2f}  {Z:.7f}  {2-Z:.7f}   {mn:+.2e} @w={wst:.2f}"
                  f"   [{st}]", flush=True)

    elif what == "nodip":
        Delta = float(sys.argv[2]) if len(sys.argv) > 2 else 0.02
        print(f"\n=== Z_nodip(A): supp ghat in [0,1] + strip;  Delta={Delta} ===",
              flush=True)
        print("  does Montgomery-Taylor itself survive strip positivity?",
              flush=True)
        for A in [0.0, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0]:
            W = 2 * A
            Z, cv, xs, st = solveB(W, Delta=Delta, S=1.0, dip=False)
            if Z is None:
                print(f"  A={A:5.2f}: FAILED [{st}]", flush=True); continue
            mn, wst = audit(cv, xs, W)
            print(f"  A={A:5.2f} W={W:5.2f}: Z = {Z:.7f}  2-Z = {2-Z:.7f}"
                  f"  min = {mn:+.1e}  [{st}]", flush=True)

    elif what == "dual":
        Delta = float(sys.argv[2]) if len(sys.argv) > 2 else 0.04
        print(f"\n=== DUAL moment-LP lower bounds (Delta={Delta}) ===", flush=True)
        for (A, S, dip) in [(0.0, 1.0, False), (0.0, 2.0, True),
                            (0.1, 2.0, True), (0.25, 2.0, True),
                            (0.5, 2.0, True), (1.0, 2.0, True)]:
            lb, st = dualB(2 * A, Delta=Delta, S=S, dip=dip)
            Z, cv, xs, stp = solveB(2 * A, Delta=Delta, S=S, dip=dip)
            print(f"  A={A:5.2f} S={S} dip={dip}: dual LB = "
                  f"{lb if lb is None else f'{lb:.7f}'}   primal = "
                  f"{Z if Z is None else f'{Z:.7f}'}   gap = "
                  f"{'--' if (lb is None or Z is None) else f'{Z-lb:.2e}'}  [{st}]",
                  flush=True)

    elif what == "reduction":
        # G5: validate the Phragmen-Lindelof single-slice reduction
        Delta = 0.04
        print("\n=== G5  single-slice reduction check ===", flush=True)
        for A in [0.1, 0.25, 0.5]:
            W = 2 * A
            Z, cv, xs, st = solveB(W, Delta=Delta, S=2.0, dip=True)
            mn, wst = audit(cv, xs, W, nv=40001, nw=81)
            # what does the boundary slice alone read?
            n = len(xs) - 1
            th = np.linspace(0, np.pi, 40001)
            CO = np.cos(np.outer(th, np.arange(n + 1)))
            wts = np.ones(n + 1); wts[1:] = 2.0
            gb = CO @ (wts * np.cosh(xs * W) * cv)
            print(f"  A={A:.2f}: Z={Z:.7f}  min over WHOLE strip {mn:+.2e}"
                  f" (at w={wst:.3f})   min on boundary slice {gb.min():+.2e}",
                  flush=True)

    elif what == "lukacs":
        print("\n=== independent positivity certificate (Lukacs/Chebyshev) ===",
              flush=True)
        for (A, S, dip, D) in [(0.0, 1.0, False, 0.05), (0.0, 2.0, True, 0.05),
                               (0.25, 2.0, True, 0.05), (0.5, 2.0, True, 0.05)]:
            v1, s1 = solveB_lukacs(2 * A, Delta=D, S=S, dip=dip)
            v2, cv, xs, s2 = solveB(2 * A, Delta=D, S=S, dip=dip)
            print(f"  A={A:.2f} S={S} dip={dip} D={D}: Lukacs {v1:.7f} [{s1}]"
                  f"   Toeplitz {v2:.7f}   diff {abs(v1-v2):.2e}", flush=True)
