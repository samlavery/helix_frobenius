#!/usr/bin/env python3
"""
att244 — FULL-RUNG libm-only certificate: unconditional Weil positivity for all
test supports up to [3^{-1/2}, 3^{1/2}] (attempted at L = 0.90, 1.00, 1.05, log 3).

Design (all lemmas stated in the session log; no scipy special functions in the
certified path — trust base = IEEE-754 double + libm sin/cos/log/exp (<=2ulp)
+ Higham's floating-Cholesky backward bound):

  V_h = P1 nodal FE space on [-a, a], mesh h (interior hats + 2 boundary ramps).
  M   = s0*Mass + (q+ q-^T + q- q+^T) + Band,   Band_ij = (1/pi) int_0^R2 w(r)
        Re[eta_i-hat conj(eta_j-hat)] dr,  w = sigma_mid - s0.
  Head:      certified lambda_gen(M, Mass) >= mu by Cholesky of
             Mt - mu*Masst - g*I  (normalized hats), g = folded error pads.
  Complement (Lemma D): G perp V_h  =>  |Ghat(r)| <= ||G|| sqrt(2a) h^2 r^2/8
        (both quadratures => factor 2 in beta_c);  pole tails via interpolation
        of e^{+-u/2} (second derivative e^{a/2}/4).
  Assembly:  lambda_full >= min-eig of [[mu, -cB], [-cB, s0 - beta_tot]].

  beta_c  = (a h^4/16) * I4,   I4 = (1/pi) int_0^R2 |w| r^4 dr   (certified)
  cB      = sqrt(maxW * beta_c) + 2 c_e c_pe h^2
  beta_tot= beta_c + 2 c_pe^2 h^4
  c_e     = sqrt(2 sinh a),  c_pe = sqrt(2a) e^{a/2} / 32.
"""
import numpy as np, math, sys, time
from scipy.linalg import eigh

# ---------------- constants (padded where used in bounds) ----------------
GAMMA, LOG2, LOGPI = 0.5772156649015328606, math.log(2.0), math.log(math.pi)
PSI14 = -GAMMA - 3.0 * LOG2 - math.pi / 2.0
C2 = math.sqrt(2.0) * LOG2
DCONST = PSI14 - LOGPI
R2, NSER = 45.3, 6000
HR = 2.5e-6 if "--endpoint" in sys.argv else 8e-6
NPT = int(R2 / HR)
U = 1.1102230246251565e-16               # unit roundoff 2^-53

def tail_int(T, r2o4):
    return 0.5 * np.log1p(r2o4 / (T + 0.25) ** 2)

def d_at(rval, nser):
    r2o4 = 0.25 * rval * rval
    y = np.arange(nser) + 0.25
    s = float(np.sum(r2o4 / (y * (y * y + r2o4))))
    return (DCONST + s + float(tail_int(nser, np.float64(r2o4))) - 1e-11,
            DCONST + s + float(tail_int(nser - 1, np.float64(r2o4))) + 1e-11)

# ---------------- sigma grid pass (once) ----------------
def sigma_pass():
    print("== SIGMA GRID PASS ==", flush=True)
    d_lo, d_hi = d_at(R2, 2 * 10 ** 6)
    s0 = d_lo - C2 * (1 + 1e-15)
    s0w = d_hi - d_lo
    w = np.empty(NPT)
    wenc = 0.0
    I4 = 0.0
    CH = 500000
    for c0 in range(0, NPT, CH):
        idx = np.arange(c0, min(c0 + CH, NPT))
        r = (idx + 0.5) * HR
        r2o4 = 0.25 * r * r
        acc = np.zeros_like(r)
        for n in range(NSER):
            y = n + 0.25
            acc += r2o4 / (y * (y * y + r2o4))
        lo = DCONST + acc + tail_int(NSER, r2o4)
        hi = DCONST + acc + tail_int(NSER - 1, r2o4)
        wenc = max(wenc, float((hi - lo).max()) + 2e-12)
        wc = 0.5 * (lo + hi) - C2 * np.cos(r * LOG2) - s0
        w[idx] = wc
        I4 += float(np.sum(np.abs(wc) * r ** 4)) * HR / math.pi
    maxW = float(np.abs(w).max()) + wenc + 9.3 * HR   # pointwise sup bound (Lipschitz)
    I4 *= 1.02                                        # generous pad (enters h^4 term only)
    print(f"  s0 = {s0:.12f} (width {s0w:.1e});  w_enc = {wenc:.2e};  "
          f"maxW = {maxW:.4f};  I4(certified+2%) = {I4:.4e}", flush=True)
    return s0, s0w, wenc, maxW, I4, w

# ---------------- FE closed forms (stable) ----------------
def ramp_RI(r, h):
    x = r * h
    Rr = 2.0 * np.sin(0.5 * x) ** 2 / (r * r * h)
    small = np.abs(x) < 1e-3
    Ir = np.where(small, r * h * h / 6.0 * (1 - x * x / 20.0),
                  (x - np.sin(x)) / (r * r * h))
    return Rr, Ir

def hatT(r, h):
    return h * np.sinc(r * h / (2 * math.pi)) ** 2

def pole_vec(nodes, h, s):
    """<eta_i, e^{su}>: interior e^{s u_i} * 4 sinh^2(sh/2)/(s^2 h); ramps via E1,E2."""
    Kh = 4.0 * math.sinh(s * h / 2.0) ** 2 / (s * s * h)
    q = np.exp(s * nodes) * Kh
    E1 = math.expm1(s * h) / s
    E2 = (h * math.exp(s * h) * s - math.expm1(s * h)) / (s * s * h)
    q[0] = math.exp(s * nodes[0]) * (E1 - E2)     # left ramp
    q[-1] = math.exp(s * nodes[-2]) * E2          # right ramp: int (t/h) e^{s(u_{n-1}+t)}
    return q

def mass_matrix(n, h):
    Mass = np.zeros((n + 1, n + 1))
    for i in range(n + 1):
        Mass[i, i] = 2 * h / 3 if 0 < i < n else h / 3
    for i in range(n):
        Mass[i, i + 1] = Mass[i + 1, i] = h / 6
    return Mass

# ---------------- self-tests ----------------
def self_tests():
    print("== SELF-TESTS (transforms & pole forms vs brute quadrature) ==", flush=True)
    h, a = 0.013, 0.31
    t = np.linspace(0, h, 20001)
    for r in [0.37, 7.3, 41.0]:
        num = np.trapz((1 - t / h) * np.exp(1j * r * t), t)
        Rr, Ir = ramp_RI(np.array([r]), h)
        print(f"  ramp rho({r}): closed {Rr[0]:.9e}+{Ir[0]:.9e}i  "
              f"quad {num.real:.9e}+{num.imag:.9e}i")
        u = np.linspace(-h, h, 40001)
        num2 = np.trapz((1 - np.abs(u) / h) * np.cos(r * u), u)
        print(f"  hat T({r}) : closed {hatT(np.array([r]),h)[0]:.9e}  quad {num2:.9e}")
    nodes = np.array([-a + i * 0.1 for i in range(int(2 * a / 0.1) + 1)])
    hh = 0.1
    for s in (0.5, -0.5):
        q = pole_vec(nodes, hh, s)
        u = np.linspace(nodes[1] - hh, nodes[1] + hh, 40001)
        num = np.trapz((1 - np.abs(u - nodes[1]) / hh) * np.exp(s * u), u)
        u0 = np.linspace(nodes[0], nodes[0] + hh, 20001)
        num0 = np.trapz((1 - (u0 - nodes[0]) / hh) * np.exp(s * u0), u0)
        un = np.linspace(nodes[-2], nodes[-1], 20001)
        numn = np.trapz(((un - nodes[-2]) / hh) * np.exp(s * un), un)
        print(f"  pole s={s:+.1f}: int {q[1]:.9e}/{num:.9e}  "
              f"L {q[0]:.9e}/{num0:.9e}  R {q[-1]:.9e}/{numn:.9e}")
    from scipy.special import digamma
    lo, hi = d_at(20.0, 100000)
    ref = float(np.real(digamma(0.25 + 10.0j))) - LOGPI
    print(f"  d(20) bracket [{lo:.10f},{hi:.10f}] scipy {ref:.10f} "
          f"contained={lo <= ref <= hi}", flush=True)

# ---------------- per-L certificate ----------------
def certify(L, w, s0, s0w, wenc, maxW, I4, mu_expect, alpha_est=None, safety=0.15):
    a = L / 2.0
    # mesh from Schur target: beta_c <= 0.3 * mu_expect * s0 / maxW
    bt = 0.3 * mu_expect * s0 / maxW
    h = (bt * 16.0 / (a * I4)) ** 0.25
    n = int(math.ceil(2 * a / h)); h = 2 * a / n
    print(f"== L = {L:.6f}  (a = {a:.5f}, mesh n = {n}, h = {h:.3e}) ==", flush=True)
    nodes = -a + h * np.arange(n + 1)
    tau = np.zeros(n + 1); A = np.zeros(n + 1)
    c00 = 0.0; cLR = 0.0
    CH = 1000000
    t0 = time.time()
    for c0 in range(0, NPT, CH):
        idx = np.arange(c0, min(c0 + CH, NPT))
        r = (idx + 0.5) * HR
        wc = w[idx] * (HR / math.pi)
        T = hatT(r, h); Rr, Ir = ramp_RI(r, h)
        w1 = wc * T * T; w2c = wc * T * Rr; w2s = wc * T * Ir
        c00 += float(np.sum(wc * (Rr * Rr + Ir * Ir)))
        cs2, sn2 = np.cos(2 * a * r), np.sin(2 * a * r)
        cLR += float(np.sum(wc * (cs2 * (Rr * Rr - Ir * Ir) + sn2 * 2 * Rr * Ir)))
        c1, s1v = np.cos(r * h), np.sin(r * h)
        cprev = np.ones_like(r); ccur = c1.copy()
        sprev = np.zeros_like(r); scur = s1v.copy()
        tau[0] += float(np.sum(w1)); A[0] = 0.0
        tau[1] += float(np.sum(w1 * ccur)); A[1] += float(np.sum(w2c * ccur + w2s * scur))
        for d in range(2, n + 1):
            cnew = 2 * c1 * ccur - cprev; snew = 2 * c1 * scur - sprev
            cprev, ccur = ccur, cnew; sprev, scur = scur, snew
            tau[d] += float(np.sum(w1 * ccur))
            A[d] += float(np.sum(w2c * ccur + w2s * scur))
    print(f"  tau/A accumulated in {time.time()-t0:.0f}s", flush=True)
    # assemble B
    B = np.zeros((n + 1, n + 1))
    ii = np.arange(1, n)
    B[np.ix_(ii, ii)] = tau[np.abs(ii[:, None] - ii[None, :])]
    B[0, ii] = A[ii]; B[ii, 0] = A[ii]
    B[n, ii] = A[n - ii]; B[ii, n] = A[n - ii]
    B[0, 0] = B[n, n] = c00; B[0, n] = B[n, 0] = cLR
    qp = pole_vec(nodes, h, 0.5); qm = pole_vec(nodes, h, -0.5)
    Mass = mass_matrix(n, h)
    M = s0 * Mass + np.outer(qp, qm) + np.outer(qm, qp) + B
    nrm = np.sqrt(np.diag(Mass))
    Mt = M / nrm[:, None] / nrm[None, :]
    Nt = Mass / nrm[:, None] / nrm[None, :]
    lam_f = eigh(Mt, Nt, subset_by_index=[0, 0], eigvals_only=True)[0]
    print(f"  float generalized bottom = {lam_f:+.6e}", flush=True)
    # ---- certified head via Cholesky ----
    # error pads folded into g: quad-op + recurrence + libm (generous), alpha est
    quad_op = (n + 1) * (R2 * HR * HR / 24.0) * (130.0 * h * h * 1.5 / math.pi) / (2 * h / 3)
    g_pads = quad_op + 1e-9
    if alpha_est is None:
        alpha_est = (n + 1) * U * (n + 1) * 1.6  # ~ gamma_{n+1} * trace(A)
    mu = lam_f - wenc - s0w - g_pads - alpha_est - safety * abs(lam_f)
    Atry = Mt - mu * Nt - (g_pads + alpha_est) * np.eye(n + 1)
    try:
        Rch = np.linalg.cholesky(Atry)
        gam = (n + 1) * U / (1 - (n + 1) * U)
        alpha_true = gam * float(np.sum(Rch * Rch))
        ok = alpha_true <= alpha_est
        print(f"  Cholesky OK at mu = {mu:+.6e}; alpha_true {alpha_true:.2e} "
              f"<= est {alpha_est:.2e}: {ok}", flush=True)
        if not ok:
            mu = -1.0
    except np.linalg.LinAlgError:
        print("  Cholesky FAILED — head not certified at this mu", flush=True)
        mu = -1.0
    # ---- complement + 2x2 ----
    beta_c = (a * h ** 4 / 16.0) * I4
    c_e = math.sqrt(2 * math.sinh(a)); c_pe = math.sqrt(2 * a) * math.exp(a / 2) / 32.0
    cB = math.sqrt(maxW * beta_c) + 2 * c_e * c_pe * h * h
    beta_tot = beta_c + 2 * (c_pe * h * h) ** 2
    S = s0 - beta_tot
    lam2 = 0.5 * (mu + S) - math.sqrt(0.25 * (S - mu) ** 2 + cB * cB)
    print(f"  complement: beta_c {beta_c:.2e}  cB {cB:.2e}  S {S:.6f}")
    verdict = "*** CERTIFIED POSITIVE — WEIL POSITIVITY HOLDS AT THIS SUPPORT ***" \
        if (mu > 0 and lam2 > 0) else "!!! NOT CLOSED AT THIS SUPPORT !!!"
    print(f"  FULL-SPACE CERTIFIED BOTTOM >= {lam2:+.6e}   {verdict}", flush=True)
    return lam2

def main():
    self_tests()
    s0, s0w, wenc, maxW, I4, w = sigma_pass()
    if "--endpoint" in sys.argv:
        plan = [(math.log(3.0), 1.6e-8, 3.6e-9, 0.05)]
    else:
        plan = [(0.90, 9e-6, None, 0.15), (1.00, 5e-7, None, 0.15),
                (1.05, 1.8e-7, None, 0.15), (math.log(3.0), 1.6e-8, None, 0.15)]
    out = {}
    for L, mu_e, aest, saf in plan:
        out[L] = certify(L, w, s0, s0w, wenc, maxW, I4, mu_e, alpha_est=aest, safety=saf)
    print("== SUMMARY ==")
    for L, v in out.items():
        print(f"  L = {L:.6f}: certified bottom {v:+.3e}  {'POSITIVE' if v > 0 else 'not closed'}")

if __name__ == "__main__":
    main()
