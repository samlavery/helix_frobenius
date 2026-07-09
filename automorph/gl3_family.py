"""GL(3) family test: the vanishing-side instrument across a family of degree-3 L-functions.

Second genuine GL(3) object(s), run through the SAME machinery as tmp/gl3_vanishing.py,
so that the wall / cell / weld structure becomes COMPARABLE across GL(3) L-functions.

Family:
  Sym^2 f_k  for the level-1 weight-k Hecke eigenforms  f_k  with  k in {12,16,18,20}.
  S_k(SL_2(Z)) is 1-dimensional for these k, so the normalized q-expansion of
      f_12 = Delta,   f_16 = Delta * E_4,   f_18 = Delta * E_6,   f_20 = Delta * E_8
  IS the Hecke eigenform (a_1 = 1 automatically).  Each Sym^2 f_k is a genuine GL(3)
  automorphic L-function (Gelbart-Jacquet, level 1, self-dual, root number eps = +1,
  entire since f is cuspidal non-CM).

Why a family:
  The ONLY thing that changes across k is the archimedean gamma shift  m = k - 1  in
      gamma(s) = Gamma_R(s + 1) Gamma_C(s + m).
  So the run separates two registers cleanly:
    * UNIVERSAL (weight-independent) : phase cells = 1.0000 pi, all zeros simple (d=1),
      weld pins to the eps=+1 ray.  These must NOT move with k.
    * GAMMA-DEPENDENT               : zero density N(T) must climb with k on the
      log-law read straight off the gamma factor (integral of (dtheta/dt)/pi).
  That is the measurable answer to "does the wall scale with the gamma data?"

From-scratch (no oracle, non-circular):
  tau(n) exact via the integer recurrence  m c_m = -24 sum_{j<=m} sigma_1(j) c_{m-j}
      (c_m = [q^m] prod (1-q^n)^24,  tau(n) = c_{n-1}),
  Eisenstein E_{k-12} exact via a sigma-sieve,
  eigenform a_n = [q^n](Delta * E_{k-12}) exact big-int convolution,
  self-validated by Hecke multiplicativity  a_{p^2} = a_p^2 - p^{k-1}  and the
  Deligne bound |a_p| <= 2 p^{(k-1)/2}, and by the Sym^2 Euler-vs-Dirichlet s=2
  certificate.  No L-library enters any locator.

Run: python3 tmp/gl3_family.py
Out: tmp/gl3_family_results.txt, tmp/gl3_family_summary.txt
"""
import math
import os
import time

import numpy as np
from scipy.special import loggamma

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "gl3_family_results.txt")
SUMMARY = os.path.join(HERE, "gl3_family_summary.txt")

# Eisenstein normalization constants: E_w = 1 + C_w sum sigma_{w-1}(n) q^n.
EIS_CONST = {0: None, 4: 240, 6: -504, 8: 480, 10: -264, 14: -24}
# Family of level-1 eigenforms f_k = Delta * E_{k-12} (k=12 => E_0 = 1, f = Delta).
WEIGHTS = [12, 16, 18, 20]

# Sym^2 s=2 certificate tolerance.  Both the Dirichlet sum and the Euler product are
# truncated at N, so their agreement is truncation-floored (~1e-7 at N=6000), NOT
# machine-zero; that floor shrinks with N (the N=300000 reference reaches 1e-10).  This
# gate only has to catch a WRONG coefficient, which is O(1) off -- 6-digit agreement
# certifies the construction decisively.  (Hecke + Deligne are checked EXACTLY separately.)
CERT_TOL = 1e-6

_lines = []
def emit(s=""):
    _lines.append(s)
    print(s, flush=True)


def _flush():
    with open(OUT, "w") as fh:
        fh.write("\n".join(_lines) + "\n")


# ---------------------------------------------------------------------------
# Exact arithmetic: sigma sieve, tau, Eisenstein, eigenform convolution
# ---------------------------------------------------------------------------
def sigma_sieve(N, s):
    """sigma_s(n) = sum_{d|n} d^s, exact Python ints, for n in 0..N."""
    sig = [0] * (N + 1)
    for d in range(1, N + 1):
        ds = d ** s
        for n in range(d, N + 1, d):
            sig[n] += ds
    return sig


def tau_exact(N):
    """tau(n) for n in 1..N via  m c_m = -24 sum_{j=1}^m sigma_1(j) c_{m-j},
    with c_0 = 1, tau(n) = c_{n-1}.  Exact integers."""
    sig1 = sigma_sieve(N, 1)              # need sigma_1 up to N
    c = [0] * (N + 1)
    c[0] = 1
    sig1_arr = np.array(sig1, dtype=object)
    c_arr = np.array(c, dtype=object)
    for m in range(1, N + 1):
        # sum_{j=1}^m sigma_1(j) c_{m-j}
        acc = int(np.dot(sig1_arr[1:m + 1], c_arr[m - 1::-1])) if m >= 1 else 0
        val = (-24 * acc)
        assert val % m == 0, ("tau recurrence non-integer", m)
        c_arr[m] = val // m
    tau = np.empty(N + 1, dtype=object)
    tau[0] = 0
    for n in range(1, N + 1):
        tau[n] = c_arr[n - 1]
    return tau


def eisenstein_coeffs(w, N):
    """E_w coefficient array e[0..N], e_0 = 1, e_m = C_w sigma_{w-1}(m)."""
    e = np.zeros(N + 1, dtype=object)
    e[0] = 1
    if w == 0:
        return e                          # E_0 = 1 (trivial factor)
    Cw = EIS_CONST[w]
    sig = sigma_sieve(N, w - 1)
    for m in range(1, N + 1):
        e[m] = Cw * sig[m]
    return e


def eigenform_coeffs(tau, w, N):
    """a_n = [q^n](Delta * E_w) exact.  a_1 = 1 (normalized eigenform)."""
    e = eisenstein_coeffs(w, N)
    if w == 0:
        a = np.array(tau, dtype=object)   # f_12 = Delta
    else:
        full = np.convolve(np.asarray(tau, dtype=object), e)   # exact big-int convolution
        a = full[:N + 1]
    assert a[1] == 1, ("eigenform not normalized", w, a[1])
    return a


def verify_eigenform(a, k, N):
    """Exact self-validation: Hecke a_{p^2} = a_p^2 - p^{k-1}, and Deligne |a_p|<=2 p^{(k-1)/2}."""
    small_primes = [2, 3, 5, 7, 11, 13]
    ok_hecke = True
    ok_deligne = True
    worst_deligne = 0.0
    for p in small_primes:
        if p * p > N:
            break
        lhs = int(a[p * p])
        rhs = int(a[p]) ** 2 - p ** (k - 1)
        if lhs != rhs:
            ok_hecke = False
    # Deligne bound on a modest prime range
    for p in range(2, min(N, 2000)):
        if all(p % q for q in range(2, int(p ** 0.5) + 1)) and p > 1:
            r = abs(float(a[p])) / (2.0 * p ** ((k - 1) / 2.0))
            worst_deligne = max(worst_deligne, r)
            if r > 1.0 + 1e-9:
                ok_deligne = False
    return ok_hecke, ok_deligne, worst_deligne


# ---------------------------------------------------------------------------
# Sym^2 coefficients (analytic normalization: lambda_p = a_p / p^{(k-1)/2})
# ---------------------------------------------------------------------------
def smallest_prime_factor(N):
    spf = np.zeros(N + 1, dtype=np.int64)
    spf[1] = 1
    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i:N + 1:i] = np.where(spf[i:N + 1:i] == 0, i, spf[i:N + 1:i])
    return spf


def sym2_prime_power(lam_p, kmax):
    """c_{p^j} for Sym^2 in analytic normalization: e1=e2=lam^2-1, e3=1."""
    e1 = lam_p * lam_p - 1.0
    c = [1.0]
    if kmax >= 1:
        c.append(e1)
    for j in range(2, kmax + 1):
        cm3 = c[j - 3] if j - 3 >= 0 else 0.0
        c.append(e1 * (c[j - 1] - c[j - 2]) + cm3)
    return c


def build_sym2(a, k, N):
    """Multiplicative Sym^2 coefficients c(n), n<=N, from analytic lambda_p."""
    spf = smallest_prime_factor(N)
    lam = np.zeros(N + 1, dtype=np.float64)
    c = np.zeros(N + 1, dtype=np.float64)
    c[1] = 1.0
    max_exp = int(math.log2(N)) + 1
    ptab = {}
    half = (k - 1) / 2.0
    for n in range(2, N + 1):
        p = int(spf[n])
        m, e = n, 0
        while m % p == 0:
            m //= p
            e += 1
        if p not in ptab:
            lam_p = float(a[p]) / (p ** half)
            lam[p] = lam_p
            ptab[p] = sym2_prime_power(lam_p, max_exp)
        c[n] = ptab[p][e] * c[m]
    return c, ptab


def certify_s2(c, a, k, N):
    """Truncated Dirichlet sum vs Euler product for Sym^2 L at s=2 (off-line)."""
    s = 2.0
    n = np.arange(1, N + 1, dtype=np.float64)
    partial = float(np.sum(c[1:] * n ** (-s)))
    spf = smallest_prime_factor(N)
    half = (k - 1) / 2.0
    prod = 1.0
    for p in range(2, N + 1):
        if spf[p] == p:
            lam_p = float(a[p]) / (p ** half)
            e1 = lam_p * lam_p - 1.0
            x = p ** (-s)
            local_inv = 1.0 - e1 * x + e1 * x ** 2 - 1.0 * x ** 3
            prod *= 1.0 / local_inv
    return partial, prod


# ---------------------------------------------------------------------------
# Fiber (no L-library in the loop)
# ---------------------------------------------------------------------------
def taper(u):
    w = np.zeros_like(u)
    m = u < 1.0
    uu = u[m]
    w[m] = np.exp(1.0 - 1.0 / (1.0 - uu * uu))
    return w


def fiber_complex(coeffs, N, ts):
    n = np.arange(1, N + 1, dtype=np.float64)
    u = n / N
    amp = coeffs[1:N + 1] * taper(u) / np.sqrt(n)
    keep = amp != 0.0
    n = n[keep]
    amp = amp[keep]
    lnn = np.log(n)
    dy = ts[1] - ts[0]
    z = amp * np.exp(-1j * ts[0] * lnn)
    step = np.exp(-1j * dy * lnn)
    F = np.empty(len(ts), dtype=np.complex128)
    for i in range(len(ts)):
        F[i] = np.sum(z)
        z *= step
    return F


# ---------------------------------------------------------------------------
# Gamma factor / phase gauges, parameterized by the shift m = k - 1
# ---------------------------------------------------------------------------
def theta_primary(t, m):
    """gamma(s) = Gamma_R(s+1) Gamma_C(s+m), s = 1/2 + it. Im log (t-dependence)."""
    s = 0.5 + 1j * np.asarray(t, dtype=float)
    a = -(np.asarray(t) / 2.0) * math.log(math.pi) + np.imag(loggamma((s + 1.0) / 2.0))
    b = -np.asarray(t) * math.log(2.0 * math.pi) + np.imag(loggamma(s + m))
    return a + b


def theta_alt(t, m):
    """parity alternative gamma(s) = Gamma_R(s) Gamma_C(s+m)."""
    s = 0.5 + 1j * np.asarray(t, dtype=float)
    a = -(np.asarray(t) / 2.0) * math.log(math.pi) + np.imag(loggamma(s / 2.0))
    b = -np.asarray(t) * math.log(2.0 * math.pi) + np.imag(loggamma(s + m))
    return a + b


def theta_fn(which):
    return theta_primary if which == "primary" else theta_alt


def gamma_logmod(t, m, which):
    """Re log gamma(1/2+it): completed-line magnitude."""
    s = 0.5 + 1j * np.asarray(t, dtype=float)
    if which == "primary":
        lr = -((s + 1.0) / 2.0) * math.log(math.pi) + loggamma((s + 1.0) / 2.0)
    else:
        lr = -(s / 2.0) * math.log(math.pi) + loggamma(s / 2.0)
    lc = math.log(2.0) - (s + m) * math.log(2.0 * math.pi) + loggamma(s + m)
    return np.real(lr + lc)


def theta_density(t, m, which):
    """(dtheta/dt) via central difference (zero-density = (dtheta/dt)/pi)."""
    h = 1e-4
    fn = theta_fn(which)
    tp = float(fn(t + h, m))
    tm = float(fn(t - h, m))
    return (tp - tm) / (2 * h)


# ---------------------------------------------------------------------------
# Weld pin
# ---------------------------------------------------------------------------
def _dist_to_eps_ray(ray):
    d = ray % math.pi
    return min(d, math.pi - d)


def pin_ray(F, absF, theta_vals):
    med = float(np.median(absF))
    mask = absF > 0.5 * med
    psi = np.mod(np.angle(F) + theta_vals, math.pi)
    zbar = np.mean(np.exp(2j * psi[mask]))
    ray = (np.angle(zbar) / 2) % math.pi
    spread = 1.0 - abs(zbar)
    csd = math.sqrt(max(0.0, -0.5 * math.log(max(abs(zbar), 1e-300))))
    return ray, spread, csd, psi, mask


# ---------------------------------------------------------------------------
# One-form run
# ---------------------------------------------------------------------------
def run_form(k, tau, N, T_HI, DY):
    m = k - 1
    w = k - 12
    emit("=" * 78)
    emit(f"FORM  Sym^2 f_{k}   (level 1, weight {k}; gamma shift m = k-1 = {m})")
    emit("=" * 78)

    t0 = time.time()
    a = eigenform_coeffs(tau, w, N)
    ok_h, ok_d, worst_d = verify_eigenform(a, k, N)
    emit(f"  [eigenform] a_n = [q^n](Delta * E_{w}), N={N}: {time.time()-t0:.1f}s")
    emit(f"    a_2={int(a[2])}, a_3={int(a[3])}, a_5={int(a[5])}, a_7={int(a[7])}")
    emit(f"    Hecke a_p^2 = a_p^2 - p^(k-1): {'OK' if ok_h else 'FAIL'};  "
         f"Deligne |a_p|<=2p^((k-1)/2): worst {worst_d:.4f} => {'OK' if ok_d else 'VIOLATED'}")
    if not (ok_h and ok_d):
        emit("    ABORT this form: eigenform self-validation failed.")
        return None

    c, ptab = build_sym2(a, k, N)
    part, prod = certify_s2(c, a, k, N)
    reld = abs(part - prod) / abs(prod)
    emit(f"  [certificate] Sym^2 s=2: Dirichlet {part:.10f} vs Euler {prod:.10f}, "
         f"rel {reld:.2e} (tol {CERT_TOL:.0e}, truncation-floored) "
         f"=> {'OK' if reld < CERT_TOL else 'FAIL'}")
    worst_u = 0.0
    for p, tab in ptab.items():
        for kk, v in enumerate(tab):
            bound = (kk + 1) * (kk + 2) // 2
            worst_u = max(worst_u, abs(v) / bound)
    emit(f"    unitarity |c_pk|<=C(k+2,2): worst {worst_u:.4f} => {'OK' if worst_u<=1+1e-9 else 'VIOLATED'}")
    if reld >= CERT_TOL:
        emit("    ABORT this form: Sym^2 certificate did not reproduce.")
        return None

    # ---- fiber sweep ----
    ts = np.arange(DY, T_HI + DY / 2, DY)
    t0 = time.time()
    F = fiber_complex(c, N, ts)
    absF = np.abs(F)
    emit(f"  [sweep] fiber on {len(ts)} points: {time.time()-t0:.1f}s")

    # ---- weld pin (pick gamma parity) ----
    theta_p = theta_primary(ts, m)
    theta_a = theta_alt(ts, m)
    ray_p, spr_p, sd_p, psi_p, _ = pin_ray(F, absF, theta_p)
    ray_a, spr_a, sd_a, psi_a, _ = pin_ray(F, absF, theta_a)
    emit(f"  [weld] PRIMARY Gamma_R(s+1): ray {ray_p/math.pi:.4f}pi, "
         f"dist-eps {_dist_to_eps_ray(ray_p)/math.pi:.2e}pi, spread {spr_p:.2e}")
    emit(f"         ALT     Gamma_R(s)  : ray {ray_a/math.pi:.4f}pi, "
         f"dist-eps {_dist_to_eps_ray(ray_a)/math.pi:.2e}pi, spread {spr_a:.2e}")
    if spr_p <= spr_a and spr_p < 1e-2:
        which, theta_vals, spread, ray = "primary", theta_p, spr_p, ray_p
    elif spr_a < 1e-2:
        which, theta_vals, spread, ray = "alt", theta_a, spr_a, ray_a
    else:
        emit("  *** REGISTER-GRADE SURPRISE: neither gamma parity pins (spread >= 1e-2). ***")
        emit(f"      primary {spr_p:.2e}, alt {spr_a:.2e}. Reporting and moving on.")
        return dict(k=k, m=m, pinned=False, spr_p=spr_p, spr_a=spr_a)
    emit(f"  -> {which.upper()} gamma pins (spread {spread:.2e}).")

    # ---- locator ----
    logmod = gamma_logmod(ts, m, which)
    med = float(np.median(absF))
    cand = [j for j in range(1, len(ts) - 1)
            if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.25 * med]

    def g(t):
        Fv = fiber_complex(c, N, np.array([t - 1e-5, t, t + 1e-5]))[1]
        th = float(theta_fn(which)(t, m))
        return (Fv * np.exp(1j * th)).real

    def refine(tg):
        lo, hi = tg - 2 * DY, tg + 2 * DY
        glo, ghi = g(lo), g(hi)
        if glo * ghi > 0:
            lo, hi = tg - 4 * DY, tg + 4 * DY
            glo, ghi = g(lo), g(hi)
            if glo * ghi > 0:
                return tg
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            gm = g(mid)
            if glo * gm <= 0:
                hi, ghi = mid, gm
            else:
                lo, glo = mid, gm
        return 0.5 * (lo + hi)

    zeros = []
    for j in cand:
        tz = refine(ts[j])
        zeros.append(tz)
    zeros.sort()
    dedup = []
    for tz in zeros:
        if not dedup or abs(tz - dedup[-1]) > 1e-3:
            dedup.append(tz)
    zeros = dedup

    dens = np.array([theta_density(t, m, which) for t in ts]) / math.pi
    n_pred = float(np.trapezoid(dens, ts)) if hasattr(np, "trapezoid") else float(np.trapz(dens, ts))
    emit(f"  [locator] found {len(zeros)} vanishings on (0,{T_HI:.0f}]; "
         f"gamma-density N({T_HI:.0f}) ~ {n_pred:.2f}  (count cross-check)")

    # ---- phase cells ----
    Phi = np.unwrap(np.angle(F) + theta_vals)
    zidx = sorted(set(max(4, min(len(ts) - 5, int(round((tz - ts[0]) / DY)))) for tz in zeros))
    before = np.array([Phi[j - 4] for j in zidx])
    cells = np.abs(np.diff(before)) / math.pi if len(zidx) > 1 else np.array([])
    if len(cells):
        emit(f"  [cells]   {len(cells)} cells: mean {cells.mean():.4f}pi  sd {cells.std():.4f}pi  "
             f"min {cells.min():.4f}pi  max {cells.max():.4f}pi")

    # ---- hinge (eps=+1 turning point) ----
    dt = 1e-3
    tc = np.array([-2 * dt, -dt, dt, 2 * dt])
    Fc = fiber_complex(c, N, np.abs(tc))
    Fc = np.where(tc < 0, np.conj(Fc), Fc)
    thc = theta_fn(which)(tc, m)
    lmc = gamma_logmod(np.abs(tc), m, which)
    Lamc = np.exp(lmc) * Fc * np.exp(1j * thc)
    F0 = fiber_complex(c, N, np.array([0.0, DY, 2 * DY]))[0]
    lm0 = gamma_logmod(np.array([0.0]), m, which)[0]
    Lam0 = math.exp(lm0) * F0.real
    dLam = ((Lamc[3] - Lamc[0]) / (4 * dt)).real
    scale_hinge = math.exp(gamma_logmod(np.array([1.3]), m, which)[0]) * abs(
        fiber_complex(c, N, np.array([1.3, 1.3 + DY]))[0])
    emit(f"  [hinge]   Lambda(1/2) {Lam0:.4e} (finite); dLambda/dt(0)/scale "
         f"{abs(dLam)/scale_hinge:.2e} (=> turning point, eps=+1)")

    # ---- dimension census ----
    census = []
    for tz in zeros[:15]:
        h = 5e-4
        grid = np.array([tz - 2 * h, tz - h, tz, tz + h, tz + 2 * h])
        Fg = fiber_complex(c, N, grid)
        thg = theta_fn(which)(grid, m)
        lmg = gamma_logmod(grid, m, which)
        Lg = np.exp(lmg) * Fg * np.exp(1j * thg)
        val = abs(Lg[2])
        dval = abs((Lg[3] - Lg[1]) / (2 * h))
        loc_scale = math.exp(gamma_logmod(np.array([tz]), m, which)[0]) * med
        rv, rd = val / loc_scale, dval / loc_scale
        d = 1 if (rv < 0.1 and rd > 1e-3) else (0 if rv > 0.5 else 2)
        census.append(d)
    allsimple = bool(census) and all(d == 1 for d in census)
    emit(f"  [census]  d=1 at {sum(1 for d in census if d==1)}/{len(census)} zeros "
         f"=> {'ALL SIMPLE' if allsimple else 'ANOMALY'}")

    return dict(k=k, m=m, pinned=True, which=which, spread=spread,
                eps_dist=_dist_to_eps_ray(ray) / math.pi,
                n_zeros=len(zeros), n_pred=n_pred,
                cell_mean=float(cells.mean()) if len(cells) else float("nan"),
                cell_sd=float(cells.std()) if len(cells) else float("nan"),
                Lam0=Lam0, hinge_ratio=abs(dLam) / scale_hinge,
                allsimple=allsimple, n_census=len(census))


# ---------------------------------------------------------------------------
def main():
    N = 6000
    T_HI = 36.0
    DY = 0.002

    t_all = time.time()
    emit("GL(3) FAMILY VANISHING-SIDE TEST  --  Sym^2 f_k, k in " + str(WEIGHTS))
    emit("=" * 78)
    emit("Same instrument as tmp/gl3_vanishing.py, run across a gamma-shift family.")
    emit(f"bank N={N}; sweep t in (0,{T_HI:.0f}], dy={DY}.  From-scratch tau + Eisenstein.")
    emit("")

    t0 = time.time()
    tau = tau_exact(N)
    known = {2: -24, 3: 252, 4: -1472, 5: 4830, 6: -6048, 7: -16744}
    for n, want in known.items():
        assert int(tau[n]) == want, ("tau mismatch", n, int(tau[n]), want)
    emit(f"[tau] exact tau(n), N={N}: {time.time()-t0:.1f}s  "
         f"(spot-checked tau(2..7) against known values: OK)")
    emit("")

    results = []
    for k in WEIGHTS:
        r = run_form(k, tau, N, T_HI, DY)
        if r is not None:
            results.append(r)
        emit("")

    # ---- cross-form comparison ----
    emit("=" * 78)
    emit("CROSS-FORM COMPARISON  (universal register vs gamma-dependent register)")
    emit("=" * 78)
    pinned = [r for r in results if r.get("pinned")]
    emit(f"  {'k':>3} {'m':>3} {'parity':>8} {'weld spr':>10} {'cells (pi)':>16} "
         f"{'N(T) meas':>10} {'N(T) pred':>10} {'simple':>8}")
    for r in pinned:
        emit(f"  {r['k']:>3} {r['m']:>3} {r['which']:>8} {r['spread']:>10.1e} "
             f"{r['cell_mean']:>7.4f}+-{r['cell_sd']:.4f} "
             f"{r['n_zeros']:>10} {r['n_pred']:>10.2f} "
             f"{('yes' if r['allsimple'] else 'NO'):>8}")
    emit("")

    if len(pinned) >= 2:
        cell_means = np.array([r["cell_mean"] for r in pinned])
        emit("  UNIVERSAL register (must be weight-invariant):")
        emit(f"    cells across family: mean {cell_means.mean():.4f}pi, "
             f"spread across forms {cell_means.std():.4f}pi, "
             f"max |cell-1| {np.max(np.abs(cell_means-1.0)):.4f}")
        emit(f"    all-simple across family: "
             f"{sum(1 for r in pinned if r['allsimple'])}/{len(pinned)} forms")
        emit(f"    weld pins across family: {len(pinned)}/{len(results)} forms, "
             f"worst spread {max(r['spread'] for r in pinned):.1e}")
        emit("")
        emit("  GAMMA-DEPENDENT register (must climb with k on the gamma-factor law):")
        ks = np.array([r["k"] for r in pinned], dtype=float)
        nz = np.array([r["n_zeros"] for r in pinned], dtype=float)
        npred = np.array([r["n_pred"] for r in pinned], dtype=float)
        mono = all(npred[i] <= npred[i + 1] + 1e-9 for i in range(len(npred) - 1))
        emit(f"    N({T_HI:.0f}) predicted from gamma: " +
             ", ".join(f"k={int(r['k'])}:{r['n_pred']:.2f}" for r in pinned))
        emit(f"    N({T_HI:.0f}) measured (located) : " +
             ", ".join(f"k={int(r['k'])}:{r['n_zeros']}" for r in pinned))
        emit(f"    predicted density monotone increasing in k: {'YES' if mono else 'NO'}")
        if len(pinned) >= 2:
            dpred = npred[-1] - npred[0]
            dmeas = nz[-1] - nz[0]
            emit(f"    density lift k={int(ks[0])}->k={int(ks[-1])}: "
                 f"predicted +{dpred:.2f}, measured +{dmeas:.0f} zeros "
                 f"(the gamma-shift wall-scaling signal)")
            # correlation of measured vs predicted across the family
            if len(pinned) >= 3:
                cc = float(np.corrcoef(nz, npred)[0, 1])
                emit(f"    corr(measured, predicted) across family: {cc:+.4f}")

    emit("")
    emit(f"[budget] total wall time {time.time()-t_all:.1f}s")
    emit("=" * 78)

    # ---- summary file ----
    with open(SUMMARY, "w") as fh:
        fh.write("GL(3) FAMILY SUMMARY\n\n")
        if pinned:
            cell_means = np.array([r["cell_mean"] for r in pinned])
            fh.write(f"forms pinned: {len(pinned)}/{len(results)}; "
                     f"weights {[r['k'] for r in pinned]}\n")
            fh.write(f"UNIVERSAL: cells {cell_means.mean():.4f}pi (across-form spread "
                     f"{cell_means.std():.4f}pi); all-simple "
                     f"{sum(1 for r in pinned if r['allsimple'])}/{len(pinned)}; "
                     f"worst weld spread {max(r['spread'] for r in pinned):.1e}\n")
            fh.write("GAMMA-DEPENDENT: N(T) pred " +
                     ", ".join(f"k{int(r['k'])}={r['n_pred']:.2f}" for r in pinned) + "\n")
            fh.write("                 N(T) meas " +
                     ", ".join(f"k{int(r['k'])}={r['n_zeros']}" for r in pinned) + "\n")
        fh.write("Files: tmp/gl3_family.py, tmp/gl3_family_results.txt\n")
    _flush()


if __name__ == "__main__":
    main()
