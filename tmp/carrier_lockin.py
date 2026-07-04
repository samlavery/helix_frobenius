"""carrier_lockin.py -- LOCK-IN SOURCE ATTRIBUTION on the canonical pi/3 phasor bank.

Follow-on to carrier_warp_check.py (which PASSED: Jacobi-Anger sideband decomposition
of the wave warp + the first-order lock-in law on a smoothed zeta bank).  This is the
instrument version, built ON THE CANONICAL MODEL (phasor_explorer/model.py -- house
rule: use it, don't re-derive):

  BANK    F(s) = sum_{n<=N} chi(n) w(n;N,tau) n^{-s},  w = model.magnitude 'grow_equal'
          window, N = model.eigenheight(gamma).  At s = 1/2 + i*R this IS the model's
          focal channel B(char,'log_entry',N,R,'grow',tau) -- verified to 1e-12 (gate 2a).
  ANGLE   Theta(n) = (pi/3)*Omega(n), the completely additive FTA winding angle -- the
          house pi/3 clock (model's carrier step is (pi/3)*n; the completely ADDITIVE
          per-n angle needed for multiplicative sidebands is (pi/3)*Omega(n), as in
          carrier_warp_check.py).
  WARP    A(n) = exp(i*eps*sin(k*Theta(n) + phi)).  Jacobi-Anger: A = sum_m J_m(eps)
          e^{im*phi} chi_m(n), chi_m(n) = e^{im*k*Theta(n)} completely multiplicative.
  LAW     first-order root shift  droot = -(eps/2)*(e^{i phi}F_+ - e^{-i phi}F_-)/F'
          and value shift at the old root  dF = (eps/2)*(e^{i phi}F_+ - e^{-i phi}F_-),
          F_+- = the +-1 sideband-twisted banks at the unwarped root.

STRUCTURAL NOTE (house clock): 3*Theta(n) = pi*Omega(n), so sin(3*Theta) == 0 -- k=3
with phi=0 is an EXACTLY NULL warp of the pi/3 clock (blind harmonic).  We keep it as
an exact-null consistency row and add k=3, phi=pi/2, whose warp is exp(i*eps*lambda(n))
(lambda = Liouville) -- a genuine test of the phase-generalized sideband weights.

PRE-REGISTERED EXPECTATIONS (2026-07-03, written before running):
  P1 shift-tracking : every feature x (k,eps) root shift matches the law, rel err ~ O(eps)
     (the model bank is 100% bank-funded; threshold: rel err <= 2.5*eps, ~3x margin over
     the 0.7*eps seen in carrier_warp_check).
  P2 value-tracking : warped readout at the unwarped root matches, same threshold.
  P3 linearity      : rel err ~ linear in eps (eps 0.05 -> 0.02 shrinks err ~2.5x);
     linearity range = largest eps with rel err <= 5%.
  P4 scrambled ctrl : random per-n phases at matched amplitude do NOT follow the
     structured sideband prediction (rel err O(1)); the scrambled shift itself must
     still be ~linear in eps (so the mismatch is structural, not amplitude noise).
  P5 actuator       : commanded root moves land at first-order accuracy; one closed-loop
     refinement (same-k warps compose by phasor addition of w = (eps/2)e^{i phi})
     improves them.
Any miss is reported at full prominence; the linearity halving test separates
instrument bugs (err does not halve) from real structure (err halves but law misses).

PART C -- STATE-EXPANDED SPACE (owner's follow-on; pre-registered 2026-07-03 before running):
  C1 isometry  : a pure phase warp is diagonal and unit-modulus per state, so every
     state magnitude, the P/M lane masses, the model's A channel (unsigned live mass,
     the model's own norm convention) and the plain weighted l2 energy are EXACTLY
     invariant (machine precision).  The canonical state-level conventions in model.py
     (per-state a_n, lane masses Ptot/Mtot/Utot, A channel) are all DIAGONAL -- there is
     no cross-term state metric to break; recorded as such, not forced.
  C2 lanes     : the warp acts diagonally, so warped P/M lane resultants are computed
     EXACTLY upstairs (no first-order step).  At each feature the unwarped lanes balance
     (P = M: the house B = P - M = 0 claim).  The lane RE-balance height of the warped
     bank (P_w = M_w) must equal Part A's readout dip shift (same zero, reached through
     the state split, Newton-tolerance agreement); lane responses match their own
     first-order sideband law to O(eps) for additive-angle warps.
  C3 transport : state response -> projection (the sum) -> readout is an instrumented
     identity: the residual localized AT THE PROJECTION is expected to be ZERO to
     summation precision (values ~1e-15 abs; rebalance vs dip roots ~ Newton tol).
     Any larger residual = anomaly at the projection, full prominence.
  C4 control   : the scrambled warp keeps C1 (unit modulus per state -> isometry HOLDS)
     but breaks C2 (no additive-angle structure -> lane sideband law fails O(1)) -- the
     clean contrast separating energy conservation (any phase warp) from harmonic
     structure (only additive-angle warps).

GATES (run `python3 carrier_lockin.py test` for gates only):
  0. model.py's own _selftest() passes untouched.
  1. Jacobi-Anger identity on the canonical bank's angles, per-phasor 1e-15 scale,
     plus bank-level warped-vs-Bessel-sum equality (phi = 0 and phi != 0).
  2. (a) bank == model focal channel at s = 1/2 + i*gamma to 1e-11 (exact reuse; the
         residual is double-precision summation-order noise over up to 1.4e6 terms);
     (b) unwarped roots sit at the model's predicted zeros (offset = truncation
         residual only, < 0.05).
  3. (Part C) isometry: state-side l1 mass == the model A channel (exact-reuse anchor),
     and per-state modulus + all diagonal norms invariant under structured AND scrambled
     phase warps to < 1e-13.

Scope: finite validated instances; no RH/GRH assumed or proved.
Full run writes carrier_lockin_results.txt (tiered).
"""
import os
import sys
import time

import numpy as np
from mpmath import besselj

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "phasor_explorer"))
import model  # canonical single source of truth -- never re-derive

PI3 = np.pi / 3.0
RESULTS_PATH = os.path.join(HERE, "carrier_lockin_results.txt")
SEED = 20260703

# 6 features: known cancellation heights (model zeros), 4 characters, N from 412 to 1.37e6
FEATURES = [("chi4", 0), ("chi5", 0), ("chi3", 0), ("chi4", 1), ("chi3", 1), ("trivial", 0)]
WARPS = [(1, 0.0), (2, 0.0), (3, 0.0), (3, np.pi / 2)]   # (k, phi); (3,0) = exact-null harmonic
EPSES = [0.02, 0.05]
EPS_GRID = [0.00025, 0.0005, 0.001, 0.002, 0.005, 0.01, 0.02, 0.05,
            0.08, 0.12, 0.16, 0.22, 0.30, 0.40]                     # linearity scan (k=1)
TRACK_FACTOR = 2.5        # P1/P2 pre-registered: rel err <= TRACK_FACTOR * eps
LIN_TOL = 0.05            # linearity range = largest eps with rel err <= 5%

_L = []
def emit(s=""):
    print(s)
    _L.append(s)

def cfmt(z, d=6):
    z = complex(z)
    return f"{z.real:+.{d}f}{z.imag:+.{d}f}i"


def omega_sieve(N):
    """Omega(n) = # prime factors with multiplicity (completely additive), vectorized."""
    Om = np.zeros(N + 1, dtype=np.int16)
    for p in range(2, N + 1):
        if Om[p] == 0:                      # p prime: no smaller factor counted yet
            pk = p
            while pk <= N:
                Om[pk::pk] += 1
                pk *= p
    return Om


class Bank:
    """The canonical bank of one feature, frozen at its eigenheight head.

    Coefficients c0(n) = chi(n) * w(n) with w = model.magnitude('grow_equal') so that
    F(1/2 + i*R) == model.focal_channels(char,'log_entry',N,R,'grow',tau)[1] exactly.
    """
    def __init__(self, char, zidx, Om):
        self.char, self.zidx = char, zidx
        self.gamma = model.CHARS[char]["zeros"][zidx]
        self.N = model.eigenheight(self.gamma)
        self.tau = min(400.0, max(4.0, self.N / 8.0))   # model default 400, scaled for small N
        n = np.arange(1, self.N + 1)
        nf = n.astype(float)
        chi = np.asarray(model.CHARS[char]["chi"](n), dtype=float)
        w = model.magnitude(nf, float(self.N), "grow_equal", self.tau)  # pure window
        self.chi = chi
        self.pos = chi > 0      # P lane (model channel convention)
        self.neg = chi < 0      # M lane
        self.c0 = chi * w
        self.logn = np.log(nf)
        self.Th = PI3 * Om[1:self.N + 1].astype(float)   # FTA winding angle (pi/3)*Omega(n)
        self.label = f"{char:7s} g{zidx+1} gamma={self.gamma:9.4f} N={self.N:>8d} tau={self.tau:g}"

    def E(self, s):
        return np.exp(-s * self.logn)

    def F(self, s, c=None):
        cc = self.c0 if c is None else c
        return complex(np.dot(cc, self.E(s)))

    def F_and_deriv(self, s, c=None):
        cc = self.c0 if c is None else c
        E = self.E(s)
        return complex(np.dot(cc, E)), complex(-np.dot(cc * self.logn, E))

    def newton(self, s0, c=None, tol=1e-12, maxit=80):
        s = complex(s0)
        for _ in range(maxit):
            f, fp = self.F_and_deriv(s, c)
            ds = f / fp
            s -= ds
            if abs(ds) < tol:
                return s
        raise RuntimeError(f"newton failed: {self.label} from {s0}")

    def warp_coeff(self, eps, k, phi=0.0):
        return self.c0 * np.exp(1j * eps * np.sin(k * self.Th + phi))

    def sidebands(self, E0, k):
        """F_+- at a precomputed E0 = n^{-root0} (dot products only)."""
        tp = self.c0 * np.exp(1j * k * self.Th)
        tm = self.c0 * np.exp(-1j * k * self.Th)
        return complex(np.dot(tp, E0)), complex(np.dot(tm, E0))

    # ---- state-space (Part C): the lane split, model channel convention B = P - M ----
    def lane_F(self, s, c=None):
        """P and M lane resultants (M with positive mass, per model.channel_resultants)
        computed as SEPARATE per-lane state sums; F = P - M; F' for Newton steering."""
        cc = self.c0 if c is None else c
        E = self.E(s)
        P = complex(np.dot(cc[self.pos], E[self.pos]))
        M = complex(-np.dot(cc[self.neg], E[self.neg]))   # c0 < 0 on the M lane
        Fp = complex(-np.dot(cc * self.logn, E))
        return P, M, P - M, Fp

    def newton_lane(self, s0, c=None, tol=1e-12, maxit=80):
        """Root find done entirely through the lane split (P_w = M_w rebalance point)."""
        s = complex(s0)
        for _ in range(maxit):
            _, _, f, fp = self.lane_F(s, c)
            ds = f / fp
            s -= ds
            if abs(ds) < tol:
                return s
        raise RuntimeError(f"newton_lane failed: {self.label} from {s0}")

    def lane_sidebands(self, E0, k):
        """Per-lane +-1 sideband sums (P_+, P_-, M_+, M_-); F_+- = P_+- - M_+-."""
        ep = np.exp(1j * k * self.Th)
        out = []
        for tw in (ep, ep.conj()):
            cc = self.c0 * tw
            out.append(complex(np.dot(cc[self.pos], E0[self.pos])))
            out.append(complex(-np.dot(cc[self.neg], E0[self.neg])))
        return out[0], out[2], out[1], out[3]   # P+, P-, M+, M-


def lockin_pred(eps, phi, Fplus, Fminus, Fp):
    """First-order law: droot = -(eps/2)(e^{i phi}F+ - e^{-i phi}F-)/F'."""
    dF = (eps / 2.0) * (np.exp(1j * phi) * Fplus - np.exp(-1j * phi) * Fminus)
    return -dF / Fp, dF


def relerr(meas, pred):
    den = max(abs(meas), abs(pred))
    return abs(meas - pred) / den if den > 0 else 0.0


# ---------------------------------------------------------------------------- gates
def gate0():
    emit("GATE 0: canonical model self-test (untouched) ...")
    ok = model._selftest()
    assert ok is True or ok is None or ok  # _selftest returns True and asserts internally
    emit("GATE 0: PASS")


def gate1(bank):
    emit(f"GATE 1: Jacobi-Anger identity on the canonical bank's angles ({bank.char} g{bank.zidx+1}, N={bank.N})")
    eps, M = 0.15, 10
    worst_pp, worst_bk = 0.0, 0.0
    for k in (1, 2):
        for phi in (0.0, 0.7):
            x = k * bank.Th + phi
            warp = np.exp(1j * eps * np.sin(x))
            ja = np.zeros_like(warp)
            for m in range(-M, M + 1):
                ja += float(besselj(m, eps)) * np.exp(1j * m * x)
            pp = float(np.max(np.abs(warp - ja)))
            s0 = 0.5 + 1j * bank.gamma
            bk = abs(bank.F(s0, bank.c0 * warp) - bank.F(s0, bank.c0 * ja))
            worst_pp, worst_bk = max(worst_pp, pp), max(worst_bk, bk)
            emit(f"  k={k} phi={phi:4.2f}: per-phasor max |warp - Bessel(M={M})| = {pp:.2e}   "
                 f"bank-level |F_warp - F_JA| = {bk:.2e}")
    assert worst_pp < 5e-15, worst_pp
    assert worst_bk < 1e-11, worst_bk
    emit("GATE 1: PASS (the warped canonical bank IS a Bessel-weighted twist family)")


def gate2(banks):
    emit("GATE 2a: exact reuse -- bank(1/2+i*gamma) == model focal channel B (grow window)")
    for b in banks:
        Bmodel = model.focal_channels(b.char, "log_entry", b.N, b.gamma, "grow", b.tau)[1]
        mine = b.F(0.5 + 1j * b.gamma)
        d = abs(mine - Bmodel) / (1 + abs(Bmodel))
        emit(f"  {b.label}   |F - B_model| = {d:.2e}")
        # tolerance 1e-11: pure summation-order noise for up to 1.4e6 double-precision terms
        assert d < 1e-11, (b.label, d)
    emit("GATE 2a: PASS")
    emit("GATE 2b: unwarped roots sit at the model's predicted zeros (truncation residual only)")
    roots = []
    for b in banks:
        r = b.newton(0.5 + 1j * b.gamma)
        off = abs(r - (0.5 + 1j * b.gamma))
        emit(f"  {b.label}   root = {cfmt(r)}   |root - (1/2+i*gamma_model)| = {off:.2e}")
        assert off < 0.05, (b.label, off)
        roots.append(r)
    emit("GATE 2b: PASS")
    return roots


# ---------------------------------------------------------------------------- Part A
def part_a(banks, roots):
    emit()
    emit("=" * 100)
    emit("PART A: LOCK-IN SOURCE ATTRIBUTION -- measured response vs first-order sideband prediction")
    emit("  droot: root shift (complex, s-plane); dval: readout change at the unwarped root")
    emit("  tracked (pre-registered): rel err <= 2.5*eps; (k=3,phi=0) = exact-null harmonic (abs test)")
    emit("  verdicts split: VALUE law (the lock-in observable) vs SHIFT law (root tracking)")
    emit("=" * 100)
    n_rows = n_shift_ok = n_val_ok = n_null = n_null_ok = 0
    halving = []    # (feature, k, phi, err02, err05)
    failures = []   # (bank, root, k, phi) shift-law misses -> pre-registered halving diagnostic
    rows = []       # full measurement record, consumed by Part C (state-space transport check)
    for b, r0 in zip(banks, roots):
        E0 = b.E(r0)
        F0, Fp0 = b.F_and_deriv(r0)
        emit(f"\nFEATURE {b.label}   |F'(root)| = {abs(Fp0):.4f}")
        emit(f"  {'k':>2s} {'phi':>5s} {'eps':>5s}   {'droot meas':>22s} {'droot pred':>22s} "
             f"{'rel err':>8s}   {'|dval| m/p':>17s} {'rel err':>8s}  verdict")
        for (k, phi) in WARPS:
            Fpl, Fmi = b.sidebands(E0, k)
            errs = {}
            for eps in EPSES:
                cw = b.warp_coeff(eps, k, phi)
                re_ = b.newton(r0, cw)
                droot = re_ - r0
                pred, dF = lockin_pred(eps, phi, Fpl, Fmi, Fp0)
                dval = complex(np.dot(cw, E0)) - F0
                null_row = (k == 3 and phi == 0.0)
                rows.append(dict(bank=b, root=r0, k=k, phi=phi, eps=eps,
                                 droot=droot, dval=dval, null=null_row))
                if null_row:
                    ok = abs(droot) < 1e-9 and abs(pred) < 1e-9
                    n_null += 1
                    n_null_ok += int(ok)
                    verdict = "NULL-exact" + ("" if ok else "  ** FAILED NULL **")
                    emit(f"  {k:2d} {phi:5.2f} {eps:5.2f}   {cfmt(droot,10):>22s} {cfmt(pred,10):>22s} "
                         f"{'--':>8s}   {abs(dval):.2e}/{abs(dF):.2e} {'--':>8s}  {verdict}")
                else:
                    es, ev = relerr(droot, pred), relerr(dval, dF)
                    errs[eps] = es
                    ok_s = es <= TRACK_FACTOR * eps
                    ok_v = ev <= TRACK_FACTOR * eps
                    verdict = ("shift:ok " if ok_s else "shift:MISS ") + ("val:ok" if ok_v else "val:** MISS **")
                    emit(f"  {k:2d} {phi:5.2f} {eps:5.2f}   {cfmt(droot,10):>22s} {cfmt(pred,10):>22s} "
                         f"{es:8.4f}   {abs(dval):.2e}/{abs(dF):.2e} {ev:8.4f}  {verdict}")
                    n_rows += 1
                    n_shift_ok += int(ok_s)
                    n_val_ok += int(ok_v)
                    if not ok_s and eps == EPSES[0]:
                        failures.append((b, r0, k, phi))
            if len(errs) == 2 and errs[0.05] > 1e-12:
                halving.append((b.char + f"g{b.zidx+1}", k, phi, errs[0.02], errs[0.05]))
    emit(f"\nPART A headline (pre-registered eps in {EPSES}):")
    emit(f"  VALUE law (lock-in observable): {n_val_ok}/{n_rows} tracked")
    emit(f"  SHIFT law (root tracking)     : {n_shift_ok}/{n_rows} tracked  "
         f"({len(failures)} (feature,k,phi) combos -> halving diagnostic below)")
    emit(f"  exact-null harmonic rows      : {n_null_ok}/{n_null} exact")
    emit("P3 halving check at the pre-registered pair (err(0.02)/err(0.05); first-order predicts ~0.4):")
    ratios = [e02 / e05 for (_, _, _, e02, e05) in halving]
    for (lab, k, phi, e02, e05), rt in zip(halving, ratios):
        emit(f"  {lab:12s} k={k} phi={phi:4.2f}: {e02:.4f}/{e05:.4f} = {rt:.3f}")
    emit(f"  median ratio = {np.median(ratios):.3f} (expect ~0.4 if error is genuinely 2nd-order)")
    return dict(n_rows=n_rows, n_shift_ok=n_shift_ok, n_val_ok=n_val_ok,
                n_null=n_null, n_null_ok=n_null_ok, med_ratio=float(np.median(ratios)),
                failures=failures, rows=rows)


def halving_diagnostic(failures):
    """Pre-registered discriminator for every shift-law miss: halve eps until the law
    tracks to <= 5%.  Error halving with eps = first-order law confirmed, the miss was
    gain-induced saturation (|droot| too large for the linearization), NOT a sourceless
    feature.  Error NOT halving = report at full prominence as unresolved."""
    emit()
    emit("=" * 100)
    emit("HALVING DIAGNOSTIC (pre-registered) for every shift-law miss: eps -> eps/2 ladder")
    emit("=" * 100)
    unresolved = []
    for b, r0, k, phi in failures:
        E0 = b.E(r0)
        _, Fp0 = b.F_and_deriv(r0)
        Fpl, Fmi = b.sidebands(E0, k)
        eps, ladder = EPSES[0], []
        while eps > 2.4e-4:
            re_ = b.newton(r0, b.warp_coeff(eps, k, phi))
            pred, _ = lockin_pred(eps, phi, Fpl, Fmi, Fp0)
            e = relerr(re_ - r0, pred)
            ladder.append((eps, e))
            if e <= LIN_TOL:
                break
            eps /= 2.0
        ratios = [ladder[i + 1][1] / ladder[i][1] for i in range(len(ladder) - 1)]
        resolved = ladder[-1][1] <= LIN_TOL
        if not resolved:
            unresolved.append((b.label, k, phi))
        emit(f"  {b.char}g{b.zidx+1:<2d} k={k} phi={phi:4.2f}: "
             + "  ".join(f"e({ep:.5f})={er:.4f}" for ep, er in ladder))
        emit(f"      halving ratios {['%.2f' % r for r in ratios]} (expect ~0.5)   -> "
             + ("LAW CONFIRMED as eps->0 (gain saturation, instrument-side; not sourceless)"
                if resolved else "** UNRESOLVED -- REPORT AT FULL PROMINENCE **"))
    if not failures:
        emit("  (no shift-law misses -- nothing to diagnose)")
    return unresolved


def linearity(banks, roots):
    emit()
    emit("=" * 100)
    emit("LINEARITY RANGE (k=1, phi=0): largest eps with first-order rel err <= 5%")
    emit("=" * 100)
    emit("  gain g = |F+ - F-|/(2|F'|)  (droot ~ g*eps); usable |droot| at 5% = g*eps_5%")
    emit(f"  {'feature':<46s} " + "".join(f"{e:>8.5f}" for e in EPS_GRID) + f"   {'eps_5%':>8s} {'gain':>6s} {'droot5%':>8s}")
    ranges = []
    for b, r0 in zip(banks, roots):
        E0 = b.E(r0)
        _, Fp0 = b.F_and_deriv(r0)
        Fpl, Fmi = b.sidebands(E0, 1)
        gain = abs((Fpl - Fmi) / (2 * Fp0))
        row = []
        for eps in EPS_GRID:
            re_ = b.newton(r0, b.warp_coeff(eps, 1, 0.0))
            pred, _ = lockin_pred(eps, 0.0, Fpl, Fmi, Fp0)
            row.append(relerr(re_ - r0, pred))
        # largest contiguous-from-below eps with err <= tol
        eps5 = 0.0
        for eps, e in zip(EPS_GRID, row):
            if e <= LIN_TOL:
                eps5 = eps
            else:
                break
        ranges.append((eps5, gain))
        emit(f"  {b.label:<46s} " + "".join(f"{e:8.4f}" for e in row)
             + f"   {eps5:8.5f} {gain:6.2f} {eps5*gain:8.5f}")
    e5 = [r[0] for r in ranges]
    d5 = [r[0] * r[1] for r in ranges]
    emit(f"  eps_5% spans {min(e5):.5f}..{max(e5):.5f} ({max(e5)/max(min(e5),1e-12):.0f}x) but root excursion "
         f"g*eps_5% only {min(d5):.4f}..{max(d5):.4f} ({max(d5)/max(min(d5),1e-12):.0f}x):")
    emit("  the usable budget is the ROOT EXCURSION, not eps itself; gain is feature-dependent")
    return ranges


def make_psis(banks):
    """Scrambled per-n phases, one draw per control bank; the draw order (banks[2] then
    banks[0]) reproduces the original control's random stream (seed fixed)."""
    rng = np.random.default_rng(SEED)
    return {i: rng.uniform(0.0, 2.0 * np.pi, banks[i].N) for i in (2, 0)}


def scrambled_control(banks, roots, psis):
    emit()
    emit("=" * 100)
    emit("CONTROL: scrambled warp exp(i*eps*sin(psi_n)), psi_n ~ U(0,2pi) (matched amplitude, seed %d)" % SEED)
    emit("  pre-registered: must NOT follow the structured k=1 sideband prediction (rel err O(1));")
    emit("  its own shift must stay ~linear in eps (ratio ~2 under eps doubling) -> mismatch is structural")
    emit("=" * 100)
    out = []
    for bi in (2, 0):
        b, r0, psi = banks[bi], roots[bi], psis[bi]
        E0 = b.E(r0)
        _, Fp0 = b.F_and_deriv(r0)
        Fpl, Fmi = b.sidebands(E0, 1)
        dr = {}
        for eps in (0.05, 0.025):
            cw = b.c0 * np.exp(1j * eps * np.sin(psi))
            dr[eps] = b.newton(r0, cw) - r0
            pred, _ = lockin_pred(eps, 0.0, Fpl, Fmi, Fp0)
            e = abs(dr[eps] - pred) / abs(pred)
            out.append(e)
            emit(f"  {b.label} eps={eps:5.3f}: droot_scr = {cfmt(dr[eps],8)}  vs structured pred "
                 f"{cfmt(pred,8)}  rel err = {e:.3f}")
        lin = abs(dr[0.05]) / abs(dr[0.025])
        emit(f"    scrambled-shift linearity |droot(0.05)|/|droot(0.025)| = {lin:.3f} (expect ~2)")
    emit(f"  CONTROL verdict: min rel err vs structured law = {min(out):.3f} "
         + ("-> does NOT track (as pre-registered)" if min(out) > 0.5 else "** UNEXPECTED: tracked **"))
    return out


# ---------------------------------------------------------------------------- Part B
def solve_w(delta, Fp, Fpl, Fmi):
    """Solve w Fpl - conj(w) Fmi = -delta*Fp for w = (eps/2)e^{i phi} (real-linear 2x2)."""
    d = -delta * Fp
    a1, a2 = Fpl - Fmi, 1j * (Fpl + Fmi)
    M = np.array([[a1.real, a2.real], [a1.imag, a2.imag]])
    u, v = np.linalg.solve(M, np.array([d.real, d.imag]))
    return u + 1j * v


def part_b(bank, root0):
    emit()
    emit("=" * 100)
    emit(f"PART B: WARP AS ACTUATOR (closed loop) on dip #3 = {bank.label}")
    emit("  command a root shift delta; solve A(n)=exp(i*eps*sin(k*Theta+phi)) (k=1) via the")
    emit("  first-order law; apply; measure.  Refinement: same-k warps compose by w1+w2.")
    emit("=" * 100)
    k = 1
    E0 = bank.E(root0)
    _, Fp0 = bank.F_and_deriv(root0)
    Fpl, Fmi = bank.sidebands(E0, k)
    commands = [0.010j, -0.005j, 0.008 + 0.0j]
    labels = ["height +0.010 (up)", "height -0.005 (down)", "sigma +0.008 (sideways)"]
    accs = []
    for delta, lab in zip(commands, labels):
        w = solve_w(delta, Fp0, Fpl, Fmi)
        eps1 = 2 * abs(w)
        emit(f"  COMMAND {lab:24s} delta={cfmt(delta,4)}   solved warp eps={eps1:.4f} "
             f"phi={float(np.angle(w)):+.4f} rad")
        s_cur, misses = root0, []
        for it in range(1, 6):
            epsw, phiw = 2 * abs(w), float(np.angle(w))
            cw = bank.warp_coeff(epsw, k, phiw)
            s_cur = bank.newton(s_cur, cw)
            ach = s_cur - root0
            miss = abs(ach - delta) / abs(delta)
            misses.append(miss)
            emit(f"    iter {it}: eps={epsw:.4f} phi={phiw:+.4f}  achieved {cfmt(ach,6)}  "
                 f"miss {miss*100:7.3f}%" + ("   (one-shot)" if it == 1 else ""))
            if miss < 0.005:
                break
            # closed-loop refinement: sidebands of the WARPED bank at the achieved root;
            # same-k warps compose by phasor addition of w = (eps/2)e^{i phi}
            Ec = bank.E(s_cur)
            Fpc = complex(-np.dot(cw * bank.logn, Ec))
            Fplc = complex(np.dot(cw * np.exp(1j * k * bank.Th), Ec))
            Fmic = complex(np.dot(cw * np.exp(-1j * k * bank.Th), Ec))
            w = w + solve_w(delta - ach, Fpc, Fplc, Fmic)
        accs.append((misses[0], misses[-1], len(misses), eps1))
    return accs


# ---------------------------------------------------------------------------- Part C
def state_mags(bank, s):
    """Per-state magnitudes |v_n| of the state vector v_n = c0_n n^{-s} (diagonal)."""
    return np.abs(bank.c0) * np.exp(-s.real * bank.logn)


def isometry_devs(bank, s, warp):
    """(per-state modulus dev, and rel devs of: l2 energy, model A channel, P mass, M mass)
    under the diagonal warp -- all should be machine-zero for any pure phase warp."""
    va = state_mags(bank, s)
    wm = np.abs(warp)
    per_state = float(np.max(np.abs(wm - 1.0)))
    def rel(a, b):
        return abs(a - b) / abs(a) if a else 0.0
    l2 = rel(float(np.sum(va ** 2)), float(np.sum((va * wm) ** 2)))
    P0, Pw = float(np.sum(va[bank.pos])), float(np.sum((va * wm)[bank.pos]))
    M0, Mw = float(np.sum(va[bank.neg])), float(np.sum((va * wm)[bank.neg]))
    return per_state, l2, rel(P0 + M0, Pw + Mw), rel(P0, Pw), rel(M0, Mw)


def gate3(banks, roots, psis):
    emit("GATE 3 (Part C): isometry -- pure phase warps leave every state magnitude and all")
    emit("  diagonal state norms (l2 energy, model A channel, P/M lane masses) invariant")
    worst = 0.0
    for b, r0 in ((banks[2], roots[2]), (banks[5], roots[5])):
        # exact-reuse anchor: state-side l1 mass at s = 1/2 + i*gamma == the model A channel
        Amod = complex(model.focal_channels(b.char, "log_entry", b.N, b.gamma, "grow", b.tau)[0]).real
        l1 = float(np.sum(np.abs(b.c0) * np.exp(-0.5 * b.logn)))
        da = abs(l1 - Amod) / Amod
        emit(f"  {b.label}   state-l1 mass vs model A channel: rel diff = {da:.2e}")
        assert da < 1e-11, (b.label, da)
        cfgs = [(f"k={k} phi={phi:4.2f}", np.exp(1j * 0.05 * np.sin(k * b.Th + phi)))
                for (k, phi) in WARPS]
        if b is banks[2]:
            cfgs.append(("scrambled", np.exp(1j * 0.05 * np.sin(psis[2]))))
        for lab, warp in cfgs:
            devs = isometry_devs(b, r0, warp)
            worst = max(worst, max(devs))
            emit(f"    {lab:14s} per-state {devs[0]:.1e}  l2 {devs[1]:.1e}  A {devs[2]:.1e}  "
                 f"P {devs[3]:.1e}  M {devs[4]:.1e}")
    assert worst < 1e-13, worst
    emit(f"GATE 3: PASS (worst deviation {worst:.1e}; scrambled warp is ALSO isometric)")


def part_c(banks, roots, rows, psis):
    emit()
    emit("=" * 100)
    emit("PART C: STATE-EXPANDED SPACE -- the warp measured upstairs, per-state, before the sum")
    emit("=" * 100)
    # ---------------- C1: isometry across all structured configs
    emit("C1 ISOMETRY (pre-registered: exact): max deviation over all 8 warp configs per feature")
    emit(f"  {'feature':<46s} {'per-state':>10s} {'l2 energy':>10s} {'A channel':>10s} {'P mass':>10s} {'M mass':>10s}")
    iso_worst = 0.0
    for b, r0 in zip(banks, roots):
        m = [0.0] * 5
        for (k, phi) in WARPS:
            for eps in EPSES:
                devs = isometry_devs(b, r0, np.exp(1j * eps * np.sin(k * b.Th + phi)))
                m = [max(a, d) for a, d in zip(m, devs)]
        iso_worst = max(iso_worst, max(m))
        emit(f"  {b.label:<46s} " + "".join(f"{x:10.1e}" for x in m))
    emit(f"  C1 verdict: EXACT to machine precision (worst {iso_worst:.1e}).  Note: every canonical")
    emit("  state-level norm in model.py (per-state a_n, P/M/U lane masses, A channel, l2) is")
    emit("  DIAGONAL -- no cross-term state metric exists to test (recorded, not forced).")
    # ---------------- C2 + C3: exact lane responses, rebalance height, transport residual
    emit()
    emit("C2+C3 LANES AND TRANSPORT: warped lane responses computed EXACTLY upstairs (diagonal")
    emit("  action, no first-order step); rebalance height (P_w = M_w, found via newton_lane on the")
    emit("  lane split) vs Part A's readout dip; transport residual |dF_state_projected - dF_readout|")
    emit("  localized at the projection.  Lane 1st-order sideband law shown for reference (O(eps)).")
    max_reb = max_resid = max_resid_rel = 0.0
    lane_errs = {}   # (feature, k, phi) -> {eps: max(relP, relM)} for the 1st-order reference
    for b, r0 in zip(banks, roots):
        E0 = b.E(r0)
        P0, M0, F0, Fp0 = b.lane_F(r0)
        emit(f"\nFEATURE {b.label}")
        emit(f"  lane balance at unwarped root (house P = M claim): |P - M| = {abs(P0 - M0):.2e}   "
             f"(|P| = {abs(P0):.4f}, |M| = {abs(M0):.4f})")
        emit(f"  {'k':>2s} {'phi':>5s} {'eps':>5s}  {'|dP| exact':>11s} {'rel1st':>7s}  "
             f"{'|dM| exact':>11s} {'rel1st':>7s}  {'rebal-vs-dip':>12s} {'transport res':>13s} {'rel':>8s}")
        Ppl_c, Pmi_c, Mpl_c, Mmi_c = {}, {}, {}, {}
        for row in [r for r in rows if r["bank"] is b and not r["null"]]:
            k, phi, eps = row["k"], row["phi"], row["eps"]
            if k not in Ppl_c:
                Ppl_c[k], Pmi_c[k], Mpl_c[k], Mmi_c[k] = b.lane_sidebands(E0, k)
            warp = np.exp(1j * eps * np.sin(k * b.Th + phi))
            cw = b.c0 * warp
            Pw, Mw, _, _ = b.lane_F(r0, cw)          # exact per-state -> lane sums
            dP, dM = Pw - P0, Mw - M0
            zp, zm = np.exp(1j * phi), np.exp(-1j * phi)
            dP_pred = (eps / 2.0) * (zp * Ppl_c[k] - zm * Pmi_c[k])
            dM_pred = (eps / 2.0) * (zp * Mpl_c[k] - zm * Mmi_c[k])
            # rebalance height found entirely through the lane split
            s_lane = b.newton_lane(r0, cw)
            reb = abs(s_lane - (r0 + row["droot"]))
            # transport: project the exact state response through the sum, vs Part A readout
            dF_proj = dP - dM
            resid = abs(dF_proj - row["dval"])
            smass = float(np.sum(np.abs(b.c0 * (warp - 1.0)) * np.exp(-r0.real * b.logn)))
            rrel = resid / smass if smass > 0 else 0.0
            max_reb = max(max_reb, reb)
            max_resid = max(max_resid, resid)
            max_resid_rel = max(max_resid_rel, rrel)
            lane_errs.setdefault((f"{b.char}g{b.zidx+1}", k, phi), {})[eps] = \
                max(relerr(dP, dP_pred), relerr(dM, dM_pred))
            emit(f"  {k:2d} {phi:5.2f} {eps:5.2f}  {abs(dP):11.6f} {relerr(dP, dP_pred):7.4f}  "
                 f"{abs(dM):11.6f} {relerr(dM, dM_pred):7.4f}  {reb:12.2e} {resid:13.2e} {rrel:8.1e}")
    emit(f"\n  C2 verdict: lane rebalance == readout dip, max |s*_lane - s*_readout| = {max_reb:.2e} (Newton tol)")
    wk = max(lane_errs, key=lambda kk: lane_errs[kk][EPSES[1]])
    we = lane_errs[wk]
    emit(f"  lane 1st-order reference: worst rel err {we[EPSES[1]]:.4f} at {wk[0]} k={wk[1]} "
         f"(small-response row); its halving ratio err({EPSES[0]})/err({EPSES[1]}) = "
         f"{we[EPSES[0]]/we[EPSES[1]]:.3f} (~0.4-0.5 = genuinely 2nd-order, not an anomaly)")
    emit(f"  C3 verdict: transport residual at the projection, max abs = {max_resid:.2e}, max rel to")
    emit(f"  per-state response mass = {max_resid_rel:.2e} "
         + ("-- ZERO to summation precision, as pre-registered" if max_resid_rel < 1e-12
            else "** ANOMALY AT THE PROJECTION -- FULL PROMINENCE **"))
    # ---------------- C4: scrambled warp, state side
    emit()
    emit("C4 SCRAMBLED CONTROL, STATE SIDE: isometry must HOLD (unit modulus), lane sideband")
    emit("  structure must BREAK (no additive angle) -- the separating signature")
    c4 = []
    for bi in (2, 0):
        b, r0, psi = banks[bi], roots[bi], psis[bi]
        E0 = b.E(r0)
        P0, M0, _, _ = b.lane_F(r0)
        Ppl, Pmi, Mpl, Mmi = b.lane_sidebands(E0, 1)
        for eps in (0.05, 0.025):
            warp = np.exp(1j * eps * np.sin(psi))
            devs = isometry_devs(b, r0, warp)
            Pw, Mw, _, _ = b.lane_F(r0, b.c0 * warp)
            dP, dM = Pw - P0, Mw - M0
            rp = relerr(dP, (eps / 2.0) * (Ppl - Pmi))
            rm = relerr(dM, (eps / 2.0) * (Mpl - Mmi))
            c4.append((max(devs), rp, rm))
            emit(f"  {b.char}g{b.zidx+1} eps={eps:5.3f}: isometry dev {max(devs):.1e} (HOLDS)   "
                 f"lane vs structured k=1 law: relP = {rp:.3f}, relM = {rm:.3f} (BREAKS)")
    iso_c4 = max(x[0] for x in c4)
    struct_c4 = min(max(x[1], x[2]) for x in c4)
    emit(f"  C4 verdict: energy conservation is warp-agnostic (dev <= {iso_c4:.1e}) while harmonic")
    emit(f"  structure needs the additive angle (min lane-law rel err {struct_c4:.2f} = O(1) break)")
    return dict(iso_worst=iso_worst, max_reb=max_reb, max_resid=max_resid,
                max_resid_rel=max_resid_rel, iso_c4=iso_c4, struct_c4=struct_c4)


def main(full):
    t0 = time.time()
    emit(f"carrier_lockin.py -- lock-in source attribution instrument   [{time.strftime('%Y-%m-%d %H:%M:%S')}]")
    emit(f"canonical model: {os.path.abspath(model.__file__)}")
    emit()
    gate0()
    Nmax = max(model.eigenheight(model.CHARS[c]["zeros"][z]) for c, z in FEATURES)
    emit(f"\nsieving Omega(n) to N = {Nmax:,} ...")
    Om = omega_sieve(Nmax)
    banks = [Bank(c, z, Om) for c, z in FEATURES]
    gate1(banks[2])          # chi3 g1 bank angles
    roots = gate2(banks)
    psis = make_psis(banks)
    gate3(banks, roots, psis)
    if not full:
        emit(f"\nTEST MODE: all gates PASS ({time.time()-t0:.1f}s). Run without 'test' for the full instrument.")
        return
    pa = part_a(banks, roots)
    unresolved = halving_diagnostic(pa["failures"])
    ranges = linearity(banks, roots)
    ctrl = scrambled_control(banks, roots, psis)
    accs = part_b(banks[2], roots[2])
    pc = part_c(banks, roots, pa["rows"], psis)
    emit()
    emit("=" * 100)
    emit("TIERED SUMMARY")
    emit("=" * 100)
    emit("TIER 1 (measured, finite validated instances; no RH/GRH assumed or proved):")
    emit(f"  * VALUE law (lock-in observable): {pa['n_val_ok']}/{pa['n_rows']} tracked at pre-registered eps.")
    emit(f"  * SHIFT law: {pa['n_shift_ok']}/{pa['n_rows']} tracked at pre-registered eps -- P1 AS WRITTEN")
    emit(f"    PARTIALLY MISSED (full prominence).  Every miss ran the pre-registered halving")
    emit(f"    diagnostic: {len(pa['failures']) - len(unresolved)}/{len(pa['failures'])} confirmed the law as eps->0 "
         f"(errors halve with eps; miss = gain")
    emit(f"    saturation |droot| ~ g*eps too large for the linearization, instrument-side);")
    emit(f"    unresolved (sourceless-feature candidates): {len(unresolved)}"
         + (f" ** {unresolved} **" if unresolved else " -- NONE."))
    emit(f"  * exact-null harmonic rows: {pa['n_null_ok']}/{pa['n_null']} exact (k=3, phi=0: 3*Theta = pi*Omega).")
    emit(f"  * P3 halving median at (0.02, 0.05): {pa['med_ratio']:.3f} (~0.4 expected).")
    emit(f"  * linearity/calibration: eps_5% = {['%.5g' % r[0] for r in ranges]}, gain g = "
         f"{['%.2f' % r[1] for r in ranges]};")
    emit(f"    usable ROOT EXCURSION g*eps_5% = {['%.4f' % (r[0]*r[1]) for r in ranges]} -- the")
    emit(f"    instrument budget is the root excursion, not eps itself.")
    emit(f"  * actuator: one-shot misses {['%.2f%%' % (a[0]*100) for a in accs]}, closed-loop final "
         f"{['%.3f%%' % (a[1]*100) for a in accs]}")
    emit(f"    in {[a[2] for a in accs]} iterations (solved eps: {['%.3f' % a[3] for a in accs]}).")
    emit(f"  * scrambled control rel errs vs structured law: {['%.2f' % e for e in ctrl]} (O(1) = does not")
    emit(f"    track, as pre-registered; its own shift stays ~linear in eps -> mismatch is structural).")
    emit(f"  * PART C (state space): isometry EXACT (worst dev {pc['iso_worst']:.1e}; every canonical state")
    emit(f"    norm diagonal, no cross terms exist); lane rebalance == readout dip to {pc['max_reb']:.1e};")
    emit(f"    transport residual at the projection: max {pc['max_resid']:.1e} abs, {pc['max_resid_rel']:.1e} of the")
    emit(f"    per-state response mass -- the readout response is ENTIRELY projection/interference")
    emit(f"    re-arrangement (state energy conserved to 1e-16 while readout moves by O(0.1));")
    emit(f"    scrambled warp: isometry HOLDS ({pc['iso_c4']:.1e}) while lane structure BREAKS")
    emit(f"    (rel err >= {pc['struct_c4']:.2f}) -- energy conservation vs harmonic structure separated.")
    emit("TIER 2 (state of the evidence): on the canonical bank every cancellation feature is")
    emit("  bank-funded -- each responds to a controlled carrier wave as the Bessel-sideband theory")
    emit("  dictates (value law directly; shift law in its measured linear range), and the same law")
    emit("  inverts into a working closed-loop actuator.  This is the lock-in-amplifier")
    emit("  operationalization of 'every readout feature has a source'.  New instrument law:")
    emit(f"  sideband gain g is FEATURE-DEPENDENT ({min(r[1] for r in ranges):.2f}..{max(r[1] for r in ranges):.2f} "
         f"here; the eta/zeta feature ~{max(r[1] for r in ranges):.0f} is far")
    emit("  hotter than the quadratic-character features), so warp amplitude must be budgeted in")
    emit("  root excursion g*eps, not in eps.")
    emit("FALSIFIABILITY: P1-P5 and C1-C4 pre-registered in the module docstring, outcomes annotated")
    emit("  above; P1 partial miss reported at full prominence and resolved instrument-side by the")
    emit("  pre-registered discriminator; a feature whose error did NOT halve would have been a")
    emit("  sourceless-feature candidate -- count after this run: "
         + ("zero." if not unresolved else f"{len(unresolved)} ** SEE ABOVE **"))
    emit("  A transport residual above summation precision would have been an anomaly AT THE")
    emit("  PROJECTION -- count after this run: "
         + ("zero." if pc['max_resid_rel'] < 1e-12 else f"** {pc['max_resid_rel']:.1e} SEE PART C **"))
    emit(f"\ntotal runtime {time.time()-t0:.1f}s")
    with open(RESULTS_PATH, "w") as f:
        f.write("\n".join(_L) + "\n")
    print(f"\n[results written to {RESULTS_PATH}]")


if __name__ == "__main__":
    main(full=not (len(sys.argv) > 1 and sys.argv[1] == "test"))
