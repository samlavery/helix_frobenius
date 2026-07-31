#!/usr/bin/env python3
"""
detuned_rung_separation.py -- numerics probe A: the DETUNED-RUNG SEPARATION
CONTROL (arithmetic sensitivity of route (b)'s separation step).

CONTEXT (2026-07-29).  Proven so far: termwise lattice pair-reality
(Im(dual_xi + dual_-xi) = 0 on the Kloosterman-weighted master-formula terms,
eps_from_parity test D) and the exact Bessel-order ladder (rank r enters the
dual kernel only through orders n == r mod 2 with the quarter-turn phase
(-i)^n; eps_from_parity test A1).  The open bridge is SEPARATION: reality of
an AGGREGATE over rungs does not automatically descend to one rung.  This
probe detunes exactly one rung inside a three-rung aggregate and asks which
observables see it.

OBJECT UNDER TEST (the same instrument as eps_from_parity.py/poisson_dual.py:
elliptic p=2, k=1 channel, frozen W profile, frozen Kloosterman sum, frozen
prefactors; only the quadrature is promoted to the theta-grid of test A1):
  T_r(xi; l,f) = (p^{k/2}/2) f^-3 l^-2 * Kl_{l,f}(xi, -4p^k) * I_r(xi; l,f),
  I_r(xi)      = int_0^pi W_{l,f}(cos t) sin((r+1)t) e^{-i z cos t} dt,
                 z = 2 pi xi c,  c = p^{k/2}/(2 l f^2)      [U_r channel]
  agg(xi)      = sum_{(l,f) in {(1,1),(3,2)}} sum_{r in {1,3,5}}
                 eps_r * [T_r(xi) + T_r(-xi)],   xi in {1,2,3,4},
  eps_r        = measured theta-selfduality epsilon ladder (eps_from_parity
                 test B, k=12 seed): eps_1 = +1, eps_3 = -1, eps_5 = -1.

PRE-REGISTERED CRITERIA (fixed BEFORE any run; results only appended after):
  ANCHOR [instrument gate; if it fails no verdict is issued]
      On-instrument Bessel resummation identity at every rung r in {1,3,5},
      both lattice sites, xi in {1,2}:
        |I_r(xi) - pi sum_n a_n (-i)^n J_n(z)| / max_z |I_r| <= 1e-8,
      normalized per rung by the max over the z-grid (recorded trap: never
      per-(r,z) -- Bessel zeros masquerade as failures).
  P1  [baseline aggregate pair-reality]
        viol_P1 = max_xi |Im agg(xi)| / max_xi |agg(xi)| <= 1e-10.
      (Aggregate normalization by MAX over xi, per the recorded trap.)
  P2a [WEIGHT-SIDE detune] rung r*=3 only: U_3 -> U_4 in the x-weight
      (I_3 replaced by I_4 inside rung 3; Kl, prefactor, eps_3 unchanged).
      Criterion: viol_P2a >= 1e6 * max(viol_P1, 1e-16), i.e. the reality
      violation rises by >= 6 orders of magnitude.
  P2b [KERNEL-SIDE detune = order shift] rung r*=3 only: the rung's dual
      kernel is replaced by its order-shifted Bessel resummation
        I~_3(xi) = pi sum_n a_n^(3) (-i)^n J_{n+1}(z)
      (coefficients and quarter-turn phases kept, every Bessel order slid by
      one -- test A1's control, promoted into the aggregate).
      Criterion: viol_P2b >= 1e6 * max(viol_P1, 1e-16).
  P3  [jet localization at small argument, site (1,1)]
      (i) JET BAND: exact moment jets of the archimedean aggregate
          A(z) = sum_r eps_r I_r,  jet_m = (-i)^m/m! int G(t) cos^m t dt,
          m = 0..11.  Baseline even-order jet mass / odd-order jet mass
          <= 1e-10; after either detune of rung 3 the ratio >= 1e-2
          (the detuned rung, and only it, changes parity band).
      (ii) LOADINGS: on the full master-formula samples S(xi) =
          sum_r eps_r T_r(xi), xi on 24 points in [0.02, 0.40], fit complex
          loadings (c_1,c_3,c_5,d_1,d_3,d_5) against the known rung columns
          K_r = T_r and detuned columns K~_r (weight-side basis for P2a's
          detune, kernel-side basis for P2b's).  Flag rung r iff
          max(|c_r - c_r^P1|, |d_r - d_r^P1|) > 1e-3.  Criteria: the flagged
          set is exactly {3}; spectator rungs 1,5 stay within 1e-6 (absolute,
          loadings are O(1)) of their P1 values; basis condition number
          (identifiability of the separation) <= 1e8.
  P4  [reality-preserving control; must NOT flag]
      One global unimodular phase e^{i phi}, phi = 0.7, applied symmetrically
      to every +xi/-xi pair (e^{i phi} on the +xi member, e^{-i phi} on the
      -xi member -- the standing-wave-preserving gauge).  Criteria:
      pair-reality stays <= 1e-10 AND the gauge-invariant loading statistics
      ||c_r| - |c_r^P1|| <= 1e-6, |d_r| <= 1e-6 for every rung (no flag).

ANALYTIC NOTE (pre-run, part of the registration): T(-xi) = conj(T(xi)) holds
for ANY real x-weight (real Kronecker symbol, real profile), so the P2a
weight-side detune is EXPECTED to leave pair-reality at zero -- pair-reality
certifies the order<->phase<->conjugation registration, not the weight
content.  The pre-registered P2a criterion applies regardless and a P2a FAIL
is reported at full prominence as the structural finding "reality channel is
weight-blind"; P2b and P3 then decide whether the separating information
exists elsewhere (order-phase registration + jet band).  If P2b AND P3 also
fail, separation is arithmetic-blind on every probed observable and route
(b)'s separation step inherits the degree barrier: that verdict is published.

Run: python3 tmp/detuned_rung_separation.py
Out: tmp/detuned_rung_separation_results.txt
"""
import os
import sys
import math
import cmath
import time

import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poisson_dual as PD

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "detuned_rung_separation_results.txt")
_f = open(OUT, "w")


def emit(s=""):
    print(s, flush=True)
    _f.write(s + "\n")
    _f.flush()


# ---------------------------------------------------------------------------
# Frozen channel constants (identical to eps_from_parity.py).
# ---------------------------------------------------------------------------
P_, K_ = 2, 1
SIGN = -1
SCALE = 2.0 * P_ ** (K_ / 2.0)          # 2 p^{k/2}
RUNGS = (1, 3, 5)
EPS = {1: +1.0, 3: -1.0, 5: -1.0}       # measured epsilon ladder (test B)
DETUNED = 3
SITES = ((1, 1), (3, 2))
XIS = (1, 2, 3, 4)
PHI = 0.7
NT = 8192
TS = np.linspace(0.0, math.pi, NT + 1)
XS = np.cos(TS)
NMAX = 400


def W_profile(x, l, f):
    """theta_inf * (F + H) elliptic profile -- byte-level copy of the frozen
    eps_from_parity.py construction (which mirrors poisson_dual.arch_integral,
    sign=-1, iota=1)."""
    th = PD.theta_inf_profile(x, -1, K_)
    if th == 0.0:
        return 0.0
    edge = abs(1.0 - x * x)
    edge = max(edge, 1e-9)
    afe_arg = l * f * f / (SCALE * math.sqrt(edge))
    Fw = float(PD.F_profile(afe_arg))
    Hw = float(PD.H_profile(afe_arg, 1)) / math.sqrt(SCALE * SCALE * edge)
    return th * (Fw + Hw)


class Site:
    """One (l,f) lattice site of the elliptic p=2 channel."""

    def __init__(self, l, f):
        self.l, self.f = l, f
        self.c = P_ ** (K_ / 2.0) / (2.0 * l * f * f)
        self.pref = (P_ ** (K_ / 2.0) / 2.0) / (f ** 3 * l ** 2)
        self.Wv = np.array([W_profile(x, l, f) for x in XS])
        self._g = {}
        self._kl = {}
        self._co = {}

    def weight(self, m):
        """G_m(t) = W(cos t) sin((m+1)t): the U_m channel on the theta grid."""
        if m not in self._g:
            self._g[m] = self.Wv * np.sin((m + 1) * TS)
        return self._g[m]

    def kl(self, xi):
        key = round(float(xi), 12)
        if key not in self._kl:
            self._kl[key] = PD.kloosterman_lf(self.l, self.f, float(xi),
                                              -4 * P_ ** K_)
        return self._kl[key]

    def arch_I(self, m, xi):
        """I_m(xi) = int_0^pi G_m(t) e^{-i z cos t} dt, z = 2 pi xi c."""
        z = 2.0 * math.pi * xi * self.c
        return np.trapezoid(self.weight(m) * np.exp(-1j * z * XS), TS)

    def coeffs(self, m):
        """Cosine coefficients a_n of G_m (a_0 halved), truncation index."""
        if m not in self._co:
            G = self.weight(m)
            ns = np.arange(0, NMAX + 1)
            a = (2.0 / math.pi) * np.trapezoid(
                np.cos(np.outer(ns, TS)) * G[None, :], TS, axis=1)
            a[0] *= 0.5
            keep = np.abs(a) > 1e-15 * max(np.max(np.abs(a)), 1e-300)
            ncut = int(ns[keep][-1]) if keep.any() else 0
            self._co[m] = (a, ncut)
        return self._co[m]

    def term(self, m, xi):
        """Full master-formula term: pref * Kl(xi) * I_m(xi)."""
        return self.pref * self.kl(xi) * self.arch_I(m, xi)


_bcache = {}


def bessel_row(zabs, nmax):
    key = (round(zabs, 12), nmax)
    if key not in _bcache:
        _bcache[key] = np.array(
            [float(mp.besselj(n, zabs)) for n in range(nmax + 1)])
    return _bcache[key]


def resum_I(site, m, xi, shift=0):
    """Bessel-ladder (re)summation of I_m: pi sum_n a_n (-i)^n J_{n+shift}(z).
    shift=0 is the exact identity (test A1); shift=1 is the order-shift
    detune (test A1's control), coefficients and phases kept."""
    a, ncut = site.coeffs(m)
    z = 2.0 * math.pi * xi * site.c
    ns = np.arange(0, ncut + 1)
    Jrow = bessel_row(abs(z), ncut + shift)
    Jvals = Jrow[ns + shift].copy()
    if z < 0:
        Jvals *= (-1.0) ** ((ns + shift) % 2)      # J_n(-z) = (-1)^n J_n(z)
    phases = (-1j) ** (ns % 4)
    return math.pi * np.sum(a[: ncut + 1] * phases * Jvals)


def shifted_term(site, m, xi):
    """Kernel-side detuned master term: pref * Kl(xi) * I~_m(xi)."""
    return site.pref * site.kl(xi) * resum_I(site, m, xi, shift=1)


# ---------------------------------------------------------------------------
# ANCHOR: on-instrument resummation identity (gate).
# ---------------------------------------------------------------------------
def run_anchor(sites):
    emit("ANCHOR  on-instrument Bessel resummation I_r = pi sum a_n (-i)^n J_n(z)")
    worst = 0.0
    for site in sites:
        for r in RUNGS:
            vals, errs = [], []
            for xi in (1, 2):
                direct = site.arch_I(r, xi)
                resum = resum_I(site, r, xi, shift=0)
                vals.append(abs(direct))
                errs.append(abs(direct - resum))
            rel = max(errs) / max(max(vals), 1e-300)
            worst = max(worst, rel)
            emit(f"    (l,f)=({site.l},{site.f}) r={r}: rel err {rel:.3e}")
    ok = worst < 1e-8
    emit(f"    worst = {worst:.3e}  -> {'PASS' if ok else 'FAIL (instrument gate: no verdict)'}")
    return ok, worst


# ---------------------------------------------------------------------------
# P1/P2/P4: the paired aggregate on the xi lattice.
# ---------------------------------------------------------------------------
def rung_pair(site, r, xi, mode):
    """eps_r-weighted (+xi/-xi) pair of rung r at one site, under a mode:
    mode None = baseline; 'weight' = U_3 -> U_4 in rung 3; 'kernel' =
    order-shifted resummation in rung 3; 'gauge' = e^{i phi} / e^{-i phi}."""
    if r == DETUNED and mode == "weight":
        tp, tm = site.term(r + 1, xi), site.term(r + 1, -xi)
    elif r == DETUNED and mode == "kernel":
        tp, tm = shifted_term(site, r, xi), shifted_term(site, r, -xi)
    else:
        tp, tm = site.term(r, xi), site.term(r, -xi)
    if mode == "gauge":
        tp *= cmath.exp(1j * PHI)
        tm *= cmath.exp(-1j * PHI)
    return EPS[r] * (tp + tm)


def aggregate_violation(sites, mode):
    vals = {}
    for xi in XIS:
        vals[xi] = sum(rung_pair(site, r, xi, mode)
                       for site in sites for r in RUNGS)
    mx = max(abs(v) for v in vals.values())
    mi = max(abs(v.imag) for v in vals.values())
    return mi / max(mx, 1e-300), vals, mx


# ---------------------------------------------------------------------------
# P3 (i): exact moment jets of the archimedean aggregate at site (1,1).
#   jet_m = (-i)^m / m! * int G(t) cos^m t dt  (coefficient of z^m of I).
#   For the kernel-side detuned rung the jets come from the shifted Bessel
#   Taylor series: J_{n+1}(z) = sum_k (-1)^k (z/2)^{n+1+2k}/(k!(n+1+k)!).
# ---------------------------------------------------------------------------
MJET = 12  # orders m = 0..11


def moment_jets(site, m):
    G = site.weight(m)
    return np.array([(-1j) ** (mm % 4) / math.factorial(mm)
                     * np.trapezoid(G * XS ** mm, TS) for mm in range(MJET)])


def shifted_jets(site, m):
    a, ncut = site.coeffs(m)
    out = np.zeros(MJET, dtype=complex)
    for mm in range(MJET):
        tot = 0.0 + 0.0j
        for n in range(0, min(ncut, mm - 1) + 1):
            nu = n + 1
            if mm < nu or (mm - nu) % 2 != 0:
                continue
            k = (mm - nu) // 2
            tot += (a[n] * (-1j) ** (n % 4) * (-1.0) ** k
                    / (2.0 ** mm * math.factorial(k) * math.factorial(nu + k)))
        out[mm] = math.pi * tot
    return out


def jet_band(jets):
    ev = sum(abs(jets[mm]) for mm in range(0, MJET, 2))
    od = sum(abs(jets[mm]) for mm in range(1, MJET, 2))
    return ev / max(od, 1e-300), ev, od


# ---------------------------------------------------------------------------
# P3 (ii): loading localization on the full master-formula samples.
# ---------------------------------------------------------------------------
XI_GRID = np.linspace(0.02, 0.40, 24)


def column(site, r, kind):
    """kind 'base' = T_r; 'wdet' = weight-side detuned T (U_{r+1});
    'kdet' = kernel-side detuned T (order-shifted resummation)."""
    if kind == "base":
        return np.array([site.term(r, xi) for xi in XI_GRID])
    if kind == "wdet":
        return np.array([site.term(r + 1, xi) for xi in XI_GRID])
    return np.array([shifted_term(site, r, xi) for xi in XI_GRID])


def fit_loadings(basis, S):
    sol, _, _, sv = np.linalg.lstsq(basis, S, rcond=None)
    resid = np.linalg.norm(basis @ sol - S) / max(np.linalg.norm(S), 1e-300)
    cond = sv[0] / sv[-1]
    return sol, resid, cond


def loading_report(tag, sol, sol_base, gauge_invariant=False):
    """Flags per rung; returns (flags, spectator_max_dev)."""
    flags, devs = [], {}
    for i, r in enumerate(RUNGS):
        if gauge_invariant:
            dc = abs(abs(sol[i]) - abs(sol_base[i]))
            dd = abs(sol[i + 3])
        else:
            dc = abs(sol[i] - sol_base[i])
            dd = abs(sol[i + 3] - sol_base[i + 3])
        dev = max(dc, dd)
        devs[r] = dev
        if dev > 1e-3:
            flags.append(r)
        emit(f"    {tag} r={r}: |c|={abs(sol[i]):.9f} |d|={abs(sol[i+3]):.3e}"
             f"  dev-from-P1 = {dev:.3e}{'  FLAGGED' if dev > 1e-3 else ''}")
    return flags, devs


def main():
    global XIS
    t0 = time.time()
    emit("DETUNED-RUNG SEPARATION CONTROL -- probe A of the separation step")
    emit("aggregate: rungs r in {1,3,5}, eps = (+1,-1,-1), sites (1,1),(3,2),")
    emit("           elliptic p=2 k=1 master-formula terms, xi in {1,2,3,4}")
    emit("=" * 86)
    sites = [Site(l, f) for (l, f) in SITES]
    site11 = sites[0]

    # ---------------- ANCHOR ----------------
    anchor_ok, anchor_worst = run_anchor(sites)

    # ---------------- P1 ----------------
    emit("P1  baseline aggregate pair-reality (max_xi |Im agg| / max_xi |agg|)")
    v1, vals1, mx1 = aggregate_violation(sites, None)
    for xi in XIS:
        emit(f"    xi={xi}: agg = {vals1[xi].real:+.6e} {vals1[xi].imag:+.6e}i")
    p1_ok = v1 <= 1e-10
    emit(f"    viol_P1 = {v1:.3e} (max |agg| = {mx1:.3e})  -> "
         f"{'PASS' if p1_ok else 'FAIL'}")
    floor = max(v1, 1e-16)

    # ---------------- P2a ----------------
    emit("P2a weight-side detune of rung 3 (U_3 -> U_4; Kl, pref, eps kept)")
    v2a, vals2a, mx2a = aggregate_violation(sites, "weight")
    p2a_ok = v2a >= 1e6 * floor
    emit(f"    viol_P2a = {v2a:.3e} (max |agg| = {mx2a:.3e}); rise over P1 floor = "
         f"{v2a / floor:.3e}x  -> {'PASS (>= 6 orders)' if p2a_ok else 'FAIL (reality channel weight-BLIND)'}")

    # ---------------- P2b ----------------
    emit("P2b kernel-side detune of rung 3 (Bessel order shift J_n -> J_{n+1},")
    emit("    coefficients and quarter-turn phases kept)")
    v2b, vals2b, mx2b = aggregate_violation(sites, "kernel")
    p2b_ok = v2b >= 1e6 * floor
    emit(f"    viol_P2b = {v2b:.3e} (max |agg| = {mx2b:.3e}); rise over P1 floor = "
         f"{v2b / floor:.3e}x  -> {'PASS (>= 6 orders)' if p2b_ok else 'FAIL (order-shift invisible: separation blind)'}")

    # ---------------- P3 (i): jet band ----------------
    emit("P3i jet band at site (1,1): exact moment jets m=0..11 of the")
    emit("    archimedean aggregate A(z) = sum_r eps_r I_r")
    jets_base = sum(EPS[r] * moment_jets(site11, r) for r in RUNGS)
    jets_w = (EPS[1] * moment_jets(site11, 1)
              + EPS[3] * moment_jets(site11, 4)
              + EPS[5] * moment_jets(site11, 5))
    jets_k = (EPS[1] * moment_jets(site11, 1)
              + EPS[3] * shifted_jets(site11, 3)
              + EPS[5] * moment_jets(site11, 5))
    rb, evb, odb = jet_band(jets_base)
    rw, evw, odw = jet_band(jets_w)
    rk, evk, odk = jet_band(jets_k)
    emit("    |jet_m|: m:      " + " ".join(f"{mm:>9d}" for mm in range(MJET)))
    emit("    baseline:        " + " ".join(f"{abs(v):.3e}" for v in jets_base))
    emit("    weight-detuned:  " + " ".join(f"{abs(v):.3e}" for v in jets_w))
    emit("    kernel-detuned:  " + " ".join(f"{abs(v):.3e}" for v in jets_k))
    p3i_ok = (rb <= 1e-10) and (rw >= 1e-2) and (rk >= 1e-2)
    emit(f"    even/odd jet mass: baseline {rb:.3e}  weight-det {rw:.3e}  "
         f"kernel-det {rk:.3e}  -> {'PASS' if p3i_ok else 'FAIL'}")

    # ---------------- P3 (ii): loadings ----------------
    emit("P3ii loading localization on full master-formula samples, site (1,1),")
    emit(f"     xi grid = 24 pts in [{XI_GRID[0]:.2f}, {XI_GRID[-1]:.2f}]")
    base_cols = [column(site11, r, "base") for r in RUNGS]
    wdet_cols = [column(site11, r, "wdet") for r in RUNGS]
    kdet_cols = [column(site11, r, "kdet") for r in RUNGS]
    S_P1 = sum(EPS[r] * base_cols[i] for i, r in enumerate(RUNGS))
    S_w = (EPS[1] * base_cols[0] + EPS[3] * wdet_cols[1] + EPS[5] * base_cols[2])
    S_k = (EPS[1] * base_cols[0] + EPS[3] * kdet_cols[1] + EPS[5] * base_cols[2])
    basis_w = np.column_stack(base_cols + wdet_cols)
    basis_k = np.column_stack(base_cols + kdet_cols)

    solb_w, residb_w, cond_w = fit_loadings(basis_w, S_P1)
    solb_k, residb_k, cond_k = fit_loadings(basis_k, S_P1)
    emit(f"    basis condition numbers: weight-basis {cond_w:.3e}, "
         f"kernel-basis {cond_k:.3e} (criterion <= 1e8)")
    emit(f"    baseline fit residuals: {residb_w:.3e} / {residb_k:.3e}")
    emit("    baseline loadings (weight basis):")
    loading_report("P1  ", solb_w, solb_w)

    emit("    weight-side detuned aggregate, fit in weight basis:")
    solw, residw, _ = fit_loadings(basis_w, S_w)
    flags_w, devs_w = loading_report("P2a ", solw, solb_w)
    emit(f"      fit residual {residw:.3e}; flagged rungs: {flags_w}")

    emit("    kernel-side detuned aggregate, fit in kernel basis:")
    solk, residk, _ = fit_loadings(basis_k, S_k)
    flags_k, devs_k = loading_report("P2b ", solk, solb_k)
    emit(f"      fit residual {residk:.3e}; flagged rungs: {flags_k}")

    spect_w = max(devs_w[1], devs_w[5])
    spect_k = max(devs_k[1], devs_k[5])
    p3ii_ok = (flags_w == [3] and flags_k == [3]
               and spect_w <= 1e-6 and spect_k <= 1e-6
               and cond_w <= 1e8 and cond_k <= 1e8)
    emit(f"    localization: flags weight={flags_w} kernel={flags_k}; spectator max dev "
         f"{spect_w:.3e} / {spect_k:.3e}  -> {'PASS' if p3ii_ok else 'FAIL'}")
    p3_ok = p3i_ok and p3ii_ok

    # ---------------- P4 ----------------
    emit("P4  reality-preserving control: global phase e^{i phi} (phi=0.7) on +xi,")
    emit("    e^{-i phi} on -xi, every pair, every rung; must NOT flag")
    v4, vals4, mx4 = aggregate_violation(sites, "gauge")
    emit(f"    pair-reality under gauge: viol = {v4:.3e} (criterion <= 1e-10)")
    S_g = cmath.exp(1j * PHI) * S_P1
    solg, residg, _ = fit_loadings(basis_w, S_g)
    flags_g, devs_g = loading_report("P4  ", solg, solb_w, gauge_invariant=True)
    spect_g = max(devs_g.values())
    p4_ok = (v4 <= 1e-10) and (flags_g == []) and (spect_g <= 1e-6)
    emit(f"    gauge-invariant loading deviation max = {spect_g:.3e}; flagged: {flags_g}"
         f"  -> {'PASS' if p4_ok else 'FAIL (false positive: instrument unusable)'}")

    # ---------------- VERDICT ----------------
    emit("=" * 86)
    emit(f"ANCHOR {'PASS' if anchor_ok else 'FAIL'} ({anchor_worst:.3e})   "
         f"P1 {'PASS' if p1_ok else 'FAIL'} ({v1:.3e})   "
         f"P2a {'PASS' if p2a_ok else 'FAIL'} ({v2a:.3e})   "
         f"P2b {'PASS' if p2b_ok else 'FAIL'} ({v2b:.3e})")
    emit(f"P3i {'PASS' if p3i_ok else 'FAIL'}   P3ii {'PASS' if p3ii_ok else 'FAIL'}   "
         f"P4 {'PASS' if p4_ok else 'FAIL'}")
    if not anchor_ok:
        emit("VERDICT: INSTRUMENT GATE FAILED -- no separation verdict issued.")
    elif p1_ok and p2b_ok and p3_ok and p4_ok:
        if p2a_ok:
            emit("VERDICT: separation is ARITHMETICALLY SENSITIVE on every probed")
            emit("  observable (both detunes visible in reality; jets localize).")
        else:
            emit("VERDICT: separation is ARITHMETICALLY SENSITIVE, with a structural")
            emit("  split: pair-reality is WEIGHT-BLIND (P2a null, the pre-registered")
            emit("  conjugation-symmetry expectation: T(-xi) = conj T(xi) for any real")
            emit("  weight) but maximally sensitive to order-phase misregistration")
            emit("  (P2b), and the jet/order ladder localizes the detuned rung and only")
            emit("  it (P3) without false positives (P4).  A separation mechanism can")
            emit("  exist: reality certifies the order<->phase<->conjugation")
            emit("  registration; per-rung weight identity is carried by the jet band.")
    elif not (p2a_ok or p2b_ok) or not p3_ok:
        emit("VERDICT: separation is ARITHMETIC-BLIND on the probed observables --")
        emit("  the detuned rung is invisible (P2/P3 FAIL).  Route (b)'s separation")
        emit("  step inherits the degree barrier on the seed side.  Published as a")
        emit("  finding per the falsifiability register.")
    else:
        emit("VERDICT: MIXED -- see FAIL lines above; published as found.")
    # ---------------- POST-HOC ADDENDUM ----------------
    # Added AFTER the first run (2026-07-30).  Nothing above changed; the
    # pre-registered criteria and their measured outcomes stand as printed.
    # This block reports two instrument facts discovered in the first run and
    # a replication of P1/P2 on the live sublattice with identical criteria.
    emit("")
    emit("POST-HOC ADDENDUM (observations after first run; criteria unchanged)")
    emit("A. Measured lattice support of the arithmetic weight (disc -4p^k = -8):")
    for site in sites:
        live = [(xi, site.kl(xi)) for xi in range(1, 49)
                if abs(site.kl(xi)) > 1e-9]
        if live:
            desc = ", ".join(f"xi={xi}: {v.real:+.1f}{v.imag:+.1e}i"
                             for xi, v in live[:4]) + ", ..."
        else:
            desc = "NONE (site identically dead on the integer lattice)"
        emit(f"    Kl_({site.l},{site.f})(xi,-8), xi=1..48 live points: {desc}")
    emit("    => every live integer-lattice weight is REAL (Kl = 4 on 4Z at (1,1));")
    emit("       site (3,2) contributes nothing at any integer xi.")
    emit("B. The baseline PAIRED aggregate nulls (max |agg| = %.3e above): for" % mx1)
    emit("   odd r, I_r is purely imaginary and every live Kl is real, so each")
    emit("   +xi/-xi pair cancels EXACTLY -- the on-instrument appearance of the")
    emit("   proven odd-rank lattice closure (RankLadderParity.latticeSum_eq_zero_odd")
    emit("   / rank_ladder_closure odd-r closure).  P1's PASS is therefore trivial")
    emit("   (0 over roundoff); the load-bearing reality facts are the phases of")
    emit("   the DETUNED aggregates (P2a real, P2b imaginary), and BOTH detunes are")
    emit("   visible at O(1) in aggregate MAGNITUDE (closure break):")
    emit(f"     max|agg|: baseline {mx1:.3e} -> weight-det {mx2a:.3e} "
         f"({mx2a / max(mx1, 1e-300):.1e}x), kernel-det {mx2b:.3e} "
         f"({mx2b / max(mx1, 1e-300):.1e}x)")
    emit("C. Replication of P1/P2 on the LIVE sublattice xi in {4,8,12,16}")
    emit("   (all points live, Kl = 4; same pre-registered criteria):")
    XIS = (4, 8, 12, 16)
    v1L, _, mx1L = aggregate_violation(sites, None)
    fL = max(v1L, 1e-16)
    v2aL, _, mx2aL = aggregate_violation(sites, "weight")
    v2bL, _, mx2bL = aggregate_violation(sites, "kernel")
    emit(f"    P1  viol = {v1L:.3e} (max|agg| = {mx1L:.3e})  -> "
         f"{'PASS' if v1L <= 1e-10 else 'FAIL'}")
    emit(f"    P2a viol = {v2aL:.3e} (max|agg| = {mx2aL:.3e}); rise = "
         f"{v2aL / fL:.3e}x  -> "
         f"{'PASS' if v2aL >= 1e6 * fL else 'FAIL (weight-blind, replicated)'}")
    emit(f"    P2b viol = {v2bL:.3e} (max|agg| = {mx2bL:.3e}); rise = "
         f"{v2bL / fL:.3e}x  -> "
         f"{'PASS' if v2bL >= 1e6 * fL else 'FAIL'}")
    emit(f"[done] {time.time() - t0:.0f}s -- results in {OUT}")


if __name__ == "__main__":
    main()
