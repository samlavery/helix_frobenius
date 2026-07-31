#!/usr/bin/env python3
"""
be_bridge.py -- THE BE BRIDGE (the paper's named open experiment, sec:pipeline):
does the MEASURED nu-clock of Altug's actual orbital transform generate the warp
that closes the actual transform's cell?

Object: the complex transform (nu here is Altug's nu_J; the paper's clock law is
stated in nu_clock = 2 nu_J, so the law in this coordinate is HALF of 0.524):
    V(nu) = J_{l,f}(xi,nu,X) = INT G(y/X) y Psi_r(y) e(-y nu / 2lf^2) dy,
Psi_r(y) = INT theta_inf(x) [F(arg)+arg H(arg)] U_r(x) e(-x xi sqrt(4y)/4lf^2) dx
(be_prop52_certify.Psi with the Chebyshev rank multiplier U_r, as in sec:comb).

The clock configurator (sec:general: "sets the period, PHASE, and scale"): the
comb's instantaneous phase phi(nu) is extracted (Hilbert transform of the
de-trended log-power) and fitted ONCE per configuration by the frozen quadratic
model phi = a0 + a1 nu + a2 nu^2 -- three numbers, a slowly-drifting clock, per
the paper's own finding that the scalar kappa is "the mean of a slightly
drifting clock".  Nothing is fitted per cell or per point.

Cells are cut where the FITTED phase crosses multiples of 2pi; the de-enveloped
fluctuation is resampled at per_cell samples per fitted cycle (the mu_M snap in
clock phase) and summed over complete cells.  A deterministic comb riding the
fitted clock closes; the envelope misfit is the only leak.

PRE-REGISTERED CRITERIA (fixed before the run):
  ANCHOR-1  strict synthetic comb, known period: period within 2%, closure
            >= 30x below the worst wrong-period control.
  ANCHOR-2  drifting synthetic comb (5% frequency drift): phase-tracked closure
            >= 30x below the fixed-period closure of the same signal.
            Both anchors gate everything; anchor failure = instrument failure.
  CLOCK     measured local period within 15% of the nu_J law
            0.262*(lf2)^1.03*(X/8)^(-1.04) (cross-check only, never an input).
  BRIDGE    per configuration (r, xi, X, lf2) passing the comb-quality gate
            (harmonics 1,2 capture >= 5% of log-power fluctuation):
            phase-tracked closure q_track satisfies
              q_track * 10 <= min(wrong-drift controls)  AND
              q_track * 10 <= fixed-period closure       AND
              q_track < noise surrogate.
  FALSIFIER if q_track fails on the gated configurations, the bridge is
            DISCONFIRMED and reported as such (falsifiability register).

Run: python3 tmp/be_bridge.py       Out: tmp/be_bridge_results.txt
"""
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import be_prop52_certify as BP

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "be_bridge_results.txt")
RNG = np.random.default_rng(20260728)

_f = open(OUT, "w")


def emit(s=""):
    print(s, flush=True)
    _f.write(s + "\n")
    _f.flush()


# ---------------------------------------------------------------- U_r multiplier
def cheb_U(r, x):
    if r == 0:
        return np.ones_like(x)
    if r == 1:
        return 2.0 * x
    um2, um1 = np.ones_like(x), 2.0 * x
    for _ in range(2, r + 1):
        um2, um1 = um1, 2.0 * x * um1 - um2
    return um1


def Psi_r(y, xi, l, f, r):
    lf2 = l * f * f
    sq4y = math.sqrt(4.0 * y)
    edge = np.sqrt(np.maximum(1.0 - BP._XS * BP._XS, 1e-12))
    arg = lf2 / (sq4y * edge)
    prof = BP._TH * (BP.F_of(arg) + arg * BP.H_of(arg)) * cheb_U(r, BP._XS)
    phase = np.exp(-2j * math.pi * (BP._XS * xi * sq4y) / (4.0 * lf2))
    return np.sum(prof * phase) * BP._DX


# ---------------------------------------------------------------- transform V(nu)
def nuJ_law(lf2, X):
    """The measured clock law transported to the nu_J coordinate (nu_clock = 2 nu_J)."""
    return 0.5 * 0.524 * (lf2 ** 1.03) * ((X / 8.0) ** (-1.04))


def transform_band(r, xi, l, f, X, periods=10.0, per_cell=48, ny=1400):
    lf2 = l * f * f
    d_pred = nuJ_law(lf2, X)
    ys = np.linspace(0.20 * X, 1.30 * X, ny)
    g = BP.G_altug(ys / X)
    psi = np.array([Psi_r(float(y), xi, l, f, r) if gw > 0 else 0.0
                    for y, gw in zip(ys, g)], dtype=complex)
    integ = g * ys * psi
    nu0 = 2.0 * d_pred
    n_samp = int(round(periods * per_cell))
    nus = nu0 + np.arange(n_samp) * (d_pred / per_cell)
    phase = np.exp(-2j * math.pi * np.outer(nus, ys) / (2.0 * lf2))
    V = (phase @ integ) * (ys[1] - ys[0])
    return nus, V, d_pred


# ---------------------------------------------------------------- clock pieces
def log_power_fluct(nus, V, deg=3):
    lp = np.log(np.maximum(np.abs(V) ** 2, 1e-300))
    c = np.polyfit(nus, lp, deg)
    env = np.polyval(c, nus)
    return lp - env, env


def _period_score(fl, t, d):
    w = 2.0 * math.pi / d
    p = 0.0
    for k in (1, 2):
        p += (np.dot(fl, np.cos(k * w * t)) ** 2 +
              np.dot(fl, np.sin(k * w * t)) ** 2)
    return p


def measure_period(nus, V, d_lo, d_hi, nscan=3000):
    """Coarse fundamental of the log-power fluctuation (initialization only)."""
    fl, _ = log_power_fluct(nus, V)
    t = nus - nus[0]
    best = (float("nan"), -1.0)
    for d in np.linspace(d_lo, d_hi, nscan):
        p = _period_score(fl, t, d)
        if p > best[1]:
            best = (d, p)
    return best


def comb_power_fraction(nus, V, period):
    fl, _ = log_power_fluct(nus, V)
    t = nus - nus[0]
    w = 2.0 * math.pi / period
    n = len(fl)
    cap = 0.0
    for k in (1, 2):
        cap += (np.dot(fl, np.cos(k * w * t)) ** 2 +
                np.dot(fl, np.sin(k * w * t)) ** 2) * 2.0 / n
    tot = np.dot(fl, fl)
    return float(cap / tot) if tot > 0 else 0.0


def hilbert_phase(fl, dnu, period):
    """Instantaneous phase of the FUNDAMENTAL: narrowband filter around 1/period
    (0.55-1.45x), then the FFT analytic signal."""
    n = len(fl)
    F = np.fft.fft(fl)
    freqs = np.fft.fftfreq(n, d=dnu)
    f0 = 1.0 / period
    keep = (freqs > 0.55 * f0) & (freqs < 1.45 * f0)
    Ff = np.where(keep, F, 0.0)
    analytic = np.fft.ifft(2.0 * Ff)
    return np.unwrap(np.angle(analytic))


def fit_quad_clock(nus, V, period):
    """The frozen 3-parameter clock: phi(nu) = a0 + a1 nu + a2 nu^2, fitted once
    to the fundamental's Hilbert phase of the de-trended log-power fluctuation.
    The edges (half a period each side) are excluded from the fit (filter ring)."""
    fl, _ = log_power_fluct(nus, V)
    phi = hilbert_phase(fl, nus[1] - nus[0], period)
    t = nus - nus[0]
    m = max(1, int(round(0.5 * period / (nus[1] - nus[0]))))
    sl = slice(m, len(t) - m)
    A = np.stack([np.ones_like(t[sl]), t[sl], t[sl] ** 2], axis=1)
    coef, *_ = np.linalg.lstsq(A, phi[sl], rcond=None)
    return coef  # a0, a1, a2 (in the t = nu - nu0 coordinate)


def joint_envelope(nus, V, clock_period, deg=3):
    t = nus - nus[0]
    lp = np.log(np.maximum(np.abs(V) ** 2, 1e-300))
    w = 2.0 * math.pi / clock_period
    cols = [t ** j for j in range(deg + 1)]
    for k in (1, 2):
        cols.append(np.cos(k * w * t))
        cols.append(np.sin(k * w * t))
    A = np.stack(cols, axis=1)
    coef, *_ = np.linalg.lstsq(A, lp, rcond=None)
    return A[:, :deg + 1] @ coef[:deg + 1]


# ---------------------------------------------------------------- closures
def _closure_on_grid(t_grid, nus, V, per_cell):
    """De-envelope on the given (clock-aligned) grid and sum complete cells.
    On the aligned grid the comb is periodic in the GRID INDEX (per_cell samples
    per cycle), so the joint envelope fit uses index-space harmonics: the
    polynomial part (in nu) is the envelope, decontaminated of the comb."""
    if t_grid is None or len(t_grid) < 2 * per_cell:
        return float("nan"), 0
    Va = np.interp(t_grid, nus, V.real) + 1j * np.interp(t_grid, nus, V.imag)
    lp = np.log(np.maximum(np.abs(Va) ** 2, 1e-300))
    t = t_grid - t_grid[0]
    cyc = 2.0 * math.pi * np.arange(len(t_grid)) / per_cell
    cols = [t ** j for j in range(4)]
    for k in (1, 2):
        cols.append(np.cos(k * cyc))
        cols.append(np.sin(k * cyc))
    A = np.stack(cols, axis=1)
    coef, *_ = np.linalg.lstsq(A, lp, rcond=None)
    env = A[:, :4] @ coef[:4]
    W = np.abs(Va) ** 2 / np.exp(env)
    W = W - np.mean(W)
    rms = float(np.sqrt(np.mean(W ** 2)))
    if rms == 0:
        return float("nan"), 0
    ncell = len(W) // per_cell
    qs = [abs(float(np.mean(W[c * per_cell:(c + 1) * per_cell]))) / rms
          for c in range(ncell)]
    return float(np.median(qs)), ncell


def phase_aligned_grid(nus, coef, per_cell):
    """Grid of nu-points where the fitted phase crosses k*(2pi/per_cell),
    complete 2pi cells only."""
    a0, a1, a2 = coef
    t = nus - nus[0]
    phi = a0 + a1 * t + a2 * t * t
    if not np.all(np.diff(phi) > 0):
        if np.all(np.diff(phi) < 0):
            phi = -phi
        else:
            return None
    lo = math.ceil(phi[0] / (2 * math.pi))
    hi = math.floor(phi[-1] / (2 * math.pi))
    ncell = hi - lo
    if ncell < 2:
        return None
    targets = 2 * math.pi * (lo + np.arange(ncell * per_cell) / per_cell)
    tg = np.interp(targets, phi, t)
    return nus[0] + tg


def cell_closure_tracked(nus, V, coef, per_cell=48):
    grid = phase_aligned_grid(nus, coef, per_cell)
    return _closure_on_grid(grid, nus, V, per_cell)


def cell_closure_fixed(nus, V, period, per_cell=48):
    span = nus[-1] - nus[0]
    ncell = int(math.floor(span / period))
    if ncell < 2:
        return float("nan"), 0
    grid = nus[0] + np.arange(ncell * per_cell) * (period / per_cell)
    return _closure_on_grid(grid, nus, V, per_cell)


# ---------------------------------------------------------------- anchors
def anchor_strict():
    nus = np.linspace(1.0, 16.0, 14 * 48)
    d_true = 1.07
    env = np.exp(-0.15 * (nus - 1.0))
    comb = 1.0 + 0.45 * np.cos(2 * math.pi * nus / d_true) \
               + 0.18 * np.cos(4 * math.pi * nus / d_true + 0.7)
    V = env * comb * np.exp(1j * 3.0 * nus)
    d_meas, _ = measure_period(nus, V, 0.6 * d_true, 1.5 * d_true)
    coef = fit_quad_clock(nus, V, d_meas)
    q_true, nc = cell_closure_tracked(nus, V, coef)
    q_ctrl = min(cell_closure_fixed(nus, V, fm * d_meas)[0]
                 for fm in (0.80, 0.90, 1.10, 1.25))
    ok_p = abs(d_meas - d_true) / d_true < 0.02
    ok_c = q_true * 30.0 <= q_ctrl
    emit(f"ANCHOR-1 strict   d_meas={d_meas:.4f}/{d_true:.4f}  q={q_true:.2e}  "
         f"worst-ctrl={q_ctrl:.2e}  cells={nc}  period_ok={ok_p} contrast_ok={ok_c}")
    return ok_p and ok_c


def anchor_drift():
    nus = np.linspace(1.0, 16.0, 14 * 48)
    d0 = 1.07
    w0 = 2 * math.pi / d0
    t = nus - nus[0]
    span = t[-1]
    phi = w0 * t * (1.0 + 0.025 * t / span)       # ~5% frequency drift over band
    env = np.exp(-0.15 * (nus - 1.0))
    comb = 1.0 + 0.45 * np.cos(phi) + 0.18 * np.cos(2 * phi + 0.7)
    V = env * comb * np.exp(1j * 3.0 * nus)
    d_meas, _ = measure_period(nus, V, 0.6 * d0, 1.5 * d0)
    coef = fit_quad_clock(nus, V, d_meas)
    q_trk, nc = cell_closure_tracked(nus, V, coef)
    q_fix, _ = cell_closure_fixed(nus, V, d_meas)
    ok = q_trk * 30.0 <= q_fix
    emit(f"ANCHOR-2 drifting q_tracked={q_trk:.2e}  q_fixed={q_fix:.2e}  "
         f"cells={nc}  tracked/fixed contrast_ok={ok}")
    return ok


# ---------------------------------------------------------------- main sweep
def run_config(r, xi, l, f, X):
    lf2 = l * f * f
    nus, V, d_pred = transform_band(r, xi, l, f, X)
    d_meas, _ = measure_period(nus, V, 0.6 * d_pred, 1.5 * d_pred)
    frac = comb_power_fraction(nus, V, d_meas)
    gate = frac >= 0.05
    coef = fit_quad_clock(nus, V, d_meas)
    q_trk, nc = cell_closure_tracked(nus, V, coef)
    q_fix, _ = cell_closure_fixed(nus, V, d_meas)
    # wrong-drift controls: negate curvature; rescale rate by 0.9 / 1.1
    ctrls = []
    for cc in ([coef[0], coef[1], -coef[2]],
               [coef[0], 0.9 * coef[1], coef[2]],
               [coef[0], 1.1 * coef[1], coef[2]]):
        ctrls.append(cell_closure_tracked(nus, V, np.array(cc))[0])
    q_ctrl = np.nanmin(ctrls)
    # noise surrogate on the tracked grid
    fl, env = log_power_fluct(nus, V)
    Wr = np.exp(env) * (1.0 + np.std(np.abs(V) ** 2 / np.exp(env) - 1.0)
                        * RNG.standard_normal(len(nus)))
    Vs = np.sqrt(np.maximum(Wr, 1e-300)) * np.exp(1j * np.angle(V))
    q_surr, _ = cell_closure_tracked(nus, Vs, coef)
    bridge = gate and (q_trk * 10.0 <= q_ctrl) and (q_trk * 10.0 <= q_fix) \
        and (q_trk < q_surr)
    emit(f"r={r:2d} xi={xi} lf2={lf2} X={X:5.1f}  "
         f"dnu meas/law={d_meas/d_pred:5.3f}  combfrac={frac:5.3f} "
         f"gate={'Y' if gate else 'n'}  q_trk={q_trk:.3e}  q_fix={q_fix:.3e}  "
         f"ctrl={q_ctrl:.3e}  surr={q_surr:.3e}  cells={nc}  "
         f"BRIDGE={'CLOSES' if bridge else ('--gated--' if not gate else 'FAILS')}")
    return gate, bridge, d_meas / d_pred


def main():
    emit("BE BRIDGE -- measured clock feeding the carrier warp on the actual transform")
    emit("clock law in nu_J coordinate: 0.262*(lf2)^1.03*(X/8)^-1.04  (nu_clock = 2 nu_J)")
    emit("=" * 78)
    if not (anchor_strict() and anchor_drift()):
        emit("ANCHOR FAILED -- instrument invalid, no verdict on the bridge.")
        return
    emit("-" * 78)
    gated, closed, ratios = 0, 0, []
    for (l, f, X) in [(1, 1, 8.0), (1, 1, 16.0), (1, 2, 16.0)]:
        for xi in (1, 2):
            for r in (0, 1, 2, 3, 5, 8):
                g, b, rr = run_config(r, xi, l, f, X)
                if g:
                    gated += 1
                    ratios.append(rr)
                    if b:
                        closed += 1
    emit("-" * 78)
    if ratios:
        emit(f"clock cross-check vs nu_J law: ratio median={np.median(ratios):.3f} "
             f" range=({min(ratios):.3f},{max(ratios):.3f})")
    emit(f"gated configurations: {gated}   bridge closes on: {closed}")
    if gated == 0:
        emit("VERDICT: NO GATED CELLS -- comb too weak in scanned band; inconclusive.")
    elif closed == gated:
        emit("VERDICT: BRIDGE CLOSES on every gated configuration -- the measured clock")
        emit("         generates the closing warp on the actual transform's cell.")
    elif closed == 0:
        emit("VERDICT: BRIDGE DISCONFIRMED on every gated configuration (falsifiability")
        emit("         register: to be reported as prominently as a success).")
    else:
        emit(f"VERDICT: MIXED ({closed}/{gated}) -- report per-configuration; "
             f"productivity ledger separates clock law from deep-event visibility.")


if __name__ == "__main__":
    main()
