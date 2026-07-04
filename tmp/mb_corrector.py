#!/usr/bin/env python3
"""
mb_corrector.py — CORRECTOR SYNTHESIS: add tuned pure harmonics to the MB chart window
and ask whether the iterated-fold residue (the 0.441 +- 0.058 plateau of mb_iterfold)
can be CANCELLED.  The adversarial verifier of the fold-floor "invariant" verdict.

THE MOVE (owner's): instead of rescaling the window (the fold's only knob), ADD tones:
    W_corr(t) = W(t) + sum_{j=1..J} [a_j cos(2 pi w_j t) + b_j sin(2 pi w_j t)] * B(t)
where t = y/X (the window variable), W = B = the house never-clip bump (c=0.75, w=1.00,
exactly Altug's chart), and every harmonic H_j is a pure tone CARRIED BY the same bump.
So W_corr(t) = B(t) * m(t),  m(t) = 1 + trig polynomial — a shape move class that is
dense (J -> inf) in smooth reshapings over the fixed support; the fold's width-rescaled
optima are in its closure.  ONE shared corrector for ALL grid cells (a uniformizing
chart, stronger than the fold's 18 per-cell widths).

ADMISSIBILITY (never-clip legal; pre-registered):
  (A1) carrier: every H_j = B(t)*tone with B the compact C^inf bump on [0.25, 1.25],
       strictly inside the integration range [0.05, 1.45] — smooth entry (all
       derivatives vanish at the support edges), NO truncation of the integrand.
       Structural: holds for every candidate by construction.
  (A2) coefficient box max(|a_j|,|b_j|) <= 5.0 (penalty-enforced; keeps W_corr O(1)).
  (A3) entry positivity: m(t) > 0 at both support edges (no sign flip at entry).
       REQUIRED of any corrector used in the verdict; checked explicitly.
  (A4) global min/max of m over the support REPORTED (a signed smooth window remains
       never-clip legal — the law is about entry/truncation, not sign — but sign
       structure is part of the honest record).

BUILDS ON (anchor-gated, reused wholesale, not re-derived):
  * tmp/mb_iterfold.py    — cached-core engine (== be_exact_gauge.decay_exponent_fast
    to 1e-13), Nyquist-safe combos (ppc=8 in y AND x), bump_vec, envelope_gamma,
    run_fold (the fold-floor reference), smooth_scramble, run_anchor_gate.
  * recorded mb_iterfold results (mb_iterfold_results.txt): raw Nyquist-safe baseline
    spread 1.257, exact-gauged 1.150, K=12 fold sequence, K=13..24 attractor band
    0.441 +- 0.058 (the number under test).

PRE-REGISTERED PROTOCOL:

STEP 0 — ANCHOR GATE (fail = STOP):
  (i)   mb_iterfold.run_anchor_gate(fast=True) must PASS (= its `test` mode: ancestors,
        published 18-cell table, gauge hierarchy, engine identity).
  (ii)  raw Nyquist-safe baseline spread must reproduce 1.257 +- 0.02 and the exact-
        gauged spread 1.150 +- 0.02 on the same reduced grid.
  (iii) the K=12 fold sequence must reproduce the recorded values (max dev < 0.02);
        fold-floor reference = the recorded K=13..24 band 0.441 +- 0.058.
  (iv)  corrector engine identity: tensor path |b + A c| == direct integral with the
        modified window to 1e-9; vectorized envelope == house envelope_gamma to 1e-10.

STEP 1 — FREQUENCY DICTIONARIES (all four, compression curve spread-vs-J each):
  (i)   logprime : w_j = ln p, p in {2,3,5,7,11,13,17,19}  [cycles per unit t —
        convention pre-registered here; the FREE dictionary covers nearby scales].
  (ii)  winharm  : integer/half-integer harmonics of the natural window scale
        (support length 1 in t): w_j in {0.5, 1.0, ..., 4.0}.
  (iii) weylnu   : Weyl/character frequencies — harmonics of the r-ladder in the DUAL
        (nu) clock: Sym^r character frequencies are the half-integers (r+1)/2; a shift
        of nu by dnu is the tone w = X*dnu/(4 lf^2) in t (cell-dependent LAW, shared
        coefficients): dnu in {0.5, 1.0, ..., 4.0}.
  (iv)  free     : dense frequency grid w in [0.25, 5.00] step 0.05, J <= 4, greedy
        with 2-parameter screening (top 5 -> full refit).
  Fit: GREEDY selection with FULL coefficient refit at each step (Nelder-Mead, warm
  start + one chained restart, deterministic); dictionaries (i)-(iii) J = 1..8, plus
  an all-at-once J=8 refit from zeros (curve takes the min).  Objective = std of the
  gamma surface (house envelope fit, nu <= 24) across the 18-cell grid; invalid
  (parity-null) cells penalized; coefficient box per (A2).

STEP 2 — VERDICT (pre-registered thresholds; fold band 0.441 +- 0.058, BREAK = mean
  minus two widths = 0.325):
  (c) PLATEAU BREAK: ANY admissible ((A1)-(A3)) corrector reaches full-grid spread
      < 0.325  =>  the 0.441 "invariant" verdict of mb_iterfold needs REVISION (the
      fold family was too narrow).  OVERRIDES the (a)/(b) labels; reported first.
  (a) COMPRESSION/IDENTIFIED: some single dictionary reaches spread <= 0.325 at
      J <= 4 AND the scrambled control passes; the transport test is reported and a
      transport failure demotes (a) to "in-sample identification only".
  (b) NO COMPRESSION: best spread across all dictionaries at J = 4 stays > 0.40 AND
      at J = 8 stays > 0.35 (dof ~ #cells needed to move) => residue incompressible
      BY THIS SYNTHESIS (greedy+NM is heuristic: spreads are upper bounds on the
      class optimum; stated as such).
  Anything else => AMBIGUOUS.  Any of the three is a result; (a) is not forced.

STEP 3 — CONTROLS (mandatory):
  (i)   scrambled kernel (mb_iterfold.smooth_scramble, frozen seed 20260703): the same
        synthesis (winning dictionary, same J*) must NOT compress comparably.
        PASS iff (spread_J*/spread_0)_scrambled - (spread_J*/spread_0)_real >= 0.15.
  (ii)  TRANSPORT: parity split of the grid (i_xi + i_lf + i_X even -> train, odd ->
        test; 9/9, both X, all xi, all (l,f) in each half); refit the winning
        dictionary at J* on train only; evaluate on test.  R = (1 - s_test/s0_test) /
        (1 - s_train/s0_train); PASS iff R >= 0.5.  (The fold's law FAILED its
        hold-out; this is the corrector's version of that test.)
  (iii) admissibility of the winner per (A3)/(A4) + Nyquist spot-check: winner-
        corrected gamma on the worst combo at 2x ny, |dgamma| < 0.15 (house).

TIERS: [anchor] / [measured] / [interpretation].  FALSIFICATION register:
  * anchor gate fail                       -> STOP, no synthesis run;
  * scrambled compresses comparably       -> any COMPRESSION claim ((a)/(c)) is VOID
        (the synthesis trivially fits anything, per the mission protocol's triviality
        guard); against a (b) no-compression null the same outcome CORROBORATES it
        (what compression exists is generic).  [Scoping of this clause to (a)/(c)
        was a wiring correction made after the first full run and is labeled as
        such in the results file; no [measured] number changed.]
  * winner fails (A3)                      -> excluded from verdict, next-best used;
  * transport fail                         -> identification demoted, reported at
                                              full prominence (as the fold's was).

Run:
  python3 mb_corrector.py test      # STEP 0 anchor gate only
  python3 mb_corrector.py results   # full protocol -> mb_corrector_results.txt + summary
"""

import sys
import os
import math
import time

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mb_iterfold as IF
import mb_uniform as MB                    # noqa: F401 (ancestor; loaded so gates exist)
import be_exact_gauge as BEG               # noqa: F401

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------------------
# PRE-REGISTERED CONSTANTS
# ---------------------------------------------------------------------------
GRID = IF.GRID
NUS = np.asarray(IF.NUS, dtype=float)
C0, W0 = IF.C0, IF.W0

FOLD_BAND = (0.441, 0.058)                     # mb_iterfold K=13..24 attractor band
BREAK_THRESH = FOLD_BAND[0] - 2.0 * FOLD_BAND[1]   # 0.325 — verdict (c) trigger
NOCOMP_J4, NOCOMP_J8 = 0.40, 0.35              # verdict (b) triggers
CBOX = 5.0                                     # (A2) coefficient box
PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)
HALFHARM = np.arange(1, 9) * 0.5               # {0.5 .. 4.0}
FREE_GRID = np.round(np.arange(0.25, 5.0001, 0.05), 4)
FREE_JMAX = 4
SCREEN_TOP = 5
NM_FEV_PER_DIM = 300
SCR_MARGIN = 0.15                              # control (i) pass margin
TRANSPORT_R = 0.5                              # control (ii) pass threshold

# [anchor] recorded mb_iterfold numbers (mb_iterfold_results.txt)
REC_RAW_STD = 1.257
REC_GAU_STD = 1.150
REC_FOLD_SEQ = np.array([1.257, 0.640, 0.522, 0.478, 0.475, 0.427, 0.451, 0.440,
                         0.409, 0.419, 0.416, 0.403, 0.541])
REC_SCR_STD0 = 2.382

# fast envelope constants (bins for NUS = [2,4,8,16,24]; bin (33,100) empty)
_BINX = np.log(np.sqrt(np.array([2 * 4, 4 * 8, 8 * 16, 16 * 33], dtype=float)))
_XC = _BINX - _BINX.mean()
_SXX = float((_XC ** 2).sum())


# ---------------------------------------------------------------------------
# FAST GAMMA (vectorized twin of IF.envelope_gamma; identity checked in gate)
# ---------------------------------------------------------------------------

def fast_gammas(Jmat):
    """gamma per row of Jmat (n,5) — closed-form least-squares slope on the house
    envelope bins; exact fallback to IF.envelope_gamma when a bin underflows."""
    Jmat = np.asarray(Jmat, dtype=float)
    v = np.column_stack([Jmat[:, 0], Jmat[:, 1], Jmat[:, 2],
                         np.maximum(Jmat[:, 3], Jmat[:, 4])])
    out = np.empty(Jmat.shape[0])
    good = (v > 1e-18).all(axis=1)
    if good.any():
        out[good] = -(np.log(v[good]) @ _XC) / _SXX
    for i in np.where(~good)[0]:
        out[i] = IF.envelope_gamma(NUS, Jmat[i])
    out[Jmat.max(axis=1) < IF.NULL_FLOOR] = np.nan       # parity-null convention
    return out


# ---------------------------------------------------------------------------
# TENSORS — J is linear in the window, so amplitudes are |b + A c|
# ---------------------------------------------------------------------------

def cell_pieces(cell, combos, rowmap):
    combo = combos[(cell[1], cell[2], cell[3])]
    rw = rowmap[cell]
    ys, dy, X, lf2 = combo["ys"], combo["dy"], combo["X"], combo["lf2"]
    t = ys / X
    base = IF.bump_vec(t, C0, W0) * ys * rw              # (ny,) complex
    Yp = np.exp(-2j * np.pi * np.outer(NUS, ys) / (4.0 * lf2))   # (5, ny)
    return t, base, Yp, dy


def tensors_for(cells, combos, rowmap, omegas_of):
    """b (n,5) complex; A (n,5,2K) complex with columns (cos_k, sin_k) per candidate.
    omegas_of(cell) -> length-K array of tone frequencies (cycles per unit t)."""
    n = len(cells)
    K = len(omegas_of(cells[0]))
    b = np.zeros((n, 5), complex)
    A = np.zeros((n, 5, 2 * K), complex)
    for i, cell in enumerate(cells):
        t, base, Yp, dy = cell_pieces(cell, combos, rowmap)
        b[i] = Yp @ base * dy
        ph = 2.0 * np.pi * np.outer(np.asarray(omegas_of(cell), float), t)  # (K, ny)
        tones = np.empty((2 * K, len(t)))
        tones[0::2] = np.cos(ph)
        tones[1::2] = np.sin(ph)
        A[i] = ((tones * base[None, :]) @ Yp.T).T * dy
    return b, A


def sub_A(A, chosen):
    """Column pairs of the chosen candidates, in order."""
    return np.concatenate([A[:, :, 2 * c:2 * c + 2] for c in chosen], axis=2)


# ---------------------------------------------------------------------------
# OBJECTIVE + OPTIMIZER (deterministic)
# ---------------------------------------------------------------------------

def spread_of(coefs, b, A):
    Jmat = np.abs(b + (A @ coefs if len(coefs) else 0.0))
    g = fast_gammas(Jmat)
    valid = np.isfinite(g)
    pen = 10.0 * float((~valid).sum())
    if len(coefs):
        over = float(np.max(np.abs(coefs))) - CBOX
        if over > 0:
            pen += 10.0 * over
    if valid.sum() < 4:
        return 1e3 + pen
    return float(np.std(g[valid])) + pen


def mean_gamma(coefs, b, A):
    Jmat = np.abs(b + (A @ coefs if len(coefs) else 0.0))
    g = fast_gammas(Jmat)
    return float(np.nanmean(g))


def nm_fit(b, A, x0, fev=None):
    fev = fev or NM_FEV_PER_DIM * max(4, len(x0))
    opts = dict(maxfev=fev, xatol=1e-4, fatol=1e-6)
    r = minimize(spread_of, x0, args=(b, A), method="Nelder-Mead", options=opts)
    r2 = minimize(spread_of, r.x, args=(b, A), method="Nelder-Mead", options=opts)
    return (r2.x, float(r2.fun)) if r2.fun < r.fun else (r.x, float(r.fun))


def greedy_fit(b, A, labels, Jmax, screen=False, emit=lambda s: None):
    """Greedy candidate selection with full refit; returns per-J records."""
    ncand = A.shape[2] // 2
    chosen, coef = [], np.zeros(0)
    s0 = spread_of(coef, b, A[:, :, :0])
    curve = [s0]
    recs = [dict(J=0, spread=s0, chosen=[], coef=coef.copy(),
                 mean=mean_gamma(coef, b, A[:, :, :0]))]
    for step in range(Jmax):
        cands = [c for c in range(ncand) if c not in chosen]
        if screen and len(cands) > SCREEN_TOP:
            scr = []
            Aold = sub_A(A, chosen) if chosen else A[:, :, :0]
            for c in cands:
                Atr = np.concatenate([Aold, A[:, :, 2 * c:2 * c + 2]], axis=2)

                def f2(c2, _A=Atr):
                    return spread_of(np.concatenate([coef, c2]), b, _A)

                r = minimize(f2, np.zeros(2), method="Nelder-Mead",
                             options=dict(maxfev=160, xatol=1e-3, fatol=1e-5))
                scr.append((float(r.fun), c))
            scr.sort()
            cands = [c for _, c in scr[:SCREEN_TOP]]
        best = None
        for c in cands:
            Atr = sub_A(A, chosen + [c])
            x0 = np.concatenate([coef, np.zeros(2)])
            x, fval = nm_fit(b, Atr, x0)
            if best is None or fval < best[0]:
                best = (fval, c, x)
        fval, c, x = best
        chosen.append(c)
        coef = x
        curve.append(min(fval, curve[-1]))
        recs.append(dict(J=len(chosen), spread=fval, chosen=list(chosen),
                         coef=coef.copy(),
                         mean=mean_gamma(coef, b, sub_A(A, chosen))))
        emit(f"        J={len(chosen)}: spread {fval:.3f}  (+{labels[c]})")
    return dict(curve=np.array(curve), recs=recs, chosen=chosen, coef=coef)


# ---------------------------------------------------------------------------
# DICTIONARIES
# ---------------------------------------------------------------------------

def dict_defs():
    lp = np.log(np.array(PRIMES, float))
    hh = HALFHARM.copy()
    fr = FREE_GRID.copy()
    return {
        "logprime": dict(labels=[f"ln{p}({math.log(p):.3f})" for p in PRIMES],
                         omegas=(lambda cell, _v=lp: _v), Jmax=8, screen=False),
        "winharm":  dict(labels=[f"w={x:.1f}" for x in hh],
                         omegas=(lambda cell, _v=hh: _v), Jmax=8, screen=False),
        "weylnu":   dict(labels=[f"dnu={x:.1f}" for x in hh],
                         omegas=(lambda cell, _v=hh:
                                 _v * cell[3] / (4.0 * cell[1] * cell[2] ** 2)),
                         Jmax=8, screen=False),
        "free":     dict(labels=[f"w={x:.2f}" for x in fr],
                         omegas=(lambda cell, _v=fr: _v),
                         Jmax=FREE_JMAX, screen=True),
    }


def split_train_test():
    train, test = [], []
    for ix, xi in enumerate((0, 2, 6)):
        for il, (l, f) in enumerate(((1, 1), (2, 1), (1, 2))):
            for iX, X in enumerate((8.0, 16.0)):
                (train if (ix + il + iX) % 2 == 0 else test).append((xi, l, f, X))
    return train, test


# ---------------------------------------------------------------------------
# ADMISSIBILITY
# ---------------------------------------------------------------------------

def modulation_stats(omegas, coef):
    """m(t) = 1 + sum a cos + b sin on a dense support grid; returns stats."""
    t = np.linspace(0.25, 1.25, 4001)
    m = np.ones_like(t)
    for k, w in enumerate(omegas):
        m += coef[2 * k] * np.cos(2 * np.pi * w * t) + coef[2 * k + 1] * np.sin(2 * np.pi * w * t)
    B = IF.bump_vec(t, C0, W0)
    Wc = B * m
    return dict(m_min=float(m.min()), m_max=float(m.max()),
                m_lo=float(m[0]), m_hi=float(m[-1]),
                W_min=float(Wc.min()), W_max=float(Wc.max()),
                entry_ok=bool(m[0] > 0 and m[-1] > 0))


def admissibility(dname, ddef, chosen, coef, cells):
    """(A3)/(A4) for the winner; per-cell for the cell-dependent (weylnu) law."""
    if dname == "weylnu":
        stats = None
        for cell in cells:
            ws = ddef["omegas"](cell)[chosen]
            st = modulation_stats(ws, coef)
            if stats is None or st["m_min"] < stats["m_min"]:
                stats = st
            stats["entry_ok"] = stats["entry_ok"] and st["entry_ok"]
        return stats
    ws = ddef["omegas"](cells[0])[chosen]
    return modulation_stats(ws, coef)


# ---------------------------------------------------------------------------
# STEP 0 — ANCHOR GATE
# ---------------------------------------------------------------------------

def engine_identity(combos, rowmap, emit):
    """Gate (iv): tensor path == direct-integral with the modified window; fast
    envelope == house envelope_gamma."""
    dd = dict_defs()["logprime"]
    cells = [GRID[0], GRID[7], GRID[17]]
    b, A = tensors_for(cells, combos, rowmap, dd["omegas"])
    coef = np.zeros(16)
    coef[0], coef[1], coef[4], coef[5] = 0.30, -0.20, 0.10, 0.05   # ln2 + ln5 tones
    J_tensor = np.abs(b + A @ coef)
    maxdev = 0.0
    for i, cell in enumerate(cells):
        combo = combos[(cell[1], cell[2], cell[3])]
        rw = rowmap[cell]
        ys, X = combo["ys"], combo["X"]
        t = ys / X
        m = np.ones_like(t)
        ws = dd["omegas"](cell)
        for k, w in enumerate(ws):
            m += coef[2 * k] * np.cos(2 * np.pi * w * t) + coef[2 * k + 1] * np.sin(2 * np.pi * w * t)
        prof = IF.bump_vec(t, C0, W0) * m * ys * rw
        row_scale = float(J_tensor[i].max())
        for n, nu in enumerate(NUS):
            yph = np.exp(-2j * np.pi * (ys * nu) / (4.0 * combo["lf2"]))
            Jdir = abs(np.sum(prof * yph) * combo["dy"])
            maxdev = max(maxdev, abs(Jdir - J_tensor[i, n]) / row_scale)
    emit(f"      tensor |b+Ac| == direct modified-window integral: max dev / cell scale"
         f" {maxdev:.2e}  (summation-order fp only)")
    ok_t = maxdev < 1e-9
    # fast envelope vs house envelope on the baseline J matrix of the full grid
    bg, _ = tensors_for(GRID, combos, rowmap, dd["omegas"])
    Jbase = np.abs(bg)
    g_fast = fast_gammas(Jbase)
    dev_e = 0.0
    for i in range(len(GRID)):
        g_house = IF.envelope_gamma(NUS, Jbase[i])
        dev_e = max(dev_e, abs(g_fast[i] - g_house))
    emit(f"      fast envelope == IF.envelope_gamma over 18 cells: max dev {dev_e:.2e}")
    return ok_t and dev_e < 1e-10, Jbase


def run_gate(full=True, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    emit("=" * 78)
    emit("STEP 0 — ANCHOR GATE (mb_iterfold gate + recorded-baseline + fold-floor +")
    emit("         corrector-engine identity; GATE FAIL = STOP)")
    emit("=" * 78)

    emit("\n[anchor] (i) mb_iterfold.run_anchor_gate(fast=True):")
    ok_if, _ = IF.run_anchor_gate(fast=True, verbose=False)
    emit(f"      -> {'PASS' if ok_if else 'FAIL'}")
    if not ok_if:
        emit("\n[anchor] GATE VERDICT: FAIL (ancestral gate)")
        return False, None, None, "\n".join(out)

    emit("\n[anchor] building Nyquist-safe production caches (mb_iterfold parameters):")
    t0 = time.time()
    combos = {}
    for (l, f) in ((1, 1), (2, 1), (1, 2)):
        for X in (8.0, 16.0):
            combos[(l, f, X)] = IF.build_combo(l, f, X, xi_max=6)
            c = combos[(l, f, X)]
            emit(f"      combo (l,f,X)=({l},{f},{X}): ny={c['ny']} nx={c['nx']}")
    emit(f"      [cache build {time.time()-t0:.0f}s]")
    rowmap = {cell: IF.rowint_of(combos[(cell[1], cell[2], cell[3])], cell[0], 0)
              for cell in GRID}

    emit("\n[anchor] (ii) recorded baselines (mb_iterfold_results.txt):")
    gs_raw, gs_gau = [], []
    for cell in GRID:
        combo = combos[(cell[1], cell[2], cell[3])]
        graw, _ = IF.gamma_of(combo, rowmap[cell], C0, W0, gauged=False)
        ggau, _ = IF.gamma_of(combo, rowmap[cell], C0, W0, gauged=True)
        gs_raw.append(graw)
        gs_gau.append(ggau)
    raw_std, gau_std = float(np.std(gs_raw)), float(np.std(gs_gau))
    emit(f"      raw Nyquist-safe spread {raw_std:.3f} (recorded {REC_RAW_STD}; tol 0.02)")
    emit(f"      exact-gauged spread    {gau_std:.3f} (recorded {REC_GAU_STD}; tol 0.02)")
    ok_base = abs(raw_std - REC_RAW_STD) < 0.02 and abs(gau_std - REC_GAU_STD) < 0.02

    ok_fold = True
    if full:
        emit("\n[anchor] (iii) K=12 fold reproduction (IF.run_fold, identical protocol):")
        fold = IF.run_fold(GRID, combos, rowmap, gauged=False, law=True)
        dev = float(np.max(np.abs(fold["seq"] - REC_FOLD_SEQ)))
        emit("      std_k: " + " ".join(f"{s:.3f}" for s in fold["seq"]))
        emit(f"      max |std_k - recorded| = {dev:.4f}  (tol 0.02)")
        emit(f"      fold-floor reference: recorded K=13..24 band {FOLD_BAND[0]} +- {FOLD_BAND[1]}"
             f"  -> BREAK threshold {BREAK_THRESH:.3f}")
        ok_fold = dev < 0.02

    emit("\n[anchor] (iv) corrector engine identity:")
    ok_eng, Jbase = engine_identity(combos, rowmap, emit)
    g0 = fast_gammas(Jbase)
    s0 = float(np.std(g0[np.isfinite(g0)]))
    emit(f"      c=0 tensor baseline spread {s0:.3f} == raw baseline {raw_std:.3f}"
         f"  |d|={abs(s0-raw_std):.2e}")
    ok_eng = ok_eng and abs(s0 - raw_std) < 1e-9

    gate = ok_if and ok_base and ok_fold and ok_eng
    emit(f"\n[anchor] GATE VERDICT: {'PASS' if gate else 'FAIL'}"
         f"  (ancestral {ok_if}, baselines {ok_base}, fold {ok_fold}, engine {ok_eng})")
    emit("=" * 78)
    return gate, combos, rowmap, "\n".join(out)


# ---------------------------------------------------------------------------
# STEP 1 — SYNTHESIS OVER THE FOUR DICTIONARIES
# ---------------------------------------------------------------------------

def run_synthesis(combos, rowmap, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    emit("=" * 78)
    emit("STEP 1 — CORRECTOR SYNTHESIS (four pre-registered dictionaries; greedy + full")
    emit(f"refit, NM deterministic; objective = std(gamma) across the 18-cell grid;")
    emit(f"box |c|<={CBOX}; baseline spread = raw Nyquist-safe c=0)")
    emit("=" * 78)

    dds = dict_defs()
    results = {}
    for name, dd in dds.items():
        t0 = time.time()
        emit(f"\n[measured] dictionary '{name}' "
             f"({len(dd['labels'])} candidates, Jmax={dd['Jmax']}"
             f"{', screened' if dd['screen'] else ''}):")
        b, A = tensors_for(GRID, combos, rowmap, dd["omegas"])
        fit = greedy_fit(b, A, dd["labels"], dd["Jmax"], screen=dd["screen"], emit=emit)
        # all-at-once J=8 refit from zeros (unscreened dicts only; curve takes min)
        if not dd["screen"]:
            xall, fall = nm_fit(b, A, np.zeros(A.shape[2]))
            emit(f"        all-at-once J=8 from zeros: spread {fall:.3f}"
                 f" (greedy J=8: {fit['curve'][-1]:.3f})")
            if fall < fit["curve"][-1]:
                fit["curve"][-1] = fall
                fit["recs"][-1] = dict(J=8, spread=fall, chosen=list(range(8)),
                                       coef=xall, mean=mean_gamma(xall, b, A))
                fit["chosen"], fit["coef"] = list(range(8)), xall
        results[name] = dict(fit=fit, b=b, A=A, dd=dd)
        emit(f"      compression curve (spread vs J): "
             + " ".join(f"{s:.3f}" for s in fit["curve"]))
        emit(f"      mean-gamma path: "
             + " ".join(f"{r['mean']:.2f}" for r in fit["recs"]))
        emit(f"      [{time.time()-t0:.0f}s]")

    emit(f"\n[measured] COMPRESSION CURVES vs the fold floor "
         f"({FOLD_BAND[0]} +- {FOLD_BAND[1]}; BREAK < {BREAK_THRESH:.3f}):")
    emit(f"    {'J':>3} " + " ".join(f"{n:>9}" for n in dds))
    Jm = max(dd["Jmax"] for dd in dds.values())
    for J in range(Jm + 1):
        row = [f"{J:>3} "]
        for n in dds:
            c = results[n]["fit"]["curve"]
            row.append(f"{c[J]:>9.3f}" if J < len(c) else f"{'-':>9}")
        emit("    " + " ".join(row))
    emit("=" * 78)
    return results, "\n".join(out)


# ---------------------------------------------------------------------------
# STEP 2 — VERDICT
# ---------------------------------------------------------------------------

def pick_winner(results):
    """Best admissible (A3) record over all (dict, J); ties (within 1e-3) broken
    toward the smallest J (parsimony)."""
    ranked = []
    for name, res in results.items():
        for rec in res["fit"]["recs"]:
            if rec["J"] == 0:
                continue
            ranked.append((rec["spread"], name, rec))
    ranked.sort(key=lambda z: (round(z[0] / 1e-3), z[2]["J"]))
    for spread, name, rec in ranked:
        st = admissibility(name, results[name]["dd"], rec["chosen"], rec["coef"], GRID)
        if st["entry_ok"] and abs(np.max(np.abs(rec["coef"]))) <= CBOX + 1e-9:
            return name, rec, st, ranked
    return None, None, None, ranked


def read_verdict(results, winner_name, winner_rec, scr_ok):
    best_j4 = min(res["fit"]["curve"][min(4, len(res["fit"]["curve"]) - 1)]
                  for res in results.values())
    best_j8 = min(res["fit"]["curve"][-1] for res in results.values())
    best_any = winner_rec["spread"] if winner_rec else best_j8
    fired_c = best_any < BREAK_THRESH
    fired_a = (fired_c and winner_rec is not None and winner_rec["J"] <= 4 and scr_ok)
    fired_b = (best_j4 > NOCOMP_J4) and (best_j8 > NOCOMP_J8)
    if fired_c:
        v = "(c) PLATEAU BREAK" + (" + (a) IDENTIFIED" if fired_a else "")
    elif fired_b:
        v = "(b) NO COMPRESSION"
    else:
        v = "AMBIGUOUS"
    return v, dict(best_any=best_any, best_j4=best_j4, best_j8=best_j8,
                   fired_a=fired_a, fired_b=fired_b, fired_c=fired_c)


# ---------------------------------------------------------------------------
# STEP 3 — CONTROLS
# ---------------------------------------------------------------------------

def run_controls(combos, rowmap, results, winner_name, winner_rec, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    emit("=" * 78)
    emit("STEP 3 — CONTROLS (mandatory)")
    emit("=" * 78)
    dd = results[winner_name]["dd"]
    Jstar = winner_rec["J"] if winner_rec["J"] <= 4 else 4
    emit(f"\n    winning dictionary '{winner_name}', J* = {Jstar} (<=4 for controls)")

    # (i) scrambled kernel
    emit(f"\n[measured] (i) SCRAMBLED control (IF.smooth_scramble, seed {IF.SEED_SCRAMBLE}),")
    emit(f"    identical synthesis: dictionary '{winner_name}', greedy to J={Jstar}:")
    scr = IF.smooth_scramble(combos, GRID)
    rowmap_scr = {cell: rowmap[cell] * scr[cell] for cell in GRID}
    b_s, A_s = tensors_for(GRID, combos, rowmap_scr, dd["omegas"])
    fit_s = greedy_fit(b_s, A_s, dd["labels"], Jstar, screen=dd["screen"], emit=emit)
    curve_r = results[winner_name]["fit"]["curve"]
    ratio_r = curve_r[Jstar] / curve_r[0]
    ratio_s = fit_s["curve"][-1] / fit_s["curve"][0]
    emit(f"      scrambled curve: " + " ".join(f"{s:.3f}" for s in fit_s["curve"])
         + f"   (std_0 {fit_s['curve'][0]:.3f}; recorded scrambled base {REC_SCR_STD0})")
    emit(f"      compression ratio at J={Jstar}: real {ratio_r:.3f} vs scrambled {ratio_s:.3f}"
         f"   (pass margin {SCR_MARGIN})")
    scr_ok = (ratio_s - ratio_r) >= SCR_MARGIN
    emit(f"      -> scrambled control {'PASS (does NOT compress comparably)' if scr_ok else 'FAIL: compresses comparably — the observed compression is GENERIC fitting capacity, not kernel-specific cancellation (voids any (a)/(c) claim; corroborates a (b) null)'}")

    # (ii) transport
    train, test = split_train_test()
    emit(f"\n[measured] (ii) TRANSPORT — parity split (9 train / 9 test), refit on train")
    emit(f"    only ('{winner_name}', greedy to J={Jstar}), evaluate held-out:")
    b_tr, A_tr = tensors_for(train, combos, rowmap, dd["omegas"])
    fit_tr = greedy_fit(b_tr, A_tr, dd["labels"], Jstar, screen=dd["screen"],
                        emit=lambda s: None)
    b_te, A_te = tensors_for(test, combos, rowmap, dd["omegas"])
    s0_tr, s_tr = fit_tr["curve"][0], fit_tr["curve"][-1]
    s0_te = spread_of(np.zeros(0), b_te, A_te[:, :, :0])
    s_te = spread_of(fit_tr["coef"], b_te, sub_A(A_te, fit_tr["chosen"]))
    freqs_tr = [dd["labels"][c] for c in fit_tr["chosen"]]
    emit(f"      train: {s0_tr:.3f} -> {s_tr:.3f}   (chose: {', '.join(freqs_tr)})")
    emit(f"      test : {s0_te:.3f} -> {s_te:.3f}   (transported coefficients)")
    comp_tr = 1.0 - s_tr / s0_tr
    comp_te = 1.0 - s_te / s0_te
    R = comp_te / comp_tr if comp_tr > 1e-9 else float("nan")
    emit(f"      compression train {100*comp_tr:.0f}% / test {100*comp_te:.0f}%"
         f"  -> R = {R:.2f}  (pass >= {TRANSPORT_R})")
    trans_ok = np.isfinite(R) and R >= TRANSPORT_R
    emit(f"      -> transport {'PASS (corrector is a transportable law)' if trans_ok else 'FAIL (in-sample only — same failure mode as the fold law)'}")

    # (iii) admissibility + Nyquist spot-check on the winner
    emit(f"\n[measured] (iii) ADMISSIBILITY of the winner (J={winner_rec['J']}):")
    st = admissibility(winner_name, dd, winner_rec["chosen"], winner_rec["coef"], GRID)
    emit(f"      modulation m(t): min {st['m_min']:+.3f} max {st['m_max']:+.3f}; "
         f"entry values m(0.25)={st['m_lo']:+.3f}, m(1.25)={st['m_hi']:+.3f}")
    emit(f"      corrected window W_corr: min {st['W_min']:+.3f} max {st['W_max']:+.3f};"
         f" support [0.25,1.25] (compact, C^inf entry — carrier bump) — no truncation")
    emit(f"      max |coef| = {np.max(np.abs(winner_rec['coef'])):.3f} (box {CBOX})")
    emit(f"      entry sign flips: {'NONE (A3 PASS)' if st['entry_ok'] else 'PRESENT (A3 FAIL)'}"
         f"; global sign: {'nonnegative' if st['m_min'] >= 0 else 'signed interior (reported per A4)'}")

    combo2 = IF.build_combo(1, 1, 16.0, xi_max=6, ny_mult=2.0)
    devs = []
    for xi in (0, 6):
        cell = (xi, 1, 1, 16.0)
        for combo, rmap in ((combos[(1, 1, 16.0)], rowmap[cell]),
                            (combo2, IF.rowint_of(combo2, xi, 0))):
            ys, X = combo["ys"], combo["X"]
            t = ys / X
            m = np.ones_like(t)
            ws = dd["omegas"](cell)
            for k, c in enumerate(winner_rec["chosen"]):
                m += (winner_rec["coef"][2 * k] * np.cos(2 * np.pi * ws[c] * t)
                      + winner_rec["coef"][2 * k + 1] * np.sin(2 * np.pi * ws[c] * t))
            prof = IF.bump_vec(t, C0, W0) * m * ys * rmap
            Js = np.array([abs(np.sum(prof * np.exp(-2j * np.pi * ys * nu / (4.0 * combo["lf2"])))
                               * combo["dy"]) for nu in NUS])
            devs.append(IF.envelope_gamma(NUS, Js))
    d0, d6 = abs(devs[0] - devs[1]), abs(devs[2] - devs[3])
    emit(f"      Nyquist spot-check, winner-corrected gamma at 2x ny on (1,1,16):"
         f" |d|={d0:.3f} (xi=0), {d6:.3f} (xi=6)  (house tol 0.15)")
    conv_ok = d0 < 0.15 and d6 < 0.15
    emit(f"      -> convergence {'PASS' if conv_ok else 'FAIL'}")
    emit("=" * 78)
    return dict(scr_ok=scr_ok, trans_ok=trans_ok, adm=st, conv_ok=conv_ok, R=R,
                ratio_r=ratio_r, ratio_s=ratio_s, s_tr=(s0_tr, s_tr), s_te=(s0_te, s_te),
                freqs_tr=freqs_tr, Jstar=Jstar, text="\n".join(out))


# ---------------------------------------------------------------------------
# drivers
# ---------------------------------------------------------------------------

def run_tests():
    print("mb_corrector self-tests = STEP 0 ANCHOR GATE (fold repro deferred to results)")
    ok, _, _, _ = run_gate(full=False)
    print(f"\nANCHOR GATE: {'PASS' if ok else 'FAIL'}")
    return ok


def run_results():
    t_start = time.time()
    buf = []
    ok, combos, rowmap, txt0 = run_gate(full=True)
    buf.append(txt0)
    if not ok:
        buf.append("\n*** ANCHOR GATE FAILED — protocol stopped (pre-registered). ***")
        _write(buf)
        return

    results, txt1 = run_synthesis(combos, rowmap)
    buf.append("\n\n" + txt1)

    winner_name, winner_rec, winner_adm, ranked = pick_winner(results)
    if winner_rec is None:
        buf.append("\n*** no admissible corrector found (all fail A3) — reporting raw ranking ***")
        winner_name, winner_rec = ranked[0][1], ranked[0][2]

    ctrl = run_controls(combos, rowmap, results, winner_name, winner_rec)
    buf.append("\n\n" + ctrl["text"])

    verdict, vd = read_verdict(results, winner_name, winner_rec, ctrl["scr_ok"])

    fin = []
    fin.append("=" * 78)
    fin.append("VERDICT (pre-registered reading; STEP 2)")
    fin.append("=" * 78)
    dd = results[winner_name]["dd"]
    freqs = [dd["labels"][c] for c in winner_rec["chosen"]]
    coefs = ", ".join(f"({winner_rec['coef'][2*k]:+.3f},{winner_rec['coef'][2*k+1]:+.3f})"
                      for k in range(winner_rec["J"]))
    fin.append(f"[measured] fold floor under test: {FOLD_BAND[0]} +- {FOLD_BAND[1]}"
               f" (BREAK < {BREAK_THRESH:.3f}; NO-COMP J4 > {NOCOMP_J4}, J8 > {NOCOMP_J8})")
    fin.append(f"[measured] best admissible corrector: dict '{winner_name}', J={winner_rec['J']},"
               f" spread {winner_rec['spread']:.3f} (baseline {results[winner_name]['fit']['curve'][0]:.3f})")
    fin.append(f"           frequencies: {', '.join(freqs)}")
    fin.append(f"           coefficients (a,b): {coefs}")
    fin.append(f"[measured] best at J<=4 across dicts: {vd['best_j4']:.3f};"
               f" best at Jmax: {vd['best_j8']:.3f}")
    fin.append(f"[measured] best corrector vs fold floor: {vd['best_any']:.3f} vs"
               f" {FOLD_BAND[0]} +- {FOLD_BAND[1]} — the shared-corrector class"
               f" {'BEATS' if vd['best_any'] < FOLD_BAND[0] - FOLD_BAND[1] else 'DOES NOT even reach'}"
               f" the fold floor")
    if not ctrl["scr_ok"] and (vd["fired_c"] or vd["fired_a"]):
        fin.append("[measured] SCRAMBLED CONTROL FAILED against a compression claim ->")
        fin.append("    pre-registered triviality guard: verdict VOID")
        verdict = "VOID (compression claim, scrambled control failed)"
    elif not ctrl["scr_ok"]:
        fin.append("[measured] scrambled control: compresses comparably (FAIL of the margin")
        fin.append("    test) — with NO compression claim on the table this corroborates the")
        fin.append("    null: the achieved compression is generic, not kernel-specific.")
        fin.append("    (Wiring correction, labeled: the VOID clause is scoped to (a)/(c)")
        fin.append("    compression claims per the mission protocol; first-run label was VOID.)")
    fin.append(f"\n[measured] VERDICT: {verdict}")
    if vd["fired_c"]:
        fin.append(f"[interpretation] the 0.441 'invariant' of mb_iterfold is FAMILY-RELATIVE:")
        fin.append(f"    an admissible pure-harmonic corrector beats the fold band by more than")
        fin.append(f"    its width. The fold family (width-only) was too narrow; mb_iterfold's")
        fin.append(f"    plateau verdict needs REVISION as pre-registered (outcome (c)).")
        if vd["fired_a"]:
            fin.append(f"[interpretation] (a) also fires: J<={winner_rec['J']} harmonics from")
            fin.append(f"    '{winner_name}' cancel most of the residue — the invariant is")
            fin.append(f"    identified by its cancellation spectrum (frequencies above)."
                       + (" Transport PASSED." if ctrl["trans_ok"] else
                          " TRANSPORT FAILED -> in-sample identification only (demoted)."))
    elif vd["fired_b"]:
        fin.append(f"[interpretation] (b): no dictionary compresses the residue at J<=4 and even")
        fin.append(f"    J=8 (dof ~ #cells) stays above {NOCOMP_J8} — the fold plateau behaves as")
        fin.append(f"    incompressible/noise-like content AGAINST PURE-HARMONIC MODULATION;")
        fin.append(f"    the 0.441 invariant SURVIVES its adversarial verifier. (Heuristic-")
        fin.append(f"    optimizer caveat: spreads are upper bounds on the class optimum.)")
    else:
        fin.append(f"[interpretation] AMBIGUOUS: compression lands between the pre-registered")
        fin.append(f"    branches (below fold band but not below BREAK, or J>4 needed).")
    fin.append(f"\n[controls] scrambled: {'PASS' if ctrl['scr_ok'] else 'FAIL'};"
               f" transport R={ctrl['R']:.2f} ({'PASS' if ctrl['trans_ok'] else 'FAIL'});"
               f" admissibility entry {'PASS' if ctrl['adm']['entry_ok'] else 'FAIL'}"
               f" (m range [{ctrl['adm']['m_min']:+.2f},{ctrl['adm']['m_max']:+.2f}]);"
               f" Nyquist {'PASS' if ctrl['conv_ok'] else 'FAIL'}")
    fin.append(f"[budget] total wall time {time.time()-t_start:.0f}s")
    fin.append("=" * 78)
    fintxt = "\n".join(fin)
    print("\n" + fintxt)
    buf.append("\n\n" + fintxt)
    _write(buf)
    _write_summary(results, winner_name, winner_rec, verdict, vd, ctrl)


def _write(buf):
    path = os.path.join(HERE, "mb_corrector_results.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(buf))
    print(f"\n[written] {path}")


def _write_summary(results, winner_name, winner_rec, verdict, vd, ctrl):
    dd = results[winner_name]["dd"]
    freqs = [dd["labels"][c] for c in winner_rec["chosen"]]
    lines = []
    lines.append("MB CORRECTOR SYNTHESIS — SUMMARY (detail in mb_corrector_results.txt)")
    lines.append("")
    lines.append("Anchor gate: PASS (mb_iterfold gate; raw 1.257 / gauged 1.150 baselines;")
    lines.append("K=12 fold sequence reproduced; tensor engine == direct integral to 1e-9).")
    lines.append("")
    lines.append("Compression curves (spread vs J; baseline 1.257; fold floor 0.441+-0.058,")
    lines.append(f"BREAK < {BREAK_THRESH:.3f}):")
    for name, res in results.items():
        lines.append(f"  {name:>9}: " + " ".join(f"{s:.3f}" for s in res["fit"]["curve"]))
    lines.append("")
    lines.append(f"VERDICT [measured]: {verdict}.")
    lines.append(f"Best admissible corrector: '{winner_name}' J={winner_rec['J']} spread"
                 f" {winner_rec['spread']:.3f}; frequencies {', '.join(freqs)}.")
    if vd["best_any"] >= FOLD_BAND[0] - FOLD_BAND[1]:
        lines.append(f"Best {vd['best_any']:.3f} does not even reach the fold floor"
                     f" {FOLD_BAND[0]}: the shared pure-harmonic class is WEAKER than the")
        lines.append(f"fold's 18 per-cell widths; the plateau survives its adversarial verifier.")
    else:
        lines.append(f"Best {vd['best_any']:.3f} is below the fold floor {FOLD_BAND[0]}.")
    lines.append(f"Controls: scrambled {'does NOT compress comparably (PASS)' if ctrl['scr_ok'] else 'compresses comparably (generic fit — corroborates a null, voids any (a)/(c) claim)'}"
                 f" (ratio real {ctrl['ratio_r']:.2f} vs scr {ctrl['ratio_s']:.2f});"
                 f" transport R={ctrl['R']:.2f} {'PASS' if ctrl['trans_ok'] else 'FAIL'}"
                 f" (train {ctrl['s_tr'][0]:.2f}->{ctrl['s_tr'][1]:.2f},"
                 f" test {ctrl['s_te'][0]:.2f}->{ctrl['s_te'][1]:.2f});"
                 f" admissibility entry {'PASS' if ctrl['adm']['entry_ok'] else 'FAIL'},"
                 f" m in [{ctrl['adm']['m_min']:+.2f},{ctrl['adm']['m_max']:+.2f}];"
                 f" Nyquist {'PASS' if ctrl['conv_ok'] else 'FAIL'}.")
    lines.append("")
    lines.append("Flags: shared single corrector (vs the fold's 18 per-cell widths); greedy+NM")
    lines.append("is heuristic — reported spreads are upper bounds on the class optimum, so a")
    lines.append("no-compression outcome is 'not compressible by this synthesis at this budget';")
    lines.append("gamma = envelope fit over nu<=24; FREE grid resolution 0.05.")
    path = os.path.join(HERE, "mb_corrector_summary.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(lines))
    print(f"[written] {path}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "test"
    if cmd == "test":
        okk = run_tests()
        sys.exit(0 if okk else 1)
    elif cmd == "results":
        run_results()
    else:
        print(f"unknown command {cmd}")
