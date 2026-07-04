#!/usr/bin/env python3
"""
mb_beat.py — THE EMERGENT K: is the quasi-periodic cancellation comb (mb_identify:
376/380 arches at unfolded gap g = 1.0 +- 0.1, switched ON by xi, event sets shared by
both lanes) the TWO-CLOCK BEAT of the modeled F and H terms?  Owner's question made
quantitative: "is there an emergent K from H and F that we aren't modelling?"

MEASURED OBJECT: per cell, the comb fundamental Delta-nu = mean deep-dip spacing of the
total nu-profile (mb_identify's Nyquist-safe census, ppc=8 at nu_max=40; reproduced at
the gate).  Cells with < 4 deep dips are excluded (census reported).

PRE-REGISTERED CLOCK CANDIDATES (all computed from the MODELED lanes, no fitting):
  (i)   F-H DIFFERENCE clock:  Delta-nu_diff = 2pi / |w_F - w_H|,
        w_L = median_nu d(arg V_L)/d nu, phase-differencing the COMPLEX lane transform
        V_L(nu) = sum_y c_L(y) e(-y nu/4lf^2)  (angle of adjacent-point ratio, robust).
  (ii)  F+H SUM clock:         Delta-nu_sum  = 2pi / |w_F + w_H|.
  (iii) CONTENT-BIMODALITY clock (intra-lane): the two dominant peaks of |c_T(y)|,
        separation Dy_bi  ->  Delta-nu_bi = 4 lf^2 / Dy_bi.
  (iv)  CONTENT-ACF clock (model-free emergent-K detector): the dominant off-zero peak
        of |ACF(c_T)|(tau) at lag tau*  ->  Delta-nu_acf = 4 lf^2 / tau*.  A two-
        component beat in nu MUST appear as an ACF lag peak; if (iv) matches the comb
        but (i)/(ii) do not, K is a beat INSIDE the summed content (window/chirp pair),
        not the pairwise F-H beat.
DEGENERACY BREAKER (pre-registered): any candidate proportional to lf^2/X correlates
  with the measured comb through pure kinematics.  All correlations are therefore
  reported BOTH raw (ln-scale Pearson across cells) AND UNFOLDED (spacings multiplied
  by X/(4 lf^2)); a candidate is only MATCHED if raw r > 0.9 AND median ratio
  measured/predicted in [0.7, 1.4]; the unfolded r is reported as the sharpness line.

VERDICTS (coordinator pre-registration): (a) difference clock matched -> K IS the
  pairwise beat, emergent, now modeled; (b) sum clock matched -> same, other clock;
  (c) neither -> K is NOT the pairwise beat; the empirical dispersion law
  ln Delta-nu ~ [1, ln lf^2, ln(X/8), ln(1+xi)] is fitted and reported, and candidates
  (iii)/(iv) are reported as the measured identification of what K is instead.

XI-SWITCH TEST: evaluate the winning/relevant clocks at xi = 0 — the switch-on is
  EXPLAINED if the beat period there exceeds the scan window (no full beat cycle in
  nu in [1,40]) or the content loses its second component (P2/P1 prominence collapse).

CONTROL: scrambled kernel (house recipe, seed 20260703): its comb (if any) must not
  follow the predicted dispersion (r_scr reported).

ANCHORS (gate, FAIL = STOP): scan-mesh census reproduces the recorded mb_identify mean
  gaps (4 spot cells, tol 2e-3); A(8) == J_house on the scan mesh (1e-9); ACF detector
  on a synthetic two-impulse signal recovers the known lag exactly.

TIERS: [anchor]/[measured]/[interpretation].
Run:  python3 mb_beat.py test | results
"""

import sys
import os
import math
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mb_iterfold as IF
import mb_contour as CT
import mb_elastic as EL
import mb_identify as ID

HERE = os.path.dirname(os.path.abspath(__file__))

GRIDC = IF.GRID
NU_GRID = ID.NU_GRID
SEED = 20260703
MIN_DIPS = 4
R_MATCH = 0.9
RATIO_BAND = (0.7, 1.4)
REC_GAPS = {(2, 1, 1, 8.0): 0.528, (6, 1, 1, 16.0): 0.309,
            (6, 2, 1, 8.0): 1.088, (6, 1, 2, 8.0): 2.261}


# ---------------------------------------------------------------------------
# CLOCK EXTRACTORS
# ---------------------------------------------------------------------------

def complex_profile(mesh, cvec, nus=NU_GRID):
    E = np.exp(-2j * math.pi * np.outer(nus, mesh["ys"]) / (4.0 * mesh["lf2"]))
    return E @ cvec


def phase_rate(mesh, cvec):
    """median d(arg V)/d nu over the scan (rad per unit nu); robust to dip jumps."""
    V = complex_profile(mesh, cvec)
    dnu = NU_GRID[1] - NU_GRID[0]
    dphi = np.angle(V[1:] * np.conj(V[:-1]))
    return float(np.median(dphi)) / dnu


def top2_peaks(ys, mag):
    """Two dominant local maxima of |c|(y): (separation, P2/P1)."""
    mi = np.where((mag[1:-1] > mag[:-2]) & (mag[1:-1] >= mag[2:]))[0] + 1
    if len(mi) < 2:
        return float("nan"), 0.0
    order = mi[np.argsort(mag[mi])[::-1]]
    p1, p2 = order[0], order[1]
    return abs(ys[p1] - ys[p2]), float(mag[p2] / mag[p1])


def acf_lag(ys, c):
    """Dominant off-zero |ACF| peak lag of the content (model-free beat detector)."""
    n = len(c)
    cz = c - c.mean()
    ac = np.array([np.abs(np.sum(cz[:n - k] * np.conj(cz[k:]))) for k in range(n)])
    dy = ys[1] - ys[0]
    # first local minimum after 0, then the global max beyond it
    mins = np.where((ac[1:-1] < ac[:-2]) & (ac[1:-1] <= ac[2:]))[0] + 1
    if not len(mins):
        return float("nan"), 0.0
    k0 = mins[0]
    k_star = k0 + int(np.argmax(ac[k0:int(0.9 * n)]))
    return k_star * dy, float(ac[k_star] / ac[0])


# ---------------------------------------------------------------------------
# GATE
# ---------------------------------------------------------------------------

def run_gate(verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    emit("=" * 78)
    emit("STEP 0 — ANCHOR GATE (census reproduction; J-tie; ACF detector)")
    emit("=" * 78)
    t0 = time.time()
    scan_meshes = {}
    for (l, f) in ((1, 1), (2, 1), (1, 2)):
        for X in (8.0, 16.0):
            scan_meshes[(l, f, X)] = EL.build_mesh_ext(l, f, X, ny=ID.scan_ny(l, f, X))
    cores = {k: ID.class_cores(m) for k, m in scan_meshes.items()}
    emit(f"\n[anchor] scan meshes + cores rebuilt ({time.time()-t0:.0f}s;"
         f" Nyquist ppc=8 at nu_max=40, as mb_identify)")

    emit("\n[anchor] (i) census reproduces recorded mb_identify mean gaps (tol 2e-3):")
    rows = ID.collect_laws(scan_meshes, cores, list(REC_GAPS.keys()))
    ok_c = True
    for cell, ref in REC_GAPS.items():
        g = rows[cell]["mean_gap"]
        emit(f"      {str(cell):>18}: mean gap {g:.4f} (recorded {ref})")
        ok_c = ok_c and abs(g - ref) < 2e-3

    emit("\n[anchor] (ii) A(8) == J_house on the scan mesh (1 cell):")
    cell = (2, 1, 1, 8.0)
    key = (1, 1, 8.0)
    cvec = ID.y_content(scan_meshes[key], 2, cores[key]["T"])
    A8 = float(np.abs(complex_profile(scan_meshes[key], cvec, np.array([8.0])))[0])
    Jd = CT.J_direct(scan_meshes[key], EL.weight_of(scan_meshes[key], 2, EL.wfun_bump(1.0)))
    emit(f"      rel dev {abs(A8-Jd)/Jd:.2e}  (tol 1e-9)")
    ok_j = abs(A8 - Jd) / Jd < 1e-9

    emit("\n[anchor] (iii) ACF detector on synthetic two-impulse content:")
    ys = np.linspace(0.0, 10.0, 2000)
    sig = np.exp(-0.5 * ((ys - 2.0) / 0.3) ** 2) + 0.8 * np.exp(-0.5 * ((ys - 7.3) / 0.3) ** 2)
    lag, prom = acf_lag(ys, sig.astype(complex))
    emit(f"      known separation 5.30, ACF lag {lag:.3f} (prom {prom:.2f}; tol 0.05)")
    ok_a = abs(lag - 5.3) < 0.05

    gate = ok_c and ok_j and ok_a
    emit(f"\n[anchor] GATE VERDICT: {'PASS' if gate else 'FAIL'}"
         f"  (census {ok_c}, J {ok_j}, ACF {ok_a})")
    emit("=" * 78)
    return gate, dict(scan_meshes=scan_meshes, cores=cores), "\n".join(out)


# ---------------------------------------------------------------------------
# THE BEAT TEST
# ---------------------------------------------------------------------------

def cell_clock_row(meshes, cores, cell, scr=None):
    key = (cell[1], cell[2], cell[3])
    mesh = meshes[key]
    lf2 = mesh["lf2"]
    scr_y = None if scr is None else scr[cell]
    cT = ID.y_content(mesh, cell[0], cores[key]["T"], scr=scr_y)
    cF = ID.y_content(mesh, cell[0], cores[key]["F"], scr=scr_y)
    cH = ID.y_content(mesh, cell[0], cores[key]["H"], scr=scr_y)
    wF = phase_rate(mesh, cF)
    wH = phase_rate(mesh, cH)
    dnu_diff = 2 * math.pi / abs(wF - wH) if abs(wF - wH) > 1e-12 else float("inf")
    dnu_sum = 2 * math.pi / abs(wF + wH) if abs(wF + wH) > 1e-12 else float("inf")
    dy_bi, prom_bi = top2_peaks(mesh["ys"], np.abs(cT))
    dnu_bi = 4 * lf2 / dy_bi if np.isfinite(dy_bi) and dy_bi > 0 else float("nan")
    lag, prom_ac = acf_lag(mesh["ys"], cT)
    dnu_acf = 4 * lf2 / lag if np.isfinite(lag) and lag > 0 else float("nan")
    return dict(wF=wF, wH=wH, dnu_diff=dnu_diff, dnu_sum=dnu_sum,
                dnu_bi=dnu_bi, prom_bi=prom_bi, dnu_acf=dnu_acf, prom_ac=prom_ac,
                lag=lag, dy_bi=dy_bi)


def corr_ln(a, b):
    m = np.isfinite(a) & np.isfinite(b) & (a > 0) & (b > 0)
    if m.sum() < 4:
        return float("nan"), int(m.sum())
    return float(np.corrcoef(np.log(a[m]), np.log(b[m]))[0, 1]), int(m.sum())


def run_beat(ctx, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    meshes, cores = ctx["scan_meshes"], ctx["cores"]
    emit("=" * 78)
    emit("STEPS 1-4 — MEASURED COMB vs PREDICTED CLOCKS")
    emit("=" * 78)
    rows = ID.collect_laws(meshes, cores, GRIDC)
    cells = [c for c in GRIDC if rows[c]["n_deep"] >= MIN_DIPS]
    emit(f"\n[measured] cells with >= {MIN_DIPS} deep dips: {len(cells)}/18"
         f" (all xi=0 cells have 0 — census as recorded)")

    emit("\n[measured] per-cell table (spacings in nu units):")
    emit(f"    {'cell':>18} {'meas':>7} {'diff':>8} {'sum':>7} {'bimod':>7} {'ACF':>7}"
         f" {'P2/P1':>6} {'ACFpr':>6}")
    meas, pdiff, psum, pbi, pacf = [], [], [], [], []
    clocks = {}
    for cell in cells:
        r = cell_clock_row(meshes, cores, cell)
        clocks[cell] = r
        g = rows[cell]["mean_gap"]
        meas.append(g)
        pdiff.append(r["dnu_diff"])
        psum.append(r["dnu_sum"])
        pbi.append(r["dnu_bi"])
        pacf.append(r["dnu_acf"])
        emit(f"    {str(cell):>18} {g:>7.3f} {r['dnu_diff']:>8.2f} {r['dnu_sum']:>7.3f}"
             f" {r['dnu_bi']:>7.3f} {r['dnu_acf']:>7.3f} {r['prom_bi']:>6.2f}"
             f" {r['prom_ac']:>6.2f}")
    meas = np.array(meas)
    cands = {"(i) F-H difference": np.array(pdiff), "(ii) F+H sum": np.array(psum),
             "(iii) content bimodality": np.array(pbi), "(iv) content ACF": np.array(pacf)}

    emit("\n[measured] candidate scores (raw ln-r; unfolded ln-r; median ratio m/p):")
    lf2X = np.array([c[1] * c[2] ** 2 / c[3] for c in cells]) * 4.0
    scores = {}
    for name, pred in cands.items():
        r_raw, n = corr_ln(meas, pred)
        r_unf, _ = corr_ln(meas / lf2X, pred / lf2X)
        m = np.isfinite(pred) & (pred > 0)
        ratio = float(np.median(meas[m] / pred[m])) if m.sum() >= 4 else float("nan")
        scores[name] = (r_raw, r_unf, ratio, n)
        emit(f"      {name:>26}: r_raw {r_raw:+.3f}  r_unfolded {r_unf:+.3f}"
             f"  ratio {ratio:.3f}  (n={n})")

    def matched(name):
        r, _, ratio, n = scores[name]
        return (np.isfinite(r) and r > R_MATCH and RATIO_BAND[0] <= ratio <= RATIO_BAND[1])

    if matched("(i) F-H difference"):
        verdict = "(a) K IS the pairwise F-H beat (difference clock)"
    elif matched("(ii) F+H sum"):
        verdict = "(b) K is the pairwise beat on the SUM clock"
    else:
        verdict = "(c) K is NOT the pairwise F-H beat"
    emit(f"\n[measured] PAIRWISE-BEAT VERDICT: {verdict}")
    alt = [nm for nm in ("(iv) content ACF", "(iii) content bimodality") if matched(nm)]
    if verdict.startswith("(c)") and alt:
        emit(f"[measured] K IDENTIFIED INSTEAD by: {', '.join(alt)} — the comb is a beat")
        emit(f"    INSIDE the summed content (window/chirp pair), shared by both lanes,")
        emit(f"    not a beat BETWEEN the lanes.")

    # empirical dispersion law (mandatory on (c))
    Xf = np.array([[1.0, math.log(c[1] * c[2] ** 2), math.log(c[3] / 8.0),
                    math.log(1.0 + c[0])] for c in cells])
    beta, *_ = np.linalg.lstsq(Xf, np.log(meas), rcond=None)
    R2 = 1.0 - np.sum((np.log(meas) - Xf @ beta) ** 2) / np.sum(
        (np.log(meas) - np.log(meas).mean()) ** 2)
    emit(f"\n[measured] empirical dispersion law ln(Dnu) ~ [1, ln lf^2, ln(X/8), ln(1+xi)]:")
    emit(f"      Dnu = {math.exp(beta[0]):.3f} (lf^2)^{beta[1]:.2f} (X/8)^{beta[2]:.2f}"
         f" (1+xi)^{beta[3]:.2f}   R^2 = {R2:.3f}")
    emit(f"      [reference: pure window-span clock 4 lf^2 / (0.94 X) ="
         f" {4/(0.94*8):.3f} (lf^2)^1 (X/8)^-1 (1+xi)^0]")

    # xi-switch explanation
    emit("\n[measured] XI-SWITCH TEST at xi = 0 (why no events):")
    for cell in [(0, 1, 1, 8.0), (0, 2, 1, 16.0), (0, 1, 2, 8.0)]:
        r = cell_clock_row(meshes, cores, cell)
        emit(f"      {str(cell):>18}: |w_F-w_H|={abs(r['wF']-r['wH']):.4f}"
             f" -> diff period {r['dnu_diff']:.1f} (scan window 39);"
             f" P2/P1 {r['prom_bi']:.3f}, ACF prom {r['prom_ac']:.3f}")
    r2s = [cell_clock_row(meshes, cores, c) for c in cells if c[0] == 6]
    emit(f"      xi=6 reference: P2/P1 med {np.median([r['prom_bi'] for r in r2s]):.3f},"
         f" ACF prom med {np.median([r['prom_ac'] for r in r2s]):.3f}")
    emit("=" * 78)
    return dict(rows=rows, cells=cells, meas=meas, cands=cands, scores=scores,
                verdict=verdict, alt=alt, beta=beta, R2=R2, clocks=clocks,
                text="\n".join(out))


# ---------------------------------------------------------------------------
# CONTROL
# ---------------------------------------------------------------------------

def run_control(ctx, bt, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    meshes, cores = ctx["scan_meshes"], ctx["cores"]
    emit("=" * 78)
    emit("CONTROL — scrambled kernel comb vs the predicted dispersion")
    emit("=" * 78)
    rng = np.random.default_rng(SEED)
    scr = {}
    for cell in GRIDC:
        ys = meshes[(cell[1], cell[2], cell[3])]["ys"]
        u = (ys - ys[0]) / (ys[-1] - ys[0])
        psi = np.zeros_like(ys)
        for j in range(1, 7):
            aj, bj = rng.normal(0, math.pi / math.sqrt(6.0), 2)
            psi += aj * np.cos(2 * math.pi * j * u) + bj * np.sin(2 * math.pi * j * u)
        scr[cell] = np.exp(1j * psi)
    rows_s = ID.collect_laws(meshes, cores, GRIDC, scr=scr)
    cells_s = [c for c in GRIDC if rows_s[c]["n_deep"] >= MIN_DIPS]
    emit(f"\n[measured] scrambled comb census: {len(cells_s)}/18 cells with >="
         f" {MIN_DIPS} deep dips")
    if len(cells_s) >= 4:
        meas_s = np.array([rows_s[c]["mean_gap"] for c in cells_s])
        best = {}
        for name in bt["cands"]:
            pred_s = []
            for c in cells_s:
                r = cell_clock_row(meshes, cores, c, scr=scr)
                pred_s.append(dict(zip(
                    ("(i) F-H difference", "(ii) F+H sum",
                     "(iii) content bimodality", "(iv) content ACF"),
                    (r["dnu_diff"], r["dnu_sum"], r["dnu_bi"], r["dnu_acf"])))[name])
            r_s, n_s = corr_ln(meas_s, np.array(pred_s))
            best[name] = (r_s, n_s)
            emit(f"      {name:>26}: scrambled r_raw {r_s:+.3f} (n={n_s})"
                 f"   [real {bt['scores'][name][0]:+.3f}]")
        emit("      [interpretation] a clock whose match survives scrambling is")
        emit("      kinematic/content-generic; one that dies with scrambling is tied to")
        emit("      the coherent kernel.")
    else:
        best = {}
        emit("      too few scrambled comb cells for correlation — reported as-is")
    emit("=" * 78)
    return dict(cells_s=cells_s, best=best, text="\n".join(out))


# ---------------------------------------------------------------------------
# drivers
# ---------------------------------------------------------------------------

def run_tests():
    print("mb_beat self-tests = anchor gate")
    ok, _, _ = run_gate()
    print(f"\nBEAT GATE: {'PASS' if ok else 'FAIL'}")
    return ok


def run_results():
    t_start = time.time()
    buf = []
    ok, ctx, txt0 = run_gate()
    buf.append(txt0)
    if not ok:
        buf.append("\n*** GATE FAILED — protocol stopped (pre-registered). ***")
        _write(buf)
        return
    bt = run_beat(ctx)
    buf.append("\n\n" + bt["text"])
    ctrl = run_control(ctx, bt)
    buf.append("\n\n" + ctrl["text"])

    fin = []
    fin.append("=" * 78)
    fin.append("EMERGENT-K VERDICT (pre-registered)")
    fin.append("=" * 78)
    fin.append(f"[measured] {bt['verdict']}")
    for name, (r, ru, ratio, n) in bt["scores"].items():
        fin.append(f"    {name:>26}: r {r:+.3f} / unfolded {ru:+.3f} / ratio {ratio:.3f}")
    if bt["alt"]:
        fin.append(f"[measured] K identified as: {', '.join(bt['alt'])}")
    fin.append(f"[measured] dispersion law: Dnu = {math.exp(bt['beta'][0]):.3f}"
               f" (lf^2)^{bt['beta'][1]:.2f} (X/8)^{bt['beta'][2]:.2f}"
               f" (1+xi)^{bt['beta'][3]:.2f}  R^2 {bt['R2']:.3f}")
    fin.append(f"[budget] total wall time {time.time()-t_start:.0f}s")
    fin.append("=" * 78)
    fintxt = "\n".join(fin)
    print("\n" + fintxt)
    buf.append("\n\n" + fintxt)
    _write(buf)
    _write_summary(bt, ctrl)


def _write(buf):
    path = os.path.join(HERE, "mb_beat_results.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(buf))
    print(f"\n[written] {path}")


def _write_summary(bt, ctrl):
    lines = []
    lines.append("MB BEAT / EMERGENT K — SUMMARY (detail in mb_beat_results.txt)")
    lines.append("")
    lines.append("Gate: PASS — census gaps reproduce mb_identify records (2e-3); A(8) ==")
    lines.append("J_house 1e-9; ACF detector exact on synthetic two-impulse content.")
    lines.append("")
    lines.append(f"VERDICT [measured]: {bt['verdict']}")
    for name, (r, ru, ratio, n) in bt["scores"].items():
        lines.append(f"  {name}: r {r:+.2f}, unfolded {ru:+.2f}, ratio {ratio:.2f}")
    if bt["alt"]:
        lines.append(f"K identified instead as: {', '.join(bt['alt'])} — a beat inside")
        lines.append("the summed content, shared by both lanes, not between them.")
    lines.append(f"Dispersion law: Dnu = {math.exp(bt['beta'][0]):.2f}"
                 f" (lf^2)^{bt['beta'][1]:.2f} (X/8)^{bt['beta'][2]:.2f}"
                 f" (1+xi)^{bt['beta'][3]:.2f}, R^2 {bt['R2']:.2f}.")
    lines.append("Xi-switch and control numbers in the results file.")
    lines.append("")
    lines.append("Flags: 12/18 cells enter (xi=0 has no events, by measurement); unfolded")
    lines.append("correlations guard the lf^2/X kinematic degeneracy; clock extraction is")
    lines.append("median phase rate (robust, but a single number per lane).")
    path = os.path.join(HERE, "mb_beat_summary.txt")
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
