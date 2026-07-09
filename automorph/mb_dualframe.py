#!/usr/bin/env python3
"""
mb_dualframe.py — DUAL-FRAME TOMOGRAPHY / WELD HOLONOMY, full CECH MEASUREMENT.
Measure each lane of the MB pair in BOTH charts (the 2x2 cost matrix), check cocycle
symmetry, compose the round trip, read out in the balanced and energy product charts,
and reconcile — the wall as the cocycle cost of the transition between Mellin-dual charts.

Owner's protocol (amended): "don't measure in the same frame — measure in different frames
simultaneously, project both sides DOWN a dimension, reconcile at the end"; upgraded to the
complete matrix + symmetric readouts before running.

FRAMES ARE THE EXPERIMENT — every gauge stated explicitly (no silent frames):
  LANES (mb_elastic/mb_contour, anchor-gated; straight contour — frame moves are GAUGES):
      g_F(t) = (1/2pi)          kerF(t) A_F(u_F),  kerF = Ftilde(u_F),        u_F = 1.2+it
      g_H(t) = (1/2pi) sqrt(pi) kerH(t) A_H(u_H),  kerH = GR1(u_H) Ftilde(u_H), u_H = 1.0+it
      (GR1 = Gamma((1+u)/2)/Gamma((2-u)/2) — the FE gamma-factor ratio = the transition.)
  CHART j gauge: the unimodular phase e^{-i arg ker_j(t)} (kernel phase = deterministic,
      cell-independent chart data; content phase arg A = the cell's data, never gauged).
  MEASUREMENT of object g in chart j:  M_j(g) = ln [ int |g| dt / | int g e^{-i arg ker_j} dt | ].

THE READOUTS (all per cell, 18-cell grid, nu* = 8, extended mesh (0.05,1.45) ny=112):
  1. 2x2 MATRIX: C_ij = M_j(g_i), i,j in {F,H}.  Pre-registered shape (a): diagonal small
     (each object cheap in its own chart), off-diagonal carries the wall.
  2. COCYCLE SYMMETRY: skew = lnC_FH - lnC_HF per cell + grid stats (elastic-reciprocal
     transport iff skew ~ 0).
  3. ROUND-TRIP HOLONOMY: the two-chart pure-gauge loop is exactly trivial
     (e^{-i arg kerH} e^{-i(arg kerF - arg kerH)} == e^{-i arg kerF}; verified to machine
     precision as a structural anchor).  The measured loop cost of the PAIR over staying
     home — the gauge-pairing-invariant excess — is
         HOL = (lnC_FH + lnC_HF) - (lnC_FF + lnC_HH)
     (composition check: off-diagonal sum vs diagonal sum + holonomy is the identity that
     DEFINES HOL; the content is whether HOL ~ the wall).
  4. PRODUCT CHARTS: (i) BALANCED chart = geometric mean gauge e^{-i(arg kerF+arg kerH)/2};
     costs of both objects there; equipartition index E = |C_F@bal - C_H@bal| /
     (C_F@bal + C_H@bal) (ln-units), conjecture E small (< 0.2 median).  The equipartition
     LOCATION in sigma: the lane-mass balance shift s_bal per cell (engine sigma-scan, as
     in mb_elastic Test B), reported as sigma_H(bal) = 1.0 + s_bal and sigma_F(bal) =
     1.2 + s_bal, compared against sigma* = 0.50-0.54.  HONESTY CAVEAT (pre-registered):
     be_exact_gauge's sigma* is a gamma-SPREAD HEIGHT (dimensionless), not a contour
     coordinate; a numerical match is reported as a [flag]-level coincidence unless a
     mechanism ties the units.  (ii) ENERGY chart ("H^2 F^2") = second-moment readout in
     the balanced gauge: M2(g) = ln [ int |g|^2 dt / | int g^2 e^{-2i arg ker_bal} dt | ];
     quadrature test Q = C2_T^2 / (C2_F^2 + C2_H^2) (linear units), "adds in quadrature"
     iff median Q in [0.8, 1.2].  Exploratory operationalization, stated as such.
  5. DOWN-PROJECTION (pre-registered): the xi = 0 shadow (x-Fourier DC content, xphase=1;
     the house DC-fiber/pole detector); the matrix re-measured on the shadow.
  RECONCILIATION reference (kept from the original protocol): the welded total in one
     chart, lnC_rec^j = ln[(M_F+M_H)/|int (g_F+g_H) e^{-i arg ker_j} dt|], both charts.

PRE-REGISTERED VERDICTS (medians over the grid; wall reference = lnC_T, the ungauged
total = mb_contour reading (ii), anchor-gated):
  (a) HOLONOMY IDENTIFIED (diagonal-light / off-diagonal-heavy):
      med(diag)/med(lnC_T) <= 0.3  AND  med(offdiag)/med(lnC_T) >= 0.7
      AND corr(offdiag mean, lnC_T) >= 0.8.  Then the cohomological summary line is
      emitted with the measured holonomy and equipartition sigma, and the transition-cost
      law lnC_offdiag ~ [1, ln lf^2, ln(X/8), ln(1+xi)] is fitted (GL(3) INPUT;
      [interpretation]-only extrapolation).
  (b) NON-SPLITTABLE: med(diag) >= 0.7 med(lnC_T) -> not frame-separable; dual-chart
      diagnosis needs revision; full prominence.
  (c) PARTIAL: else — measured fractions per matrix entry.

CONTROLS: scrambled kernel (house recipe, seed 20260703) through the IDENTICAL protocol
  (no FE tie in the content -> the matrix shape / holonomy should differ qualitatively;
  probe: diag/offdiag fractions + corr(HOL, lnC_T)); quadrature doubling (t x2, s x2) on
  every readout, tol 0.02; gauge unimodularity + loop-triviality anchors.

ANCHORS: 80x80 lane-sum total == mb_contour recorded baseline; |V_T| == J_house
  (BEG._F_vec path); extended-mesh baseline == mb_elastic gate values (0.679/0.422).

TIERS: [anchor]/[measured]/[interpretation].
Run:  python3 mb_dualframe.py test     # anchors + frame statement
      python3 mb_dualframe.py results  # full tomography -> mb_dualframe_results.txt
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

HERE = os.path.dirname(os.path.abspath(__file__))

GRIDC = IF.GRID
TS = CT.TS
NU_STAR = 8.0
SEED = 20260703
FRAC_DIAG, FRAC_OFF = 0.3, 0.7
CORR_OFF = 0.8
EQUI_TOL = 0.2
QUAD_BAND = (0.8, 1.2)
SIGSTAR_BAND = (0.50, 0.54)
DOUBLING_TOL = 0.02


# ---------------------------------------------------------------------------
# THE CECH EVALUATOR
# ---------------------------------------------------------------------------

def cech_costs(meshes, cells, wfuns, nu=NU_STAR, scr=None, dc_shadow=False,
               ts=None, sg=None):
    """Full matrix + product-chart readouts per cell (straight contour)."""
    ts = TS if ts is None else ts
    uF = CT.SIG_F + 1j * ts
    uH = CT.SIG_H + 1j * ts
    if sg is not None:
        wexp = np.exp(-2.0 * np.cosh(sg))
        KF, KH = CT.K2_vec(uF, sg, wexp), CT.K2_vec(uH, sg, wexp)
    else:
        KF, KH = CT.K2_vec(uF), CT.K2_vec(uH)
    kerF = KF / (uF * CT.K02)
    kerH = CT.GR1_vec(uH) * (KH / (uH * CT.K02))
    aF, aH = np.angle(kerF), np.angle(kerH)
    phF, phH = np.exp(-1j * aF), np.exp(-1j * aH)
    phB = np.exp(-1j * (aF + aH) / 2.0)                     # balanced chart
    # structural anchor: two-chart pure-gauge loop is trivial
    loop_dev = float(np.abs(phH * np.exp(-1j * (aF - aH)) - phF).max())

    by_class = {}
    for i, cell in enumerate(cells):
        by_class.setdefault((cell[1], cell[2], cell[3]), []).append(i)
    nt = len(ts)
    AF = np.zeros((len(cells), nt), complex)
    AH = np.zeros((len(cells), nt), complex)
    for key, idxs in by_class.items():
        mesh = meshes[key]
        WF = []
        for i in idxs:
            xi_eff = 0 if dc_shadow else cells[i][0]
            WF.append(EL.weight_of(mesh, xi_eff, wfuns[cells[i]], nu=nu,
                                   scr=None if scr is None else scr[cells[i]]))
        WF = np.array(WF)
        WH = WF * mesh["a"][None, :]
        LaF, LaH = mesh["La"], mesh["La"] + math.log(math.pi)
        for i0 in range(0, nt, 200):
            sl = slice(i0, i0 + 200)
            AF[idxs, sl] = (np.exp(-np.outer(uF[sl], LaF)) @ WF.T).T
            AH[idxs, sl] = (np.exp(-np.outer(uH[sl], LaH)) @ WH.T).T
    gF = kerF[None, :] * AF / (2 * math.pi)
    gH = (CT.SQRTPI * kerH)[None, :] * AH / (2 * math.pi)
    gT = gF + gH

    def _i(g):
        return np.trapezoid(g, ts, axis=1)

    def M(g, mass, ph):
        return np.log(mass / np.abs(_i(g * ph[None, :])))

    MF, MH = _i(np.abs(gF)), _i(np.abs(gH))
    MT = _i(np.abs(gT))                # TRUE total mass (house reading (ii) definition)
    MW = MF + MH                       # welded lane-mass sum (reconciliation numerator)
    out = dict(M_F=MF, M_H=MH, V_T=_i(gT), loop_dev=loop_dev)
    out["lnC_T"] = np.log(MT / np.abs(_i(gT)))
    # the 2x2 matrix
    out["C_FF"] = M(gF, MF, phF)
    out["C_FH"] = M(gF, MF, phH)
    out["C_HF"] = M(gH, MH, phF)
    out["C_HH"] = M(gH, MH, phH)
    # reconciliation (welding the two frame-local objects: lane-mass sum vs joint readout;
    # lnC_rec - lnC_T@chart == ln[(M_F+M_H)/int|gT|], the mass-interference deficit)
    out["rec_F"] = M(gT, MW, phF)
    out["rec_H"] = M(gT, MW, phH)
    # balanced chart
    out["C_Fbal"] = M(gF, MF, phB)
    out["C_Hbal"] = M(gH, MH, phB)
    out["C_Tbal"] = M(gT, MT, phB)
    # energy (second-moment) readout in the balanced gauge
    for nm, g, in (("F", gF), ("H", gH), ("T", gT)):
        m2 = _i(np.abs(g) ** 2)
        out[f"E_{nm}"] = np.log(m2 / np.abs(_i(g * g * (phB * phB)[None, :])))
    # unimodularity anchor
    out["gauge_mass_dev"] = float(max(
        np.abs(_i(np.abs(gF * phH[None, :])) - MF).max() / MF.max(),
        np.abs(_i(np.abs(gH * phB[None, :])) - MH).max() / MH.max()))
    return out


def derived(fc):
    d = {}
    d["diag"] = 0.5 * (fc["C_FF"] + fc["C_HH"])
    d["offd"] = 0.5 * (fc["C_FH"] + fc["C_HF"])
    d["skew"] = fc["C_FH"] - fc["C_HF"]
    d["HOL"] = fc["C_FH"] + fc["C_HF"] - fc["C_FF"] - fc["C_HH"]
    d["equi"] = np.abs(fc["C_Fbal"] - fc["C_Hbal"]) / np.maximum(
        fc["C_Fbal"] + fc["C_Hbal"], 1e-12)
    CE2 = {k: np.exp(fc[f"E_{k}"]) ** 2 for k in "FHT"}
    d["quad"] = CE2["T"] / (CE2["F"] + CE2["H"])
    return d


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
    emit("STEP 0 — ANCHOR GATE + FRAME STATEMENT (no silent frames)")
    emit("=" * 78)
    emit("\n[frames]")
    emit("    chart F   : gauge e^{-i arg Ftilde(1.2+it)}")
    emit("    chart H   : gauge e^{-i arg[GR1(1+it) Ftilde(1+it)]}  (FE-reflected; GR1 =")
    emit("                the FE gamma-factor ratio = the explicit transition)")
    emit("    balanced  : e^{-i(argF+argH)/2} (geometric-mean chart)")
    emit("    energy    : second-moment readout, squared balanced gauge")
    emit("    down-proj : xi=0 shadow (xphase=1, the DC fiber)")
    emit("    measurement M_j(g) = ln[ int|g| / |int g e^{-i arg ker_j}| ]")

    emit("\n[anchor] (i) 80x80 lane-sum total == mb_contour recorded baseline:")
    meshes80 = {}
    for (l, f) in ((1, 1), (2, 1), (1, 2)):
        for X in (8.0, 16.0):
            meshes80[(l, f, X)] = EL.build_mesh_ext(l, f, X, ny=80, nx=80,
                                                    y_range=(0.25, 1.25))
    wf = {c: EL.wfun_bump(1.0) for c in GRIDC}
    fc80 = cech_costs(meshes80, GRIDC, wf)
    dev = max(abs(fc80["lnC_T"][GRIDC.index(c)] - v) for c, v in EL.REC_LNC.items())
    m_, s_ = fc80["lnC_T"].mean(), fc80["lnC_T"].std()
    emit(f"      spot max dev {dev:.4f} (tol 0.01); mean/std {m_:.3f}/{s_:.3f}"
         f" (recorded {EL.REC_MEAN}/{EL.REC_STD})")
    ok_rec = dev < 0.01 and abs(m_ - EL.REC_MEAN) < 0.01 and abs(s_ - EL.REC_STD) < 0.01

    emit("\n[anchor] (ii) |V_T| == J_house, 3 spot cells:")
    ok_J = True
    for cell in ((0, 1, 1, 8.0), (2, 2, 1, 16.0), (6, 1, 2, 16.0)):
        i = GRIDC.index(cell)
        mesh = meshes80[(cell[1], cell[2], cell[3])]
        Jd = CT.J_direct(mesh, EL.weight_of(mesh, cell[0], EL.wfun_bump(1.0)))
        rd = abs(abs(fc80["V_T"][i]) - Jd) / Jd
        emit(f"      {str(cell):>18}: rel dev {rd:.2e}")
        ok_J = ok_J and rd < 1e-9

    emit(f"\n[anchor] (iii) gauge unimodularity: mass dev {fc80['gauge_mass_dev']:.2e}"
         f" (tol 1e-12); two-chart loop triviality: {fc80['loop_dev']:.2e} (tol 1e-12)")
    ok_u = fc80["gauge_mass_dev"] < 1e-12 and fc80["loop_dev"] < 1e-12

    emit("\n[anchor] (iv) extended analysis mesh (mb_elastic convention):")
    meshes = {}
    for (l, f) in ((1, 1), (2, 1), (1, 2)):
        for X in (8.0, 16.0):
            meshes[(l, f, X)] = EL.build_mesh_ext(l, f, X)
    fc = cech_costs(meshes, GRIDC, wf)
    emit(f"      lnC_T mean {fc['lnC_T'].mean():.3f} std {fc['lnC_T'].std():.3f}"
         f"  (mb_elastic gate: 0.679/0.422)")
    ok_ext = abs(fc["lnC_T"].mean() - 0.679) < 0.01 and abs(fc["lnC_T"].std() - 0.422) < 0.01

    gate = ok_rec and ok_J and ok_u and ok_ext
    emit(f"\n[anchor] GATE VERDICT: {'PASS' if gate else 'FAIL'}"
         f"  (records {ok_rec}, J {ok_J}, gauges {ok_u}, ext {ok_ext})")
    emit("=" * 78)
    return gate, dict(meshes=meshes, fc=fc, wf=wf), "\n".join(out)


# ---------------------------------------------------------------------------
# TOMOGRAPHY
# ---------------------------------------------------------------------------

def mat_table(emit, fc, d):
    emit(f"    {'cell (xi,l,f,X)':>18} {'C_FF':>7} {'C_FH':>7} {'C_HF':>7} {'C_HH':>7}"
         f" {'skew':>7} {'HOL':>7} {'total':>7}")
    for i, cell in enumerate(GRIDC):
        emit(f"    {str(cell):>18} {fc['C_FF'][i]:>7.3f} {fc['C_FH'][i]:>7.3f}"
             f" {fc['C_HF'][i]:>7.3f} {fc['C_HH'][i]:>7.3f} {d['skew'][i]:>7.3f}"
             f" {d['HOL'][i]:>7.3f} {fc['lnC_T'][i]:>7.3f}")
    emit(f"      medians: C_FF={np.median(fc['C_FF']):.3f} C_FH={np.median(fc['C_FH']):.3f}"
         f" C_HF={np.median(fc['C_HF']):.3f} C_HH={np.median(fc['C_HH']):.3f}"
         f" HOL={np.median(d['HOL']):.3f} total={np.median(fc['lnC_T']):.3f}")


def run_tomography(ctx, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    meshes, fc, wf = ctx["meshes"], ctx["fc"], ctx["wf"]
    d = derived(fc)
    emit("=" * 78)
    emit("STEPS 1-4 — THE CECH MEASUREMENT (extended mesh, straight contour, nu*=8)")
    emit("=" * 78)

    emit("\n[measured] 1. THE 2x2 COST MATRIX + holonomy (per cell):")
    mat_table(emit, fc, d)
    medT = float(np.median(fc["lnC_T"]))
    fdiag = float(np.median(d["diag"])) / medT
    foff = float(np.median(d["offd"])) / medT
    corr_off = float(np.corrcoef(d["offd"], fc["lnC_T"])[0, 1])
    emit(f"\n      diagonal fraction of the wall  med(diag)/med(total) = {fdiag:.3f}")
    emit(f"      off-diag fraction              med(offd)/med(total) = {foff:.3f}")
    emit(f"      corr(off-diagonal, total) = {corr_off:+.3f}")

    emit(f"\n[measured] 2. COCYCLE SYMMETRY: skew = C_FH - C_HF:")
    emit(f"      median {np.median(d['skew']):+.3f}, mean {d['skew'].mean():+.3f},"
         f" std {d['skew'].std():.3f}, max|skew| {np.abs(d['skew']).max():.3f}")
    sym = abs(np.median(d["skew"])) < 0.2 * medT
    emit(f"      -> transport {'SYMMETRIC (elastic-reciprocal)' if sym else 'SKEW'}"
         f" at the 0.2*wall criterion")

    emit(f"\n[measured] 3. ROUND-TRIP HOLONOMY (loop vs staying home):")
    emit(f"      pure-gauge loop composition: trivial to {fc['loop_dev']:.1e} (anchor);")
    emit(f"      measured pair holonomy HOL = C_FH + C_HF - C_FF - C_HH:")
    emit(f"      median {np.median(d['HOL']):.3f}, vs wall med(lnC_T) = {medT:.3f}"
         f"  (ratio {np.median(d['HOL'])/medT:.2f}); corr(HOL, total) ="
         f" {float(np.corrcoef(d['HOL'], fc['lnC_T'])[0,1]):+.3f}")
    emit(f"      composition law: offdiag-sum = diag-sum + HOL holds by construction;")
    emit(f"      the content is the ratio and correlation above.")

    emit(f"\n[measured] 4(i). BALANCED CHART (geometric-mean gauge):")
    emit(f"      med C_F@bal {np.median(fc['C_Fbal']):.3f}, C_H@bal"
         f" {np.median(fc['C_Hbal']):.3f}, C_T@bal {np.median(fc['C_Tbal']):.3f}")
    emit(f"      equipartition index E med {np.median(d['equi']):.3f}"
         f" (conjecture: < {EQUI_TOL})"
         f" -> {'EQUIPARTITIONS' if np.median(d['equi']) < EQUI_TOL else 'does NOT equipartition'}")
    # equipartition location in sigma (lane-mass balance; engine sigma-scan as in elastic)
    t0 = time.time()
    for key, mm in meshes.items():
        if "w0" not in mm:
            mm["w0"] = mm["base0"] * EL.wfun_bump(1.0)(mm["ys"] / mm["X"])[:, None]
    eng = CT.ContourEngine(GRIDC, meshes)
    ss = np.linspace(-0.9, 0.9, 37)
    lnR = np.empty((37, len(GRIDC)))
    for k, s in enumerate(ss):
        lanes = EL.engine_lanes(eng, np.full(len(TS), s))
        lnR[k] = np.log(lanes["M_F"] / lanes["M_H"])
    s_bal = np.full(len(GRIDC), np.nan)
    for i in range(len(GRIDC)):
        cross = np.where(np.diff(np.sign(lnR[:, i])) != 0)[0]
        if len(cross):
            k = cross[0]
            f0, f1 = lnR[k, i], lnR[k + 1, i]
            s_bal[i] = ss[k] + (ss[k + 1] - ss[k]) * (-f0) / (f1 - f0)
    okb = np.isfinite(s_bal)
    sH = 1.0 + s_bal[okb]
    sF = 1.2 + s_bal[okb]
    emit(f"      equipartition LOCATION (lane-mass balance, {int(okb.sum())}/18 cells"
         f" cross in range)   [{time.time()-t0:.0f}s]:")
    emit(f"        sigma_H(bal): median {np.median(sH):.3f} (range"
         f" {sH.min():.2f}..{sH.max():.2f});  sigma_F(bal): median {np.median(sF):.3f}")
    in_band = SIGSTAR_BAND[0] <= np.median(sH) <= SIGSTAR_BAND[1]
    emit(f"        vs sigma* band {SIGSTAR_BAND}: sigma_H(bal) median"
         f" {'IN BAND' if in_band else 'not in band'}")
    emit(f"        [flag] sigma* is a gamma-SPREAD HEIGHT (dimensionless), not a contour")
    emit(f"        coordinate; the numerical agreement is reported as a coincidence-level")
    emit(f"        observation unless a mechanism ties the units.")

    emit(f"\n[measured] 4(ii). ENERGY CHART (second-moment readout, balanced gauge):")
    emit(f"      med E_F {np.median(fc['E_F']):.3f}, E_H {np.median(fc['E_H']):.3f},"
         f" E_T {np.median(fc['E_T']):.3f}")
    emit(f"      quadrature index Q = C2_T^2/(C2_F^2+C2_H^2): median"
         f" {np.median(d['quad']):.3f} (band {QUAD_BAND})"
         f" -> {'adds in QUADRATURE' if QUAD_BAND[0] <= np.median(d['quad']) <= QUAD_BAND[1] else 'does NOT add in quadrature'}")

    emit(f"\n[measured] 5. DOWN-PROJECTION (xi=0 shadow) matrix:")
    fc_dc = cech_costs(meshes, GRIDC, wf, dc_shadow=True)
    d_dc = derived(fc_dc)
    emit(f"      medians: C_FF={np.median(fc_dc['C_FF']):.3f}"
         f" C_FH={np.median(fc_dc['C_FH']):.3f} C_HF={np.median(fc_dc['C_HF']):.3f}"
         f" C_HH={np.median(fc_dc['C_HH']):.3f} HOL={np.median(d_dc['HOL']):.3f}"
         f" total={np.median(fc_dc['lnC_T']):.3f}")
    emit(f"      (xi=0 cells: shadow == cell; xi!=0: their DC fiber)")

    emit(f"\n[measured] reconciliation reference: rec(F) med {np.median(fc['rec_F']):.3f},"
         f" rec(H) med {np.median(fc['rec_H']):.3f}  (welded total per chart)")

    if fdiag <= FRAC_DIAG and foff >= FRAC_OFF and corr_off >= CORR_OFF:
        verdict = "(a) HOLONOMY IDENTIFIED — diagonal-light, off-diagonal-heavy"
    elif fdiag >= FRAC_OFF:
        verdict = "(b) NON-SPLITTABLE — diagonal stays at wall scale; dual-chart diagnosis needs revision"
    else:
        verdict = (f"(c) PARTIAL — fractions: diag {fdiag:.2f}, offdiag {foff:.2f},"
                   f" HOL/wall {np.median(d['HOL'])/medT:.2f}")
    emit(f"\n[measured] MATRIX VERDICT: {verdict}")

    Xf = np.array([[1.0, math.log(c[1] * c[2] ** 2), math.log(c[3] / 8.0),
                    math.log(1.0 + c[0])] for c in GRIDC])
    beta, *_ = np.linalg.lstsq(Xf, d["offd"], rcond=None)
    R2 = 1.0 - np.sum((d["offd"] - Xf @ beta) ** 2) / np.sum((d["offd"] - d["offd"].mean()) ** 2)
    emit(f"\n[measured] transition-cost law: offdiag ~ [1, ln lf^2, ln(X/8), ln(1+xi)]:")
    emit(f"      beta = [{beta[0]:+.3f}, {beta[1]:+.3f}, {beta[2]:+.3f}, {beta[3]:+.3f}],"
         f" R^2 = {R2:.3f}")
    if verdict.startswith("(a)"):
        emit(f"\n[interpretation] COHOMOLOGICAL SUMMARY (shape (a) confirmed): diagonal ~")
        emit(f"    {np.median(d['diag']):.2f} + no frame zeros the total (fold/corrector/")
        emit(f"    contour campaign) + off-diagonal ~ wall ({foff:.2f} of it) => the wall")
        emit(f"    is a measured non-coboundary 1-cocycle between the Mellin-dual charts;")
        emit(f"    holonomy median {np.median(d['HOL']):.3f}; equipartition point sigma_H")
        emit(f"    = {np.median(sH):.3f}.  GL(3) use requires GL(3) gamma factors"
             f" [interpretation].")
    emit("=" * 78)
    return dict(fc=fc, d=d, fc_dc=fc_dc, verdict=verdict, fdiag=fdiag, foff=foff,
                corr_off=corr_off, beta=beta, R2=R2, s_bal=s_bal,
                sH_med=float(np.median(sH)) if okb.any() else float("nan"),
                in_band=in_band, sym=sym, text="\n".join(out))


# ---------------------------------------------------------------------------
# CONTROLS
# ---------------------------------------------------------------------------

def run_controls(ctx, tomo, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    meshes, wf, fc = ctx["meshes"], ctx["wf"], ctx["fc"]
    emit("=" * 78)
    emit("STEP 5 — CONTROLS")
    emit("=" * 78)

    emit(f"\n[measured] (i) SCRAMBLED kernel (house recipe, seed {SEED}), same protocol:")
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
    fcs = cech_costs(meshes, GRIDC, wf, scr=scr)
    ds = derived(fcs)
    medTs = float(np.median(fcs["lnC_T"]))
    fdiag_s = float(np.median(ds["diag"])) / medTs
    foff_s = float(np.median(ds["offd"])) / medTs
    corr_s = float(np.corrcoef(ds["HOL"], fcs["lnC_T"])[0, 1])
    corr_r = float(np.corrcoef(tomo["d"]["HOL"], fc["lnC_T"])[0, 1])
    emit(f"      scrambled: diag/wall {fdiag_s:.2f}, offdiag/wall {foff_s:.2f},"
         f" corr(HOL,total) {corr_s:+.2f}, med total {medTs:.3f}")
    emit(f"      real     : diag/wall {tomo['fdiag']:.2f}, offdiag/wall {tomo['foff']:.2f},"
         f" corr(HOL,total) {corr_r:+.2f}, med total {float(np.median(fc['lnC_T'])):.3f}")
    qual_diff = (abs(fdiag_s - tomo["fdiag"]) > 0.2 or abs(foff_s - tomo["foff"]) > 0.2
                 or abs(corr_s - corr_r) > 0.15)
    emit(f"      -> matrix structure {'DIFFERS (PASS: shape is a property of the coherent kernel)' if qual_diff else 'SIMILAR (FAIL margin: shape is generic to any content — full prominence)'}")

    emit("\n[measured] (ii) quadrature doubling (t x2, Bessel s x2), all readouts:")
    ts2 = np.linspace(-CT.T_C, CT.T_C, 2 * len(TS))
    sg2 = np.linspace(0.0, 6.0, 5000)
    fc2 = cech_costs(meshes, GRIDC, wf, ts=ts2, sg=sg2)
    keys = ["C_FF", "C_FH", "C_HF", "C_HH", "C_Fbal", "C_Hbal", "E_T", "lnC_T"]
    dmax = max(np.abs(fc2[k] - fc[k]).max() for k in keys)
    emit(f"      max |Delta| over readouts/cells = {dmax:.4f}  (tol {DOUBLING_TOL})")
    conv_ok = dmax < DOUBLING_TOL
    emit(f"      -> {'PASS' if conv_ok else 'FAIL (numbers flagged)'}")
    emit("=" * 78)
    return dict(scr_diff=qual_diff, corr_s=corr_s, fdiag_s=fdiag_s, foff_s=foff_s,
                conv_ok=conv_ok, text="\n".join(out))


# ---------------------------------------------------------------------------
# drivers
# ---------------------------------------------------------------------------

def run_tests():
    print("mb_dualframe self-tests = anchor gate + frame statement")
    ok, _, _ = run_gate()
    print(f"\nDUAL-FRAME GATE: {'PASS' if ok else 'FAIL'}")
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
    tomo = run_tomography(ctx)
    buf.append("\n\n" + tomo["text"])
    ctrl = run_controls(ctx, tomo)
    buf.append("\n\n" + ctrl["text"])

    fc, d = tomo["fc"], tomo["d"]
    fin = []
    fin.append("=" * 78)
    fin.append("WELD-HOLONOMY / CECH VERDICT (pre-registered)")
    fin.append("=" * 78)
    fin.append(f"[measured] {tomo['verdict']}")
    fin.append(f"    matrix medians: FF {np.median(fc['C_FF']):.3f}, FH"
               f" {np.median(fc['C_FH']):.3f}, HF {np.median(fc['C_HF']):.3f},"
               f" HH {np.median(fc['C_HH']):.3f}; wall {np.median(fc['lnC_T']):.3f}")
    fin.append(f"    skew median {np.median(d['skew']):+.3f}"
               f" ({'symmetric' if tomo['sym'] else 'skew'});"
               f" holonomy median {np.median(d['HOL']):.3f}")
    fin.append(f"    balanced chart: equipartition E med {np.median(d['equi']):.3f};"
               f" location sigma_H(bal) med {tomo['sH_med']:.3f}"
               f" ({'IN' if tomo['in_band'] else 'not in'} sigma* band {SIGSTAR_BAND},"
               f" units caveat applies)")
    fin.append(f"    energy chart: quadrature index med {np.median(d['quad']):.3f}")
    fin.append(f"    transition-cost law R^2 = {tomo['R2']:.3f}")
    fin.append(f"[controls] scrambled matrix {'DIFFERS' if ctrl['scr_diff'] else 'SIMILAR (flag)'};"
               f" doubling {'PASS' if ctrl['conv_ok'] else 'FAIL'}")
    fin.append(f"[budget] total wall time {time.time()-t_start:.0f}s")
    fin.append("=" * 78)
    fintxt = "\n".join(fin)
    print("\n" + fintxt)
    buf.append("\n\n" + fintxt)
    _write(buf)
    _write_summary(tomo, ctrl)


def _write(buf):
    path = os.path.join(HERE, "mb_dualframe_results.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(buf))
    print(f"\n[written] {path}")


def _write_summary(tomo, ctrl):
    fc, d = tomo["fc"], tomo["d"]
    lines = []
    lines.append("MB DUAL-FRAME / CECH WELD-HOLONOMY — SUMMARY")
    lines.append("(detail in mb_dualframe_results.txt)")
    lines.append("")
    lines.append("Gate: PASS — lane-sum == mb_contour records; |V_T|==J_house 1e-9; gauges")
    lines.append("unimodular + two-chart loop trivial to machine; ext mesh == mb_elastic.")
    lines.append("Frames explicit: chart F/H = kernel-phase gauges (H carries the FE gamma-")
    lines.append("ratio GR1 = the transition); balanced = geometric-mean gauge; energy =")
    lines.append("second-moment readout; down-projection = xi=0 DC shadow.")
    lines.append("")
    lines.append(f"VERDICT [measured]: {tomo['verdict']}")
    lines.append(f"Matrix medians: C_FF {np.median(fc['C_FF']):.3f} / C_FH"
                 f" {np.median(fc['C_FH']):.3f} / C_HF {np.median(fc['C_HF']):.3f} /"
                 f" C_HH {np.median(fc['C_HH']):.3f}; wall lnC_T"
                 f" {np.median(fc['lnC_T']):.3f}.")
    lines.append(f"Skew {np.median(d['skew']):+.3f}"
                 f" ({'symmetric' if tomo['sym'] else 'SKEW'});"
                 f" round-trip holonomy {np.median(d['HOL']):.3f}"
                 f" (loop-gauge triviality anchored).")
    lines.append(f"Balanced chart: equipartition index {np.median(d['equi']):.3f}"
                 f" (<{EQUI_TOL} = equipartitions); location sigma_H(bal) median"
                 f" {tomo['sH_med']:.3f} — {'IN' if tomo['in_band'] else 'NOT in'} the"
                 f" sigma* band {SIGSTAR_BAND}; [flag] sigma* is a spread HEIGHT, not a")
    lines.append("sigma-coordinate: agreement reported, not identified.")
    lines.append(f"Energy chart: quadrature index {np.median(d['quad']):.3f}"
                 f" (band {QUAD_BAND}).")
    lines.append(f"Transition-cost law: R^2 = {tomo['R2']:.2f},"
                 f" beta = {np.round(tomo['beta'],3).tolist()} (GL(3): needs GL(3) gamma")
    lines.append("factors — [interpretation] only).")
    lines.append(f"Controls: scrambled matrix {'DIFFERS (PASS)' if ctrl['scr_diff'] else 'SIMILAR (flagged)'};"
                 f" doubling {'PASS' if ctrl['conv_ok'] else 'FAIL'}.")
    lines.append("")
    lines.append("Flags: kernel-phase gauges only (content never gauged); nu*=8 extended")
    lines.append("mesh; energy readout is an exploratory operationalization of 'H^2F^2'.")
    path = os.path.join(HERE, "mb_dualframe_summary.txt")
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
