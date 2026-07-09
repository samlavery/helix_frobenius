#!/usr/bin/env python3
"""
mb_elastic.py — THE ELASTIC-PAIR TEST: is the thrice-certified invariant (fold 0.441 band,
corrector-immune, contour-exact) actually TWO things living in alternate charts — the F-term
and H-term of the MB integrand (the Mellin/functional-equation pair) — connected by an
elastic (sigma / the contour), anchored by the poles?  Owner's structural diagnosis, now
pre-registered and tested.  Mostly RE-ANALYSIS of what the three campaign instruments
already compute.

THE LANES (eq.(32) integrand = F + H; house factorization, reused from mb_contour):
    g_F(t) = (1/2pi)          Ftilde(u_F) A_F(u_F)          u_F = 1.2 + w(t) + it
    g_H(t) = (1/2pi) sqrt(pi) GR1(u_H) Ftilde(u_H) A_H(u_H)  u_H = 1.0 + w(t) + it
    lane cost  ln C_L = ln [ integral |g_L| |phi| dt / |integral g_L phi dt| ]   (phi = 1-iw')
    total cost on g_F + g_H  == mb_contour reading (ii)  (anchor-gated below).

MESH (pre-registered): the fold's recorded widths reach 1.35 (support [0.075,1.425]), which
would CLIP on the published y/X range [0.25,1.25] — never-clip law.  So the elastic analysis
runs on the EXTENDED range (0.05,1.45) (mb_iterfold's YRANGE_EXT), ny=112 nx=80, nu*=8.
The 80x80 published-mesh baseline is still reproduced against mb_contour's recorded values
as the anchor; the extended-mesh straight baseline is the reference for all deltas
(within-mesh differences; mb_contour flagged the mesh-dependence of C at ~0.1).

PRE-REGISTERED MOVES for TEST A (one lever per campaign, the levers the instruments used):
  FOLD family     : (f1) the recorded K=12 fold endpoint per-cell widths
                    (f2) the geometric midpoint widths sqrt(w_i)  ("2-3 fold iterations")
                    (f3) global width 0.8
  CORRECTOR       : (c1) the recorded winning modulation  m(t) = 1 + 0.110cos+0.203sin @1.5
                    + 0.074cos-0.827sin @1.0  (window -> G_altug * m)
  CONTOUR         : (w1-w3) the three seeded admissible random waves (seed 20260703)
                    (w4) the shared wavy winner refit at J=2 (same greedy protocol)

TEST A — ELASTIC CONSERVATION.  Per (move, cell): d_F = Delta ln C_F, d_H = Delta ln C_H,
  d_T = Delta ln C_total.  Trade correlation rho = corr(d_F, -d_H) pooled (and per family);
  pinning index P = median|d_T| / median(|d_F| + |d_H|).
  Verdict (a) TRADE (elastic law confirmed): rho >= 0.6 AND P <= 0.3.
  Verdict (b) diagnosis WRONG (full prominence):  rho < 0.3 OR P > 0.7.
  Else PARTIAL/AMBIGUOUS.
TEST B — BALANCE LOCUS.  Per cell: (sigma) constant-shift scan s in [-0.9,0.9]: floor
  s* = argmin ln C_T(s); balance s_bal = zero of ln(M_F/M_H)(s) (lane-mass crossing).
  (nu) scan nu in {2,4,8,16,24}: floor nu* = argmin ln C_T(nu); balance nu_bal = crossing
  of M_F/M_H = 1 in ln nu (censored cells reported).  Correlations (Pearson; nu Spearman).
TEST C — UNCERTAINTY SCALING.  Std across the 18 cells of: ln C_F, ln C_H, ln(C_F C_H),
  (C_F + C_H) [linear], and the true total ln C_T.  Joint verdict if
  std(ln C_T) < 0.5 * min(std ln C_F, std ln C_H).
BONUS — ELASTIC CONSTANT.  OLS of the baseline ln C_T on [1, ln lf^2, ln(X/8), ln(1+xi)];
  if R^2 >= 0.8 the law is stated [measured]; the GL(3) extrapolation requires the GL(3)
  gamma factors and is flagged [interpretation]-only.

CONTROLS: (i) quadrature doubling (t-grid x2, Bessel s-grid x2) on the lane splits
  (baseline + one wave): max |Delta ln C_lane| < 0.02; (ii) scrambled-kernel lane check
  (house recipe, seed 20260703): rho_scrambled on the SAME move subset (w1-w3, f3) vs
  rho_real on that subset — the coordinator's pre-registration expects the trade to vanish
  (FE tie broken); if it does NOT vanish the trade is kernel-structural rather than
  coherence-borne — either outcome reported at full prominence.

TIERS: [anchor]/[measured]/[interpretation].  Register: gate fail -> STOP; doubling drift
  > 0.02 -> lane numbers flagged; Test A verdict follows the thresholds, not the narrative.

Run:  python3 mb_elastic.py test     # lane-split anchor vs mb_contour recorded totals
      python3 mb_elastic.py results  # full protocol -> mb_elastic_results.txt + summary
"""

import sys
import os
import math
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mb_uniform as MB
import mb_iterfold as IF
import mb_contour as CT
import mb_corrector as MC          # noqa: F401 (house chain; split/coef provenance)

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------------------
# PRE-REGISTERED CONSTANTS + RECORDED CAMPAIGN DATA
# ---------------------------------------------------------------------------
GRIDC = IF.GRID
TS = CT.TS
NU_STAR = 8.0
NUS_SCAN = (2.0, 4.0, 8.0, 16.0, 24.0)
YEXT = (0.05, 1.45)
NY_EXT, NX_EXT = 112, 80
SEED = 20260703

# [anchor] mb_contour recorded straight baseline (80x80 published mesh, nu*=8)
REC_LNC = {(0, 1, 1, 8.0): 1.309, (0, 1, 1, 16.0): 1.784, (2, 1, 1, 8.0): 0.639,
           (2, 2, 1, 16.0): 1.197, (6, 1, 1, 8.0): 0.752, (6, 1, 2, 16.0): 0.714}
REC_MEAN, REC_STD = 0.680, 0.424

# [anchor] mb_iterfold K=12 fold endpoint widths (recorded, GRID order)
FOLD_WIDTHS = [0.54, 0.45, 1.35, 0.91, 1.35, 1.35, 0.34, 0.28, 1.35,
               0.57, 1.35, 1.15, 0.23, 0.20, 1.14, 0.40, 1.35, 0.80]

# [anchor] mb_corrector winning modulation (winharm, recorded coefficients)
CORR_TONES = [(1.5, 0.110, 0.203), (1.0, 0.074, -0.827)]     # (omega, a_cos, b_sin)

RHO_TRADE, PIN_TRADE = 0.6, 0.3           # verdict (a)
RHO_WRONG, PIN_WRONG = 0.3, 0.7           # verdict (b)
JOINT_RATIO = 0.5                         # Test C
DOUBLING_TOL = 0.02


def wfun_bump(width, center=0.75):
    return lambda t: IF.bump_vec(np.atleast_1d(np.asarray(t, float)), center, width)


def wfun_corrector(t):
    t = np.atleast_1d(np.asarray(t, float))
    m = np.ones_like(t)
    for om, a, b in CORR_TONES:
        m += a * np.cos(2 * math.pi * om * t) + b * np.sin(2 * math.pi * om * t)
    return IF.bump_vec(t, 0.75, 1.0) * m


# ---------------------------------------------------------------------------
# EXTENDED MESH + WEIGHTS (window factored OUT of the mesh, per-cell windows legal)
# ---------------------------------------------------------------------------

def build_mesh_ext(l, f, X, ny=NY_EXT, nx=NX_EXT, y_range=YEXT):
    lf2 = l * f * f
    ys = np.linspace(y_range[0] * X, y_range[1] * X, ny)
    xs = np.linspace(-0.999, 0.999, nx)
    dy, dx = ys[1] - ys[0], xs[1] - xs[0]
    Xg, Yg = np.meshgrid(xs, ys)
    edge = np.maximum(np.abs(1.0 - Xg * Xg), 1e-12)
    a = lf2 / (np.sqrt(4.0 * Yg) * np.sqrt(edge))
    th = np.array([MB.theta_inf_profile(x, -1) for x in xs])[None, :]
    base0 = Yg * th * dx * dy                       # window NOT included
    return dict(l=l, f=f, X=X, lf2=lf2, ys=ys, xs=xs, Xg=Xg, Yg=Yg,
                a=a.ravel(), La=np.log(a.ravel()), base0=base0, ny=ny, nx=nx)


def weight_of(mesh, xi, wfun, nu=NU_STAR, scr=None):
    lf2 = mesh["lf2"]
    gw = wfun(mesh["ys"] / mesh["X"])[:, None]
    xph = np.exp(-2j * math.pi * (mesh["Xg"] * xi * np.sqrt(4.0 * mesh["Yg"])) / (4.0 * lf2))
    yph = np.exp(-2j * math.pi * (mesh["Yg"] * nu) / (4.0 * lf2))
    w = mesh["base0"] * gw * xph * yph
    if scr is not None:
        w = w * scr[:, None]
    return w.ravel()


# ---------------------------------------------------------------------------
# DIRECT LANE EVALUATOR (straight or wavy; arbitrary grids for doubling)
# ---------------------------------------------------------------------------

def lane_eval(meshes, cells, wfuns, nu=NU_STAR, wave_params=None, scr=None,
              ts=None, sg=None):
    """wfuns: dict cell -> window fn.  Returns dict of per-cell lane arrays."""
    ts = TS if ts is None else ts
    if wave_params is not None and len(wave_params):
        wsh, wp = CT.wave(wave_params, ts)
    else:
        wsh = np.zeros_like(ts)
        wp = np.zeros_like(ts)
    uF = CT.SIG_F + wsh + 1j * ts
    uH = CT.SIG_H + wsh + 1j * ts
    if sg is not None:
        wexp = np.exp(-2.0 * np.cosh(sg))
        KF, KH = CT.K2_vec(uF, sg, wexp), CT.K2_vec(uH, sg, wexp)
    else:
        KF, KH = CT.K2_vec(uF), CT.K2_vec(uH)
    FtF = KF / (uF * CT.K02)
    FtH = KH / (uH * CT.K02)
    gr1 = CT.GR1_vec(uH)
    phi = 1.0 - 1j * wp
    by_class = {}
    for i, cell in enumerate(cells):
        by_class.setdefault((cell[1], cell[2], cell[3]), []).append(i)
    nt = len(ts)
    AF = np.zeros((len(cells), nt), complex)
    AH = np.zeros((len(cells), nt), complex)
    for key, idxs in by_class.items():
        mesh = meshes[key]
        WF = np.array([weight_of(mesh, cells[i][0], wfuns[cells[i]], nu=nu,
                                 scr=None if scr is None else scr[cells[i]])
                       for i in idxs])                       # (nc, M)
        WH = WF * mesh["a"][None, :]
        LaF, LaH = mesh["La"], mesh["La"] + math.log(math.pi)
        for i0 in range(0, nt, 200):
            sl = slice(i0, i0 + 200)
            EF = np.exp(-np.outer(uF[sl], LaF))
            EH = np.exp(-np.outer(uH[sl], LaH))
            AF[idxs, sl] = (EF @ WF.T).T
            AH[idxs, sl] = (EH @ WH.T).T
    gF = FtF[None, :] * AF / (2 * math.pi)
    gH = (CT.SQRTPI * gr1 * FtH)[None, :] * AH / (2 * math.pi)
    return _lanes_from_g(gF, gH, phi, ts)


def _lanes_from_g(gF, gH, phi, ts):
    out = {}
    for name, g in (("F", gF), ("H", gH), ("T", gF + gH)):
        V = np.trapezoid(g * phi[None, :], ts, axis=1)
        N = np.trapezoid(np.abs(g) * np.abs(phi)[None, :], ts, axis=1)
        out[f"lnC_{name}"] = np.log(N / np.maximum(np.abs(V), 1e-300))
        out[f"V_{name}"] = V
        out[f"M_{name}"] = N
    return out


def engine_lanes(eng, shift, wp=None):
    """Lane split straight from a CT.ContourEngine's tables (sigma-scans, waves)."""
    r, den = eng._bary(shift)
    uF = CT.SIG_F + shift + 1j * eng.ts
    uH = CT.SIG_H + shift + 1j * eng.ts
    FtF = (np.einsum("kt,kt->t", r, eng.T_KF) / den) / (uF * CT.K02)
    FtH = (np.einsum("kt,kt->t", r, eng.T_KH) / den) / (uH * CT.K02)
    gr1 = CT.GR1_vec(uH)
    AFc = np.einsum("kt,ckt->ct", r, eng.AF) / den[None, :]
    AHc = np.einsum("kt,ckt->ct", r, eng.AH) / den[None, :]
    gF = FtF[None, :] * AFc / (2 * math.pi)
    gH = CT.SQRTPI * (gr1 * FtH)[None, :] * AHc / (2 * math.pi)
    phi = 1.0 - 1j * (wp if wp is not None else np.zeros_like(eng.ts))
    return _lanes_from_g(gF, gH, phi, eng.ts)


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
    emit("STEP 0 — LANE-SPLIT ANCHOR GATE (lane-sum must equal the recorded mb_contour")
    emit("         totals; house-path J anchor; extended-mesh engine identity)")
    emit("=" * 78)

    # (i) reproduce mb_contour's 80x80 baseline via the lane evaluator
    emit("\n[anchor] (i) lane-sum total == mb_contour recorded baseline (80x80 mesh):")
    meshes80 = {}
    for (l, f) in ((1, 1), (2, 1), (1, 2)):
        for X in (8.0, 16.0):
            m = build_mesh_ext(l, f, X, ny=80, nx=80, y_range=(0.25, 1.25))
            meshes80[(l, f, X)] = m
    wf_alt = {c: wfun_bump(1.0) for c in GRIDC}
    lanes80 = lane_eval(meshes80, GRIDC, wf_alt)
    dev = max(abs(lanes80["lnC_T"][GRIDC.index(c)] - v) for c, v in REC_LNC.items())
    emit(f"      spot cells max |lnC_T - recorded| = {dev:.4f}  (tol 0.01, 3-dec records)")
    m_, s_ = lanes80["lnC_T"].mean(), lanes80["lnC_T"].std()
    emit(f"      surface mean {m_:.3f} std {s_:.3f}  (recorded {REC_MEAN}/{REC_STD})")
    ok_rec = dev < 0.01 and abs(m_ - REC_MEAN) < 0.01 and abs(s_ - REC_STD) < 0.01

    # (ii) house-path J anchor + lane linearity
    emit("\n[anchor] (ii) |V_F + V_H| == J_house (BEG._F_vec path), 3 spot cells:")
    ok_J = True
    for cell in ((0, 1, 1, 8.0), (2, 2, 1, 16.0), (6, 1, 2, 16.0)):
        i = GRIDC.index(cell)
        mesh = meshes80[(cell[1], cell[2], cell[3])]
        Jd = CT.J_direct(mesh, weight_of(mesh, cell[0], wfun_bump(1.0)))
        Vt = abs(lanes80["V_F"][i] + lanes80["V_H"][i])
        rd = abs(Vt - Jd) / Jd
        rl = abs(Vt - abs(lanes80["V_T"][i])) / Jd
        emit(f"      {str(cell):>18}: rel dev vs J_house {rd:.2e}; lane-linearity {rl:.2e}")
        ok_J = ok_J and rd < 1e-9 and rl < 1e-12

    # (iii) extended mesh: engine tables == direct lane evaluator
    emit("\n[anchor] (iii) extended mesh (0.05,1.45), ny=112: engine == direct evaluator:")
    t0 = time.time()
    meshes = {}
    for (l, f) in ((1, 1), (2, 1), (1, 2)):
        for X in (8.0, 16.0):
            mm = build_mesh_ext(l, f, X)
            mm["w0"] = mm["base0"] * wfun_bump(1.0)(mm["ys"] / X)[:, None]  # for CT engine
            meshes[(l, f, X)] = mm
    eng = CT.ContourEngine(GRIDC, meshes)
    lanes_e = engine_lanes(eng, np.zeros(len(TS)))
    lanes_d = lane_eval(meshes, GRIDC, wf_alt)
    dd = max(np.abs(lanes_e[f"lnC_{k}"] - lanes_d[f"lnC_{k}"]).max() for k in "FHT")
    emit(f"      max |Delta lnC| over lanes/cells = {dd:.2e}  (tol 1e-7)   "
         f"[build {time.time()-t0:.0f}s]")
    ok_eng = dd < 1e-7
    emit(f"\n[measured] extended-mesh straight baseline (the delta reference):")
    emit(f"      lnC_T mean {lanes_d['lnC_T'].mean():.3f} std {lanes_d['lnC_T'].std():.3f}"
         f"  (80x80 was {m_:.3f}/{s_:.3f} — mesh dependence, flagged in mb_contour)")
    gate = ok_rec and ok_J and ok_eng
    emit(f"\n[anchor] GATE VERDICT: {'PASS' if gate else 'FAIL'}"
         f"  (recorded {ok_rec}, J-anchor {ok_J}, engine {ok_eng})")
    emit("=" * 78)
    return gate, dict(meshes=meshes, eng=eng, base=lanes_d, wf_alt=wf_alt,
                      meshes80=meshes80), "\n".join(out)


# ---------------------------------------------------------------------------
# STEP 1 — LANE DECOMPOSITION (baseline)
# ---------------------------------------------------------------------------

def run_lanes(ctx, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    base = ctx["base"]
    emit("=" * 78)
    emit("STEP 1 — LANE DECOMPOSITION (extended mesh, straight contour, nu*=8)")
    emit("=" * 78)
    emit("    cell (xi,l,f,X):   lnC_F   lnC_H   lnC_T    M_F/M_H   |V_F|/|V_H|")
    for i, cell in enumerate(GRIDC):
        emit(f"      {str(cell):>18}: {base['lnC_F'][i]:7.3f} {base['lnC_H'][i]:7.3f}"
             f" {base['lnC_T'][i]:7.3f} {base['M_F'][i]/base['M_H'][i]:9.3f}"
             f" {abs(base['V_F'][i])/abs(base['V_H'][i]):11.3f}")
    emit(f"\n[measured] lane means: lnC_F {base['lnC_F'].mean():.3f},"
         f" lnC_H {base['lnC_H'].mean():.3f}, lnC_T {base['lnC_T'].mean():.3f};"
         f" median mass ratio M_F/M_H = {np.median(base['M_F']/base['M_H']):.3f}")
    emit("=" * 78)
    return "\n".join(out)


# ---------------------------------------------------------------------------
# STEP 2 — TEST A (elastic conservation)
# ---------------------------------------------------------------------------

def refit_wavy_winner(eng):
    def obj(p):
        lnC, _ = eng.costs(p)
        return float(np.std(lnC)) + CT.wave_penalty(p)
    p, curve, _ = CT.greedy_wave_fit(obj, 2)
    return p, curve


def run_testA(ctx, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    meshes, eng, base = ctx["meshes"], ctx["eng"], ctx["base"]
    emit("=" * 78)
    emit("STEP 2 — TEST A: ELASTIC CONSERVATION (d cost_F vs d cost_H under the")
    emit("recorded campaign moves; trade rho = corr(d_F, -d_H); pinning P)")
    emit("=" * 78)

    moves = {}
    # fold family
    wf1 = {c: wfun_bump(FOLD_WIDTHS[i]) for i, c in enumerate(GRIDC)}
    wf2 = {c: wfun_bump(math.sqrt(FOLD_WIDTHS[i])) for i, c in enumerate(GRIDC)}
    wf3 = {c: wfun_bump(0.8) for c in GRIDC}
    moves["f1 fold-endpoint"] = ("window", wf1, None)
    moves["f2 fold-midpoint"] = ("window", wf2, None)
    moves["f3 width-0.8"] = ("window", wf3, None)
    moves["c1 corrector-winner"] = ("window", {c: wfun_corrector for c in GRIDC}, None)
    for k, wv in enumerate(CT.random_waves(3)):
        moves[f"w{k+1} random-wave"] = ("wave", None, wv)
    t0 = time.time()
    p_win, curve_win = refit_wavy_winner(eng)
    emit(f"\n[measured] wavy shared winner refit (J=2): spread"
         f" {curve_win[0]:.3f} -> {curve_win[-1]:.3f}   [{time.time()-t0:.0f}s]")
    moves["w4 wavy-winner"] = ("wave", None, p_win)

    dF, dH, dT, fam = [], [], [], []
    emit("\n[measured] per-move lane deltas (means over 18 cells):")
    emit(f"    {'move':>20} {'<d_F>':>8} {'<d_H>':>8} {'<d_T>':>8} {'corr(dF,-dH)':>13}")
    per_move = {}
    for name, (kind, wfuns, wv) in moves.items():
        if kind == "window":
            lanes = lane_eval(meshes, GRIDC, wfuns)
        else:
            wsh, wp = CT.wave(wv, TS)
            lanes = engine_lanes(eng, wsh, wp)
        a = lanes["lnC_F"] - base["lnC_F"]
        b = lanes["lnC_H"] - base["lnC_H"]
        c = lanes["lnC_T"] - base["lnC_T"]
        rho_m = float(np.corrcoef(a, -b)[0, 1])
        per_move[name] = (a, b, c, rho_m)
        dF += list(a); dH += list(b); dT += list(c)
        fam += [name.split()[0][0]] * len(a)
        emit(f"    {name:>20} {a.mean():>8.3f} {b.mean():>8.3f} {c.mean():>8.3f}"
             f" {rho_m:>13.3f}")
    dF, dH, dT = np.array(dF), np.array(dH), np.array(dT)
    fam = np.array(fam)
    rho = float(np.corrcoef(dF, -dH)[0, 1])
    P = float(np.median(np.abs(dT)) / np.median(np.abs(dF) + np.abs(dH)))
    emit(f"\n[measured] POOLED (8 moves x 18 cells = {len(dF)} pairs):")
    emit(f"      trade correlation rho = corr(d_F, -d_H) = {rho:+.3f}")
    emit(f"      pinning index P = med|d_T| / med(|d_F|+|d_H|) = {P:.3f}")
    for f, lab in (("f", "fold"), ("c", "corrector"), ("w", "contour")):
        m = fam == f
        if m.sum() > 3:
            r_f = float(np.corrcoef(dF[m], -dH[m])[0, 1])
            P_f = float(np.median(np.abs(dT[m])) / np.median(np.abs(dF[m]) + np.abs(dH[m])))
            emit(f"      {lab:>10} family: rho {r_f:+.3f}, P {P_f:.3f}")
    if rho >= RHO_TRADE and P <= PIN_TRADE:
        v = "(a) TRADE — the elastic law is CONFIRMED (weld cost of a self-dual pair)"
    elif rho < RHO_WRONG or P > PIN_WRONG:
        v = "(b) DIAGNOSIS WRONG — shares do not trade / total not pinned"
    else:
        v = "PARTIAL/AMBIGUOUS — between the pre-registered branches"
    emit(f"\n[measured] TEST A VERDICT: {v}")
    emit("=" * 78)
    return dict(rho=rho, P=P, verdict=v, per_move=per_move, p_win=p_win,
                dF=dF, dH=dH, dT=dT, fam=fam, text="\n".join(out))


# ---------------------------------------------------------------------------
# STEP 3 — TEST B (balance locus)
# ---------------------------------------------------------------------------

def run_testB(ctx, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    meshes, eng, wf_alt = ctx["meshes"], ctx["eng"], ctx["wf_alt"]
    emit("=" * 78)
    emit("STEP 3 — TEST B: BALANCE LOCUS (does the floor sit where |F| ~ |H|?)")
    emit("=" * 78)

    # sigma: constant-shift scan
    ss = np.linspace(-0.9, 0.9, 37)
    lnCT = np.empty((37, len(GRIDC)))
    lnR = np.empty((37, len(GRIDC)))
    for k, s in enumerate(ss):
        lanes = engine_lanes(eng, np.full(len(TS), s))
        lnCT[k] = lanes["lnC_T"]
        lnR[k] = np.log(lanes["M_F"] / lanes["M_H"])
    s_floor = ss[np.argmin(lnCT, axis=0)]
    s_bal = np.full(len(GRIDC), np.nan)
    for i in range(len(GRIDC)):
        sgn = np.sign(lnR[:, i])
        cross = np.where(np.diff(sgn) != 0)[0]
        if len(cross):
            k = cross[0]
            f0, f1 = lnR[k, i], lnR[k + 1, i]
            s_bal[i] = ss[k] + (ss[k + 1] - ss[k]) * (-f0) / (f1 - f0)
    okb = np.isfinite(s_bal)
    emit("\n[measured] (sigma) per cell: floor shift s* vs mass-balance shift s_bal:")
    for i, cell in enumerate(GRIDC):
        emit(f"      {str(cell):>18}: s*={s_floor[i]:+.3f}   s_bal="
             + (f"{s_bal[i]:+.3f}" if okb[i] else "none in range"))
    if okb.sum() >= 5:
        r_sig = float(np.corrcoef(s_floor[okb], s_bal[okb])[0, 1])
        emit(f"      correlation (n={int(okb.sum())}): r = {r_sig:+.3f}")
    else:
        r_sig = float("nan")
        emit(f"      too few balance crossings in range ({int(okb.sum())}) — censored")

    # nu scan
    emit("\n[measured] (nu) lane balance vs cost floor over nu in {2,4,8,16,24}:")
    lnCT_nu = np.empty((len(NUS_SCAN), len(GRIDC)))
    lnR_nu = np.empty((len(NUS_SCAN), len(GRIDC)))
    for k, nu in enumerate(NUS_SCAN):
        lanes = lane_eval(meshes, GRIDC, wf_alt, nu=nu)
        lnCT_nu[k] = lanes["lnC_T"]
        lnR_nu[k] = np.log(lanes["M_F"] / lanes["M_H"])
    lnu = np.log(NUS_SCAN)
    nu_floor = np.array(NUS_SCAN)[np.argmin(lnCT_nu, axis=0)]
    nu_bal = np.full(len(GRIDC), np.nan)
    for i in range(len(GRIDC)):
        sgn = np.sign(lnR_nu[:, i])
        cross = np.where(np.diff(sgn) != 0)[0]
        if len(cross):
            k = cross[0]
            f0, f1 = lnR_nu[k, i], lnR_nu[k + 1, i]
            nu_bal[i] = math.exp(lnu[k] + (lnu[k + 1] - lnu[k]) * (-f0) / (f1 - f0))
    okn = np.isfinite(nu_bal)
    for i, cell in enumerate(GRIDC):
        emit(f"      {str(cell):>18}: nu*={nu_floor[i]:5.1f}   nu_bal="
             + (f"{nu_bal[i]:6.2f}" if okn[i] else "no crossing")
             + f"   lnR(nu) = " + " ".join(f"{v:+.2f}" for v in lnR_nu[:, i]))
    if okn.sum() >= 5:
        from scipy.stats import spearmanr
        r_nu = float(spearmanr(nu_floor[okn], nu_bal[okn]).statistic)
        emit(f"      Spearman (n={int(okn.sum())}): r = {r_nu:+.3f}")
    else:
        r_nu = float("nan")
        emit(f"      balance crossings in nu-range: {int(okn.sum())}/18 — mostly censored")
    emit("=" * 78)
    return dict(r_sig=r_sig, r_nu=r_nu, s_floor=s_floor, s_bal=s_bal,
                nu_floor=nu_floor, nu_bal=nu_bal, text="\n".join(out))


# ---------------------------------------------------------------------------
# STEP 4 — TEST C (uncertainty scaling) + BONUS (elastic constant)
# ---------------------------------------------------------------------------

def run_testC_bonus(ctx, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    base = ctx["base"]
    emit("=" * 78)
    emit("STEP 4 — TEST C: UNCERTAINTY SCALING + BONUS: THE ELASTIC CONSTANT")
    emit("=" * 78)
    CF, CH = np.exp(base["lnC_F"]), np.exp(base["lnC_H"])
    stds = {
        "lnC_F": base["lnC_F"].std(), "lnC_H": base["lnC_H"].std(),
        "ln(C_F*C_H)": (base["lnC_F"] + base["lnC_H"]).std(),
        "C_F+C_H (linear)": (CF + CH).std(),
        "lnC_T (true total)": base["lnC_T"].std(),
    }
    emit("\n[measured] spreads across the 18-cell grid:")
    for k, v in stds.items():
        emit(f"      std {k:>20} = {v:.3f}")
    ratio = stds["lnC_T (true total)"] / min(stds["lnC_F"], stds["lnC_H"])
    emit(f"      joint ratio std(lnC_T)/min(lanes) = {ratio:.3f}"
         f"  (joint verdict if < {JOINT_RATIO})")
    joint = ratio < JOINT_RATIO
    emit(f"      -> {'JOINT/uncertainty quantity: total flatter than either chart' if joint else 'NOT flatter: the total is not a joint smoothing of the lanes'}")

    emit("\n[measured] BONUS — elastic-constant fit: lnC_T ~ [1, ln lf^2, ln(X/8), ln(1+xi)]:")
    Xf = np.array([[1.0, math.log(c[1] * c[2] ** 2), math.log(c[3] / 8.0),
                    math.log(1.0 + c[0])] for c in GRIDC])
    y = base["lnC_T"]
    beta, res, *_ = np.linalg.lstsq(Xf, y, rcond=None)
    yhat = Xf @ beta
    R2 = 1.0 - np.sum((y - yhat) ** 2) / np.sum((y - y.mean()) ** 2)
    emit(f"      beta = [const {beta[0]:+.3f}, ln lf^2 {beta[1]:+.3f},"
         f" ln(X/8) {beta[2]:+.3f}, ln(1+xi) {beta[3]:+.3f}];  R^2 = {R2:.3f}")
    if R2 >= 0.8:
        emit(f"      [measured] law stated: wall height is a function of the cell's")
        emit(f"      structural data at R^2={R2:.2f}.")
    else:
        emit(f"      R^2 < 0.8: NO clean elastic-constant law from these features alone.")
    emit(f"      [interpretation] a GL(3) prediction requires the GL(3) gamma factors in")
    emit(f"      the kernels (different Ftilde/GR pair); out of scope for this instrument.")
    emit("=" * 78)
    return dict(stds=stds, ratio=ratio, joint=joint, beta=beta, R2=R2, text="\n".join(out))


# ---------------------------------------------------------------------------
# STEP 5 — CONTROLS
# ---------------------------------------------------------------------------

def run_controls(ctx, tA, verbose=True):
    out = []

    def emit(s=""):
        out.append(s)
        if verbose:
            print(s, flush=True)

    meshes, base, wf_alt = ctx["meshes"], ctx["base"], ctx["wf_alt"]
    emit("=" * 78)
    emit("STEP 5 — CONTROLS")
    emit("=" * 78)

    # (i) quadrature doubling on the lane splits
    emit("\n[measured] (i) quadrature doubling (t x2, Bessel s x2), baseline + wave w1:")
    ts2 = np.linspace(-CT.T_C, CT.T_C, 2 * len(TS))
    sg2 = np.linspace(0.0, 6.0, 5000)
    l2 = lane_eval(meshes, GRIDC, wf_alt, ts=ts2, sg=sg2)
    d0 = max(np.abs(l2[f"lnC_{k}"] - base[f"lnC_{k}"]).max() for k in "FHT")
    wv = CT.random_waves(1)[0]
    l1 = lane_eval(meshes, GRIDC, wf_alt, wave_params=wv)
    l3 = lane_eval(meshes, GRIDC, wf_alt, wave_params=wv, ts=ts2, sg=sg2)
    d1 = max(np.abs(l3[f"lnC_{k}"] - l1[f"lnC_{k}"]).max() for k in "FHT")
    emit(f"      max |Delta lnC_lane|: baseline {d0:.4f}, wave {d1:.4f}  (tol {DOUBLING_TOL})")
    conv_ok = d0 < DOUBLING_TOL and d1 < DOUBLING_TOL
    emit(f"      -> {'PASS' if conv_ok else 'FAIL (lane numbers flagged)'}")

    # (ii) scrambled-kernel lane check on the same move subset (w1-w3, f3)
    emit(f"\n[measured] (ii) SCRAMBLED lane check (house recipe, seed {SEED}):")
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
    base_s = lane_eval(meshes, GRIDC, wf_alt, scr=scr)
    dF_s, dH_s, dT_s = [], [], []
    dF_r, dH_r = [], []
    subset = ["w1 random-wave", "w2 random-wave", "w3 random-wave", "f3 width-0.8"]
    waves = CT.random_waves(3)
    movecfg = {"w1 random-wave": ("wave", waves[0]), "w2 random-wave": ("wave", waves[1]),
               "w3 random-wave": ("wave", waves[2]),
               "f3 width-0.8": ("window", {c: wfun_bump(0.8) for c in GRIDC})}
    for name in subset:
        kind, obj = movecfg[name]
        if kind == "wave":
            lanes_s = lane_eval(meshes, GRIDC, wf_alt, wave_params=obj, scr=scr)
        else:
            lanes_s = lane_eval(meshes, GRIDC, obj, scr=scr)
        dF_s += list(lanes_s["lnC_F"] - base_s["lnC_F"])
        dH_s += list(lanes_s["lnC_H"] - base_s["lnC_H"])
        dT_s += list(lanes_s["lnC_T"] - base_s["lnC_T"])
        a, b, _, _ = tA["per_move"][name]
        dF_r += list(a)
        dH_r += list(b)
    rho_s = float(np.corrcoef(dF_s, [-x for x in dH_s])[0, 1])
    rho_r = float(np.corrcoef(dF_r, [-x for x in dH_r])[0, 1])
    emit(f"      trade correlation on the subset: real {rho_r:+.3f} vs"
         f" scrambled {rho_s:+.3f}")
    if rho_r - rho_s >= 0.3:
        emit(f"      -> trade VANISHES under scrambling: the F/H tie is coherence-borne")
        emit(f"         (FE-tied kernel), as the diagnosis requires — control PASS")
        scr_verdict = "vanishes (coherence-borne)"
    elif abs(rho_r - rho_s) < 0.3:
        emit(f"      -> trade SURVIVES scrambling: kernel-structural (sigma-seesaw of the")
        emit(f"         Mellin pair), NOT specific to the coherent kernel — reported at")
        emit(f"         full prominence; weakens the 'FE-weld' reading of Test A")
        scr_verdict = "survives (kernel-structural)"
    else:
        emit(f"      -> scrambled trade EXCEEDS real — anomalous, flagged")
        scr_verdict = "anomalous"
    emit("=" * 78)
    return dict(conv_ok=conv_ok, rho_s=rho_s, rho_r=rho_r, scr_verdict=scr_verdict,
                text="\n".join(out))


# ---------------------------------------------------------------------------
# drivers
# ---------------------------------------------------------------------------

def run_tests():
    print("mb_elastic self-tests = lane-split anchor gate")
    ok, _, _ = run_gate()
    print(f"\nLANE GATE: {'PASS' if ok else 'FAIL'}")
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
    txt1 = run_lanes(ctx)
    buf.append("\n\n" + txt1)
    tA = run_testA(ctx)
    buf.append("\n\n" + tA["text"])
    tB = run_testB(ctx)
    buf.append("\n\n" + tB["text"])
    tC = run_testC_bonus(ctx)
    buf.append("\n\n" + tC["text"])
    ctrl = run_controls(ctx, tA)
    buf.append("\n\n" + ctrl["text"])

    fin = []
    fin.append("=" * 78)
    fin.append("ELASTIC-PAIR VERDICT (pre-registered readings)")
    fin.append("=" * 78)
    fin.append(f"[measured] TEST A (elastic conservation): {tA['verdict']}")
    fin.append(f"    pooled rho = {tA['rho']:+.3f}, pinning P = {tA['P']:.3f}"
               f"  (thresholds: (a) rho>={RHO_TRADE} & P<={PIN_TRADE};"
               f" (b) rho<{RHO_WRONG} | P>{PIN_WRONG})")
    fin.append(f"[measured] TEST B (balance locus): sigma-correlation r = {tB['r_sig']:+.3f};"
               f" nu: {int(np.isfinite(tB['nu_bal']).sum())}/18 cells have a balance"
               f" crossing (Spearman r = {tB['r_nu']:+.3f} where defined)")
    fin.append(f"[measured] TEST C (uncertainty scaling): std lnC_F {tC['stds']['lnC_F']:.3f},"
               f" lnC_H {tC['stds']['lnC_H']:.3f}, total {tC['stds']['lnC_T (true total)']:.3f}"
               f" -> joint ratio {tC['ratio']:.3f}"
               f" ({'JOINT quantity' if tC['joint'] else 'not joint-flatter'})")
    fin.append(f"[measured] BONUS: lnC_T ~ structural features R^2 = {tC['R2']:.3f}"
               + (f"; law beta = {np.round(tC['beta'],3).tolist()}" if tC["R2"] >= 0.8
                  else " — no clean law"))
    fin.append(f"[controls] doubling {'PASS' if ctrl['conv_ok'] else 'FAIL'};"
               f" scrambled trade: real {ctrl['rho_r']:+.2f} vs scr {ctrl['rho_s']:+.2f}"
               f" -> {ctrl['scr_verdict']}")
    fin.append(f"[budget] total wall time {time.time()-t_start:.0f}s")
    fin.append("=" * 78)
    fintxt = "\n".join(fin)
    print("\n" + fintxt)
    buf.append("\n\n" + fintxt)
    _write(buf)
    _write_summary(ctx, tA, tB, tC, ctrl)


def _write(buf):
    path = os.path.join(HERE, "mb_elastic_results.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(buf))
    print(f"\n[written] {path}")


def _write_summary(ctx, tA, tB, tC, ctrl):
    lines = []
    lines.append("MB ELASTIC-PAIR — SUMMARY (detail in mb_elastic_results.txt)")
    lines.append("")
    lines.append("Gate: PASS — lane-sum total reproduces mb_contour's recorded baseline")
    lines.append("(80x80 spots + mean/std); |V_F+V_H| == J_house to 1e-9; engine == direct.")
    lines.append("Analysis on the extended mesh (0.05,1.45) so the fold's 1.35-wide windows")
    lines.append("stay never-clip legal; deltas are within-mesh.")
    lines.append("")
    lines.append(f"TEST A [measured]: {tA['verdict']}")
    lines.append(f"pooled trade rho = {tA['rho']:+.2f}, pinning P = {tA['P']:.2f} over 8")
    lines.append("recorded campaign moves (fold endpoint/midpoint/width, corrector winner,")
    lines.append("3 seeded waves + refit wavy winner) x 18 cells.")
    lines.append(f"TEST B [measured]: floor-vs-balance correlation r_sigma = {tB['r_sig']:+.2f};"
                 f" nu-balance crossings {int(np.isfinite(tB['nu_bal']).sum())}/18"
                 f" (Spearman {tB['r_nu']:+.2f} where defined).")
    lines.append(f"TEST C [measured]: lane spreads F {tC['stds']['lnC_F']:.2f} /"
                 f" H {tC['stds']['lnC_H']:.2f}; true total {tC['stds']['lnC_T (true total)']:.2f};"
                 f" joint ratio {tC['ratio']:.2f} -> "
                 + ("JOINT (total flatter than either chart)." if tC["joint"]
                    else "not joint-flatter."))
    lines.append(f"BONUS: structural fit R^2 = {tC['R2']:.2f}"
                 + ("; law stated in results." if tC["R2"] >= 0.8 else " — no clean law."))
    lines.append(f"Controls: doubling {'PASS' if ctrl['conv_ok'] else 'FAIL'};"
                 f" scrambled trade {ctrl['scr_verdict']}"
                 f" (real {ctrl['rho_r']:+.2f} vs scr {ctrl['rho_s']:+.2f}).")
    lines.append("")
    lines.append("Flags: lane costs live at nu*=8 on the extended mesh (mesh-dependence of C")
    lines.append("~0.1 flagged in mb_contour); fold moves use recorded endpoint widths, not a")
    lines.append("re-run fold; GL(3) extrapolation is [interpretation]-only (needs GL(3)")
    lines.append("gamma factors).")
    path = os.path.join(HERE, "mb_elastic_summary.txt")
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
