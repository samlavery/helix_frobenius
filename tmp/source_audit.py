"""source_audit.py — adversarial RECALL audit for EveryZeroHasSource.

The falsifiability-register instrument. Owner's dichotomy: every zero of the 1D
readout has a SOURCE in the 3D phasor bank (a focal-closure/growth-window event
the locator detects from clock data alone) vs. a SOURCELESS zero = a readout
zero the bank does not predict.

METHOD (three ontological layers, never blended):
  (1) CENSUS  [MEASURED, 1D-readout verification role — mpmath permitted HERE
      by design: the census is the readout side]. For each family + window,
      count zeros by argument-principle phase-winding of L along the critical
      line, then locate each to high precision by mp.findroot. This is the
      definitive list of readout zeros in-window.
  (2) SOURCES [MEASURED, 3D no-oracle]. Run focal_closure.scan (the canonical
      locator: omega=log Z coupling + growth window, NO L-value in the loop)
      over the same window. Enumerate every source (closure) event.
  (3) MATCH: 1:1 census<->sources with distances. RECALL = census zeros with a
      source (a miss is a REGISTER HIT). PRECISION = source events with a census
      zero (an extra is a GHOST). Report locator-vs-census residuals.

THE HARD CONSTRAINT (the honest exponential price, stated in focal_closure.py):
  the locator reads at head height Z = e^y and a zero at ordinate t is a closure
  event at y = t, so the bank needs N = int(e^t) phasors. t=400 => 5e173
  phasors: physically impossible. The feasible ceiling on one machine is
  N ~ 1e8 => t ~ 18.4. So "fresh ground" here means: windows ABOVE the prior
  validation ceiling (DEMO_WINDOWS / REFERENCE_ORDINATES top out at t ~ 14-15,
  and only ever check the first 1-2 zeros per family) but at feasible height.
  We audit EVERY zero in each window, not just the first — that is the fresh,
  adversarial part the prior suite never did.
"""

from __future__ import annotations

import math
import sys
import time

import mpmath as mp
import numpy as np

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")
import focal_closure as fc

mp.mp.dps = 30


# ---------------------------------------------------------------------------
# CENSUS side (1D readout — mpmath, verification role only)
# ---------------------------------------------------------------------------

def zeta_hardy_Z(t: float):
    """Hardy Z(t): real on the line, sign changes <=> zeta zeros. Isolates
    ordinates without needing complex-argument tracking."""
    return mp.siegelz(t)


def zeta_zeros_in(t0: float, t1: float):
    """Definitive zeta-zero ordinates in (t0,t1). Uses mp.zetazero (exact,
    argument-principle-backed in mpmath) — the readout ground truth."""
    zeros = []
    k = 1
    # advance to window
    while float(mp.im(mp.zetazero(k))) < t0:
        k += 1
    while True:
        t = float(mp.im(mp.zetazero(k)))
        if t > t1:
            break
        zeros.append(t)
        k += 1
    return zeros


def dirichlet_character(q: int, gen: int, order: int):
    """Same character focal_closure.character_values builds, in mpmath."""
    vals = [mp.mpc(0)] * q
    zeta = mp.e ** (2j * mp.pi / order)
    vals[1] = mp.mpc(1)
    a, k = gen, 1
    while a != 1:
        vals[a] = zeta ** k
        a = (a * gen) % q
        k += 1
    return vals


def make_L_dirichlet(q: int, vals):
    """L(s,chi) = q^{-s} sum_{a=1}^{q-1} chi(a) zeta_Hurwitz(s, a/q)."""
    def L(s):
        return q ** (-s) * sum(vals[a] * mp.zeta(s, mp.mpf(a) / q)
                               for a in range(1, q))
    return L


def winding_count(L, t0: float, t1: float, x0: float = 6.0, npts: int = 1600):
    """Argument-principle zero count in the box Re s in [1-x0? ...]. We use the
    critical line directly: for a primitive L on RH the zeros are on Re=1/2, so
    we count sign structure of the completed real signature. For a COMPLEX
    character L is not real on the line, so instead count zeros by the winding
    of L along a rectangle hugging the critical line.

    Rectangle: corners (0.5-d, t0) -> (0.5+d, t0) -> (0.5+d,t1) -> (0.5-d,t1).
    With d small (0.25) it encloses exactly the on-line zeros in (t0,t1) if RH
    holds locally; if a zero were OFF the line at |Re-1/2|>d it would be MISSED
    by this box but CAUGHT by widening d — we cross-check with d in {0.25,0.9}.
    """
    def winding_for(d):
        def seg(a, b, n):
            return [a + (b - a) * mp.mpf(i) / n for i in range(n + 1)]
        s_pts = []
        n = npts // 4
        c1 = mp.mpc(0.5 - d, t0)
        c2 = mp.mpc(0.5 + d, t0)
        c3 = mp.mpc(0.5 + d, t1)
        c4 = mp.mpc(0.5 - d, t1)
        s_pts += seg(c1, c2, n)[:-1]
        s_pts += seg(c2, c3, n)[:-1]
        s_pts += seg(c3, c4, n)[:-1]
        s_pts += seg(c4, c1, n)[:-1]
        vals_L = [L(s) for s in s_pts]
        total = mp.mpf(0)
        for i in range(len(vals_L)):
            a = vals_L[i]
            b = vals_L[(i + 1) % len(vals_L)]
            total += mp.arg(b / a)
        return int(round(float(total / (2 * mp.pi))))
    # winding is an integer count; 15 digits is ample and ~4x faster.
    old = mp.mp.dps
    mp.mp.dps = 15
    try:
        return winding_for(0.25), winding_for(0.9)
    finally:
        mp.mp.dps = old


def locate_dirichlet_zeros(L, t0: float, t1: float, scan_n: int = 800):
    """Definitive zero ordinates of a complex-character L in (t0,t1): scan |L|
    on the line for minima, refine each by 2D Newton (findroot on complex L)."""
    # coarse scan at low precision (fast), refine each candidate at full dps.
    old = mp.mp.dps
    mp.mp.dps = 15
    ts = np.linspace(t0, t1, scan_n)
    mags = np.array([float(abs(L(mp.mpc(0.5, float(t))))) for t in ts])
    mp.mp.dps = old
    zeros = []
    med = float(np.median(mags))
    for i in range(1, len(ts) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.3 * med:
            try:
                r = mp.findroot(lambda s: L(s), mp.mpc(0.5, float(ts[i])))
            except Exception:
                continue
            t = float(mp.im(r))
            re = float(mp.re(r))
            if t0 <= t <= t1 and abs(L(r)) < 1e-10:
                if not any(abs(t - z[0]) < 1e-6 for z in zeros):
                    zeros.append((t, re, float(abs(L(r)))))
    zeros.sort()
    return zeros


# ---------------------------------------------------------------------------
# MATCHING
# ---------------------------------------------------------------------------

def match(census_ts, source_ys, tol=1e-2):
    """1:1 greedy nearest matching. Returns (pairs, misses, ghosts).
    pairs = [(census_t, source_y, |diff|)]; misses = census with no source
    (REGISTER HITS); ghosts = sources with no census zero."""
    census = list(census_ts)
    sources = list(source_ys)
    used_src = set()
    pairs = []
    misses = []
    for ct in census:
        best_j, best_d = None, None
        for j, sy in enumerate(sources):
            if j in used_src:
                continue
            d = abs(ct - sy)
            if best_d is None or d < best_d:
                best_j, best_d = j, d
        if best_j is not None and best_d <= tol:
            used_src.add(best_j)
            pairs.append((ct, sources[best_j], best_d))
        else:
            misses.append(ct)
    ghosts = [sources[j] for j in range(len(sources)) if j not in used_src]
    return pairs, misses, ghosts


# ---------------------------------------------------------------------------
# AUDIT DRIVER
# ---------------------------------------------------------------------------

OUT = []
def emit(s=""):
    print(s, flush=True)
    OUT.append(s)


def audit_family(label, family_name, census_zeros, y0, y1, per_unit=240,
                 depth_cut=2e-2, match_tol=1.5e-2):
    fam = fc.FAMILIES[family_name]
    N = int(math.exp(y1))
    emit(f"\n{'='*72}")
    emit(f"{label}   window t in [{y0}, {y1}]   (bank head N=int(e^t) up to {N:,})")
    emit(f"{'='*72}")

    emit(f"(1) CENSUS [1D readout, measured]: {len(census_zeros)} zero(s)")
    for t in census_zeros:
        emit(f"      t = {t:.9f}")

    emit(f"(2) SOURCES [3D locator, no-oracle, growth window]:")
    t0 = time.time()
    events = fc.scan(fam, y0, y1, per_unit=per_unit, depth_cut=depth_cut)
    dt = time.time() - t0
    events = sorted(events, key=lambda e: e.y)
    for e in events:
        emit(f"      y = {e.y:.9f}   Z=e^y={e.height:.3e}   depth={e.depth:.2e}")
    emit(f"      ({len(events)} source event(s); scan {dt:.1f}s)")

    source_ys = [e.y for e in events]
    pairs, misses, ghosts = match(census_zeros, source_ys, tol=match_tol)

    emit(f"(3) MATCH  (tol={match_tol:g}):")
    for ct, sy, d in pairs:
        emit(f"      census t={ct:.9f}  <->  source y={sy:.9f}   |diff|={d:.2e}")
    recall_num = len(pairs)
    recall_den = len(census_zeros)
    prec_num = len(pairs)
    prec_den = len(source_ys)
    emit(f"    RECALL    = {recall_num}/{recall_den}"
         + (f"   MISSES (REGISTER HITS): {['%.6f'%m for m in misses]}" if misses else "   (no missed zeros)"))
    emit(f"    PRECISION = {prec_num}/{prec_den}"
         + (f"   GHOSTS: {['%.6f'%g for g in ghosts]}" if ghosts else "   (no ghosts)"))
    if pairs:
        resid = [d for _, _, d in pairs]
        emit(f"    locator-vs-census residuals: min={min(resid):.2e}"
             f"  max={max(resid):.2e}  median={float(np.median(resid)):.2e}")
    return dict(recall=(recall_num, recall_den), precision=(prec_num, prec_den),
                misses=misses, ghosts=ghosts,
                residuals=[d for _, _, d in pairs])


def main():
    emit("SOURCE AUDIT — EveryZeroHasSource falsifiability register")
    emit("Fresh windows ABOVE prior validation (DEMO_WINDOWS top out at t~14-15,")
    emit("and only ever check the FIRST 1-2 zeros/family). Here every in-window")
    emit("zero is audited. Feasibility ceiling N=e^t<~1e8 => t<~18.4 (the honest")
    emit("exponential price; t=400 would need e^400~5e173 phasors).")
    emit(f"mpmath dps={mp.mp.dps}; numpy {np.__version__}")

    results = {}

    # --- FAMILY (a): zeta / eta channel. Fresh window t in [13.9, 16.0].
    #     Prior 'eta' DEMO window was [13.6,14.6] (only the first zero, t=14.13).
    #     [13.9,16.0] re-audits that zero PLUS the span up to 16 is empty (next
    #     zeta zero is t=21.02) — a clean recall+precision test: exactly one
    #     zero must appear, and >1.8 units of empty window must yield NO ghost.
    #     N=int(e^16)=8.9e6 is the feasibility ceiling for a dense eta scan
    #     (e^18=6.6e7 ran but at ~4 s/eval it is impractically slow).
    zz = zeta_zeros_in(13.9, 16.0)
    results["eta_13.9_16"] = audit_family(
        "FAMILY (a) zeta/eta", "eta", zz, 13.9, 16.0, per_unit=160)

    # --- FAMILY (b): complex Dirichlet chi7c (mod 7, order 6). Fresh window
    #     t in [9.5, 16.0]. Prior chi7c DEMO window was [1.6,10.0] (checked only
    #     the first zeros). [9.5,16.0] is almost entirely above it and dense
    #     (3 zeros), with N=int(e^16)=8.9e6 phasors — feasible.
    q7 = 7
    vals7 = dirichlet_character(7, 3, 6)
    L7 = make_L_dirichlet(q7, vals7)
    w_narrow, w_wide = winding_count(L7, 9.5, 16.0)
    emit(f"\n[chi7c argument-principle box count in t in [9.5,16.0]: "
         f"d=0.25 -> {w_narrow},  d=0.9 -> {w_wide}  "
         f"({'consistent, all on-line' if w_narrow==w_wide else 'OFF-LINE ZERO SUSPECTED'})]")
    z7 = locate_dirichlet_zeros(L7, 9.5, 16.0, scan_n=1200)
    emit(f"[chi7c located zeros: {len(z7)} vs winding {w_wide}]")
    census7 = [t for (t, re, mag) in z7]
    results["chi7c_9.5_16"] = audit_family(
        "FAMILY (b) chi7c (complex, mod 7 order 6)", "chi7c", census7,
        9.5, 16.0, per_unit=160)

    # --- (4) BOUNDARY STRESS: highest feasible height (recall vs height).
    #     The exponential price forbids high zeta ordinates: zeta zero #2 at
    #     t=21.022 needs N=e^21=1.3e9 phasors (~42 GB) -> INFEASIBLE. The
    #     highest feasible zero is the chi7c zero at t=15.747 (N=e^15.75=6.9e6).
    #     We stress it with a DEEP, finely-sampled bank on a tight window to
    #     probe whether recall/residual degrade at the ceiling of what runs.
    emit(f"\n{'#'*72}")
    emit("(4) BOUNDARY STRESS — highest feasible height (recall vs height)")
    emit("[zeta zero #2 t=21.022 would need e^21~1.3e9 phasors (~42 GB): "
         "INFEASIBLE — the honest exponential price. Highest feasible zero is")
    emit(" chi7c t=15.747, N=int(e^15.9)=8.0e6. Deep tight-window probe:]")
    emit(f"{'#'*72}")
    z7hi = [t for (t, re, mag) in locate_dirichlet_zeros(L7, 15.5, 15.9)]
    N_stress = int(math.exp(15.9))
    emit(f"[target: chi7c zero at t~15.747; bank head N=int(e^15.9)={N_stress:,}]")
    results["chi7c_stress_15.7"] = audit_family(
        "BOUNDARY chi7c (highest feasible)", "chi7c", z7hi, 15.55, 15.90,
        per_unit=400, match_tol=2e-2)

    # --------- SUMMARY ---------
    emit(f"\n{'='*72}")
    emit("SUMMARY")
    emit(f"{'='*72}")
    tot_r_n = sum(r["recall"][0] for r in results.values())
    tot_r_d = sum(r["recall"][1] for r in results.values())
    tot_p_n = sum(r["precision"][0] for r in results.values())
    tot_p_d = sum(r["precision"][1] for r in results.values())
    all_resid = [d for r in results.values() for d in r["residuals"]]
    all_misses = [(k, r["misses"]) for k, r in results.items() if r["misses"]]
    all_ghosts = [(k, r["ghosts"]) for k, r in results.items() if r["ghosts"]]
    for k, r in results.items():
        emit(f"  {k:20s}  recall {r['recall'][0]}/{r['recall'][1]}"
             f"   precision {r['precision'][0]}/{r['precision'][1]}"
             f"   resid_max={max(r['residuals']) if r['residuals'] else float('nan'):.1e}")
    emit(f"  TOTAL recall={tot_r_n}/{tot_r_d}  precision={tot_p_n}/{tot_p_d}")
    if all_resid:
        emit(f"  residuals over all matches: min={min(all_resid):.2e}"
             f"  max={max(all_resid):.2e}  median={float(np.median(all_resid)):.2e}")
    emit(f"  REGISTER HITS (sourceless zeros): "
         f"{all_misses if all_misses else 'NONE'}")
    emit(f"  GHOSTS (sourceless-free extra events): "
         f"{all_ghosts if all_ghosts else 'NONE'}")

    with open("/Users/samuellavery/work/helix_frobenius/tmp/source_audit_results.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")


if __name__ == "__main__":
    main()
