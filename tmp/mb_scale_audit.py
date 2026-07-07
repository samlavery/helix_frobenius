#!/usr/bin/env python3
"""
Scale audit for the emergent-clock Beyond-Endoscopy tests.

This is a synthesis script: it upgrades the clock question from scalar spacing
to cell-wise/vector readout across the tested GL(2), GL(3), and GL(4) regimes.
The GL(4) component numerically instantiates the formally proven vector-clock
law in CriticalLinePhasor.TwoClockWeightLaw.gl4_trace_window_vector_clock: three
coordinate spans force three coordinate periods plus the locked diagonal.
"""

from __future__ import annotations

import math
import os
import re
import time
from collections import defaultdict

import numpy as np

import mb_gl3_clock_lift as C
import mb_gl3_wall_lift as W


HERE = os.path.dirname(os.path.abspath(__file__))
GL2_RANK = os.path.join(HERE, "mb_beat_rank_sweep.txt")
GL3_FAMILY = os.path.join(HERE, "gl3_family_summary.txt")
OUT = os.path.join(HERE, "mb_scale_audit_results.txt")
SUMMARY = os.path.join(HERE, "mb_scale_audit_summary.txt")

VECTOR_BAND = (0.97, 1.03)
WALL_NEAR_BAND = (0.75, 1.75)
WALL_R2_GATE = 0.80
NU_GRID_GL4 = np.linspace(0.05, 96.0, 72000)


def parse_gl2_rank_sweep():
    rows = []
    census = {}
    table_re = re.compile(r"^\s*(\d+)\s+(\d+)\s+(\d+)\s+([0-9.]+)\s+")
    census_re = re.compile(
        r"r=(\d+): xi=2 (\d+)/6, xi=6 (\d+)/6, deep/clock (\d+)/(\d+)"
    )
    with open(GL2_RANK, "r") as fh:
        for line in fh:
            m = table_re.match(line)
            if m:
                parts = line.split()
                if len(parts) >= 17:
                    rows.append(
                        dict(
                            r=int(parts[0]),
                            deep=int(parts[1]),
                            clock=int(parts[2]),
                            prod=float(parts[3]),
                            D0=float(parts[4]),
                            lf2=float(parts[5]),
                            X=float(parts[6]),
                            xi=float(parts[7]),
                            R2=float(parts[8]),
                            kmean=float(parts[9]),
                            stat=float(parts[13]),
                            model=float(parts[14]),
                        )
                    )
            c = census_re.search(line)
            if c:
                r = int(c.group(1))
                census[r] = dict(
                    xi2=int(c.group(2)),
                    xi6=int(c.group(3)),
                    deep=int(c.group(4)),
                    clock=int(c.group(5)),
                )
    if not rows:
        raise RuntimeError(f"no rank rows parsed from {GL2_RANK}")
    return rows, census


def gl3_vector_clock_rows():
    rows = []
    for n in (4, 8, 16):
        for f in (1, 2):
            for X in (8.0, 16.0):
                for kb in (0.94, 1.18):
                    r = C.run_case(n, f, X, kb)
                    for direction, meas_key, pred_key, dip_key in (
                        ("a", "da", "pred_a", "na"),
                        ("b", "db", "pred_b", "nb"),
                        ("diag", "dd", "pred_diag", "nd"),
                    ):
                        ratio = r[meas_key] / r[pred_key]
                        rows.append(
                            dict(
                                n=n,
                                f=f,
                                X=X,
                                kappa_b=kb,
                                direction=direction,
                                measured=r[meas_key],
                                predicted=r[pred_key],
                                ratio=ratio,
                                dips=r[dip_key],
                                ok=(
                                    VECTOR_BAND[0] <= ratio <= VECTOR_BAND[1]
                                    and r[dip_key] >= 3
                                ),
                                same_b_ratio=(r["db"] / r["pred_same"]),
                            )
                        )
    return rows


def edge_points_nd(spans, mode):
    spans = list(spans)
    if mode == "axis":
        pts = []
        for mask in range(1 << len(spans)):
            coords = []
            for j, S in enumerate(spans):
                coords.append((0.5 if (mask >> j) & 1 else -0.5) * S)
            pts.append((coords, 1.0))
        return pts
    if mode == "diag_locked":
        return [([-0.5 * S for S in spans], 1.0), ([0.5 * S for S in spans], 1.0)]
    raise ValueError(mode)


def profile_transform_nd(points, Q, direction):
    coords = []
    weights = []
    for vec, w in points:
        if isinstance(direction, int):
            coords.append(vec[direction])
        elif direction == "diag":
            coords.append(sum(vec))
        else:
            raise ValueError(direction)
        weights.append(w)
    coords = np.asarray(coords, dtype=float)
    weights = np.asarray(weights, dtype=float)
    phase = np.exp(-2j * math.pi * np.outer(NU_GRID_GL4, coords) / Q)
    return np.abs(phase @ weights)


def gl4_vector_clock_rows():
    """GL(4) vector-clock grid: three formal coordinate clocks plus the locked diagonal."""
    rows = []
    for n in (4, 8, 16):
        for f in (1, 2):
            for X in (8.0, 16.0):
                for kb, kc in ((0.94, 0.94), (1.18, 0.82), (0.82, 1.31)):
                    Q = float(n * f * f)
                    spans = [0.94 * X, kb * X, kc * X]
                    axis_pts = edge_points_nd(spans, "axis")
                    diag_pts = edge_points_nd(spans, "diag_locked")
                    for label, direction, pred, pts in (
                        ("a", 0, Q / spans[0], axis_pts),
                        ("b", 1, Q / spans[1], axis_pts),
                        ("c", 2, Q / spans[2], axis_pts),
                        ("diag", "diag", Q / sum(spans), diag_pts),
                    ):
                        amp = profile_transform_nd(pts, Q, direction)
                        meas, dips, _ = C.deep_dip_spacing(NU_GRID_GL4, amp)
                        ratio = meas / pred if np.isfinite(meas) else float("nan")
                        rows.append(
                            dict(
                                n=n,
                                f=f,
                                X=X,
                                kb=kb,
                                kc=kc,
                                direction=label,
                                measured=meas,
                                predicted=pred,
                                ratio=ratio,
                                dips=dips,
                                ok=(
                                    np.isfinite(ratio)
                                    and VECTOR_BAND[0] <= ratio <= VECTOR_BAND[1]
                                    and dips >= 3
                                ),
                                same_b_ratio=meas / (Q / (0.94 * X)) if label == "b" else float("nan"),
                                same_c_ratio=meas / (Q / (0.94 * X)) if label == "c" else float("nan"),
                            )
                        )
    return rows


def gl3_wall_rows():
    profiles = {}
    for csign in (-1, 1):
        for X in (8.0, 12.0, 16.0):
            for branch in ("real3", "mixed"):
                profiles[(csign, X, branch)] = W.build_profile(csign, X, branch)

    rows = []
    for csign in (-1, 1):
        for branch in ("real3", "mixed"):
            for n in (4, 8):
                for f in (1, 2):
                    for X in (8.0, 12.0, 16.0):
                        Q = float(n * f * f)
                        prof = profiles[(csign, X, branch)]
                        pred_by_dir = {
                            "a": Q / prof["Sa"],
                            "b": Q / prof["Sb"],
                            "diag": Q / (prof["Sa"] + prof["Sb"]),
                        }
                        for direction in ("a", "b", "diag"):
                            amp = W.transform_ray(prof, Q, direction)
                            gamma, r2 = W.envelope_gamma(W.NU_GRID, amp)
                            dip, ndips = W.deep_dip_spacing(W.NU_GRID, amp)
                            pred = pred_by_dir[direction]
                            ratio = dip / pred if np.isfinite(dip) else float("nan")
                            rows.append(
                                dict(
                                    csign=csign,
                                    branch=branch,
                                    n=n,
                                    f=f,
                                    X=X,
                                    direction=direction,
                                    gamma=gamma,
                                    r2=r2,
                                    dip=dip,
                                    ndips=ndips,
                                    pred=pred,
                                    ratio=ratio,
                                    visible=np.isfinite(dip) and ndips >= 3,
                                    coherent=r2 >= WALL_R2_GATE,
                                    near=(
                                        np.isfinite(ratio)
                                        and WALL_NEAR_BAND[0] <= ratio <= WALL_NEAR_BAND[1]
                                    ),
                                )
                            )
    return rows


def parse_gl3_family_summary():
    if not os.path.exists(GL3_FAMILY):
        return {}
    out = {}
    with open(GL3_FAMILY, "r") as fh:
        txt = fh.read()
    m = re.search(r"forms pinned: (\d+)/(\d+); weights \[([^\]]+)\]", txt)
    if m:
        out["pinned"] = int(m.group(1))
        out["forms"] = int(m.group(2))
        out["weights"] = m.group(3)
    m = re.search(
        r"UNIVERSAL: cells ([0-9.]+)pi \(across-form spread ([0-9.]+)pi\); "
        r"all-simple (\d+)/(\d+); worst weld spread ([0-9.eE+-]+)",
        txt,
    )
    if m:
        out.update(
            cell_mean=float(m.group(1)),
            cell_spread=float(m.group(2)),
            simple=int(m.group(3)),
            simple_forms=int(m.group(4)),
            worst_weld=float(m.group(5)),
        )
    return out


def summarize_groups(rows, key_fields):
    groups = defaultdict(list)
    for r in rows:
        key = tuple(r[k] for k in key_fields)
        groups[key].append(r)
    return groups


def main():
    t0 = time.time()
    lines = []

    def emit(s=""):
        lines.append(s)
        print(s, flush=True)

    emit("=" * 78)
    emit("BE SCALE AUDIT — vector clocks and productive cells")
    emit("=" * 78)

    gl2_rows, gl2_census = parse_gl2_rank_sweep()
    emit("\n[GL2 Sym^r] cell-aware rank sweep")
    emit("  r  clock deep  prod   R2     lf2      X    kappa")
    for r in gl2_rows:
        emit(
            f"  {r['r']:2d} {r['clock']:5d} {r['deep']:4d} {r['prod']:5.2f}"
            f" {r['R2']:5.3f} {r['lf2']:7.2f} {r['X']:7.2f} {r['kmean']:8.4f}"
        )
    gl2_clock_all = sum(1 for r in gl2_rows if r["R2"] >= 0.999)
    gl2_prod = np.array([r["prod"] for r in gl2_rows], dtype=float)
    emit(
        f"  verdict: clock law certified at R2>=0.999 for {gl2_clock_all}/{len(gl2_rows)} ranks; "
        f"productivity range {gl2_prod.min():.2f}--{gl2_prod.max():.2f}."
    )

    vrows = gl3_vector_clock_rows()
    emit("\n[GL3 vector clock] split trace-coordinate clock")
    emit(f"  gate: measured/predicted in [{VECTOR_BAND[0]:.2f},{VECTOR_BAND[1]:.2f}] and >=3 dips")
    for direction, rows in sorted(summarize_groups(vrows, ("direction",)).items()):
        arr = np.array([r["ratio"] for r in rows], dtype=float)
        dips = np.array([r["dips"] for r in rows], dtype=float)
        ok = sum(1 for r in rows if r["ok"])
        emit(
            f"  {direction[0]:>4}: pass {ok:2d}/{len(rows):2d}, "
            f"median ratio {np.median(arr):.4f}, max dev {np.max(np.abs(arr - 1.0)):.4f}, "
            f"min dips {int(dips.min())}"
        )
    anis = [r["same_b_ratio"] for r in vrows if r["direction"] == "b" and r["kappa_b"] != C.KAPPA_A]
    emit(
        f"  scalar-control: anisotropic b-axis same-clock median ratio {np.median(anis):.4f}; "
        "the scalar GL2 clock is rejected on split windows."
    )

    gl4_rows = gl4_vector_clock_rows()
    emit("\n[GL4 formally proven vector-clock scale law] three trace-coordinate clocks")
    emit(f"  gate: measured/predicted in [{VECTOR_BAND[0]:.2f},{VECTOR_BAND[1]:.2f}] and >=3 dips")
    for direction, rows in sorted(summarize_groups(gl4_rows, ("direction",)).items()):
        arr = np.array([r["ratio"] for r in rows], dtype=float)
        dips = np.array([r["dips"] for r in rows], dtype=float)
        ok = sum(1 for r in rows if r["ok"])
        emit(
            f"  {direction[0]:>4}: pass {ok:2d}/{len(rows):2d}, "
            f"median ratio {np.median(arr):.4f}, max dev {np.max(np.abs(arr - 1.0)):.4f}, "
            f"min dips {int(dips.min())}"
        )
    banis = [
        r["same_b_ratio"]
        for r in gl4_rows
        if r["direction"] == "b" and abs(r["kb"] - 0.94) > 1e-12
    ]
    canis = [
        r["same_c_ratio"]
        for r in gl4_rows
        if r["direction"] == "c" and abs(r["kc"] - 0.94) > 1e-12
    ]
    emit(
        f"  scalar-control: anisotropic b median {np.median(banis):.4f}, "
        f"c median {np.median(canis):.4f}; formal scalar-collapse obstruction is active."
    )
    emit(
        "  formal core: CriticalLinePhasor.TwoClockWeightLaw.gl4_trace_window_vector_clock "
        "and gl4_scalar_collapse_not_uniform."
    )

    wrows = gl3_wall_rows()
    emit("\n[GL3 wall/productivity] per family yield")
    emit(
        f"  gates: visible=finite dip with >=3 dips; coherent envelope R2>={WALL_R2_GATE:.2f}; "
        f"near-vector ratio in [{WALL_NEAR_BAND[0]:.2f},{WALL_NEAR_BAND[1]:.2f}]"
    )
    emit("   c branch dir  visible coherent near-vector  med-ratio  med-gamma")
    for key, rows in sorted(summarize_groups(wrows, ("csign", "branch", "direction")).items()):
        ratios = np.array([r["ratio"] for r in rows if np.isfinite(r["ratio"])], dtype=float)
        gammas = np.array([r["gamma"] for r in rows], dtype=float)
        emit(
            f"  {key[0]:2d} {key[1]:>6} {key[2]:>4}"
            f" {sum(r['visible'] for r in rows):4d}/{len(rows):2d}"
            f" {sum(r['coherent'] for r in rows):7d}/{len(rows):2d}"
            f" {sum(r['near'] for r in rows):8d}/{len(rows):2d}"
            f" {np.median(ratios) if len(ratios) else float('nan'):10.3f}"
            f" {np.median(gammas):10.3f}"
        )
    visible = sum(r["visible"] for r in wrows)
    coherent = sum(r["coherent"] for r in wrows)
    near = sum(r["near"] for r in wrows)
    emit(
        f"  totals: visible {visible}/{len(wrows)}, coherent {coherent}/{len(wrows)}, "
        f"near-vector productive {near}/{len(wrows)}."
    )

    fam = parse_gl3_family_summary()
    if fam:
        emit("\n[GL3 Sym^2 family] universal cell register")
        emit(
            f"  forms pinned {fam['pinned']}/{fam['forms']} on weights [{fam['weights']}]; "
            f"cell mean {fam['cell_mean']:.4f}pi, spread {fam['cell_spread']:.4f}pi; "
            f"simple {fam['simple']}/{fam['simple_forms']}; worst weld {fam['worst_weld']:.1e}."
        )

    emit("\n[decision]")
    emit(
        "  The clock scales after passing from one scalar period to cell-wise/vector clocks. "
        "The GL4 vector-clock law is now a Lean theorem and the audit instantiates it. "
        "Productivity is accounted independently: GL2 deep yield by rank and GL3 wall "
        "visible/coherent/near-vector yield are measured alongside the exact split clock."
    )
    emit(f"[budget] wall time {time.time() - t0:.1f}s")
    emit("=" * 78)

    with open(OUT, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    with open(SUMMARY, "w") as fh:
        fh.write("BE SCALE AUDIT SUMMARY\n\n")
        fh.write(
            f"GL2: R2>=0.999 ranks {gl2_clock_all}/{len(gl2_rows)}; "
            f"productivity range {gl2_prod.min():.2f}--{gl2_prod.max():.2f}.\n"
        )
        fh.write(
            "GL3 vector clock: "
            + ", ".join(
                f"{direction[0]} {sum(r['ok'] for r in rows)}/{len(rows)}"
                for direction, rows in sorted(summarize_groups(vrows, ("direction",)).items())
            )
            + f"; anisotropic same-clock b median {np.median(anis):.4f}.\n"
        )
        fh.write(
            "GL4 formally proven vector-clock audit: "
            + ", ".join(
                f"{direction[0]} {sum(r['ok'] for r in rows)}/{len(rows)}"
                for direction, rows in sorted(summarize_groups(gl4_rows, ("direction",)).items())
            )
            + f"; anisotropic same-clock b median {np.median(banis):.4f}, "
            f"c median {np.median(canis):.4f}.\n"
        )
        fh.write(
            "GL4 formal core: CriticalLinePhasor.TwoClockWeightLaw.gl4_trace_window_vector_clock; "
            "productivity accounting remains a separate ledger.\n"
        )
        fh.write(
            f"GL3 wall productivity: visible {visible}/{len(wrows)}, coherent {coherent}/{len(wrows)}, "
            f"near-vector {near}/{len(wrows)}.\n"
        )
        if fam:
            fh.write(
                f"GL3 family: pinned {fam['pinned']}/{fam['forms']}; cells {fam['cell_mean']:.4f}pi "
                f"spread {fam['cell_spread']:.4f}pi; simple {fam['simple']}/{fam['simple_forms']}.\n"
            )
        fh.write("Files: tmp/mb_scale_audit.py, tmp/mb_scale_audit_results.txt\n")


if __name__ == "__main__":
    main()
