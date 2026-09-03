"""att518 — THE 3D LANE PENCIL, built (ledger 110's queued fix; HP_SKELETON Track B1).

Ledger 108 (Sam's correction): the pencil's vectors are LANE RESULTANTS -- internal
sums of rotating site-phasors -- and the focal cancellation sum_lane u R = 0 IS the
linear dependence det G(t) = 0.  The 1D scalar collapse makes a 2-lane Gram identically
rank-degenerate (scalar Cauchy-Schwarz); the AMBIENT DIMENSION is load-bearing.
Ledger 110 built the scalar-adjacent 2-lane detector (det G = 4|A_o|^2|A_e|^2 sin^2 dphi,
touch = phase-locking), found it 50x too weak, and specified "the genuine 3D lane vectors"
as the fix.  Never built until now.

THE OBJECT.  Site n of the growth fiber at head ordinate y (head height Z = e^y) is the
3D vector
    s_n(y) = w(n/Z) * a_n * ( cos th_n, sin th_n, h_n ),
    a_n = |c_n| x_n^{-1/2}  (the phasor amplitude; x_n = (pi/3) n, the carrier gauge),
    th_n = -y log x_n        (head-coupled readout angle -- focal_closure's law),
    h_n  = the site's height coordinate (three readings, below).
Lane vectors v_L = sum_{n in lane L} s_n in R^3; the Gram G = [ <v_L, v_L'> ] is PSD by
construction, so det G >= 0 with tangential touches (ledger 108 ii), and rank drop is
real-linear dependence of the lane vectors.  Contact depth (projective, gauge-free):
    kappa3(y) = det G / prod_L |v_L|^2     (for two lanes: sin^2 of the 3D angle).

THREE HEIGHT READINGS, to apply the EQUALITY TEST (ledger 272/514) before anything else:
  'const'   h_n := 1 per LANE (a common third coordinate, not summed over sites).  Then
            det G = |R_P - R_M|^2 exactly: the 1D readout squared.  RESTATEMENT control.
  'mass'    h_n := 1 per SITE: third coordinate = lane mass W_L = sum w a.  Dependence
            <=> R_P/W_P = R_M/W_M: the mass-normalized balance.
  'winding' h_n := log x_n per site: third coordinate = lane winding H_L = sum w a log x.
            Dependence <=> R_P/H_P = R_M/H_M: the height-normalized balance.
'mass' and 'winding' are the genuine 3D objects (per-site geometry summed); 'const' is
the restatement.  Whether the genuine ones touch AT the zeros, or near them with a depth
set by lane mass/height imbalance (the log-2 clock of ledger 105), is what is measured.

Read-only.  Reference ordinates are used ONLY in the validation columns.
"""

from __future__ import annotations

import math
import sys
import numpy as np

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")
from focal_closure import (FAMILIES, growth_window, PI3, REFERENCE_ORDINATES,  # noqa: E402
                           _golden, closure)


# ------------------------------------------------------------------ the object

def lane_vectors_3d(family, y: float, mode: str):
    """3D lane vectors at head ordinate y.  Returns list of (u_lane, v in R^3, R, H)."""
    Z = math.exp(y)
    N = int(Z)
    coeffs, keys = family.coeff(N)
    c = coeffs[1:N + 1]
    k = keys[1:N + 1]
    n = np.arange(1, N + 1, dtype=np.float64)
    w = growth_window(n / Z)
    x = PI3 * n
    amp = np.abs(c) * w * x ** (-0.5)
    th = -y * np.log(x)
    if mode == "winding":
        h = np.log(x)
    elif mode == "mass":
        h = np.ones_like(x)
    elif mode == "const":
        h = None
    else:
        raise ValueError(mode)
    out = []
    for lane in np.unique(k):
        sel = k == lane
        cs = c[sel]
        nz = np.abs(cs) > 0
        if not np.any(nz):
            continue
        u = complex(cs[nz][0] / abs(cs[nz][0]))
        R = complex(np.sum(amp[sel] * np.exp(1j * th[sel])))
        H = 1.0 if h is None else float(np.sum(amp[sel] * h[sel]))
        v = np.array([R.real, R.imag, H])
        out.append((u, v, R, H))
    return out


def kappa3(family, y: float, mode: str) -> float:
    """Projective contact depth of the 3D lane Gram: det G / prod |v_L|^2."""
    lanes = lane_vectors_3d(family, y, mode)
    V = np.array([v for _, v, _, _ in lanes])          # L x 3
    G = V @ V.T
    det = float(np.linalg.det(G))
    norm = float(np.prod(np.sum(V * V, axis=1)))
    return max(det, 0.0) / norm if norm > 0 else float("nan")


# ------------------------------------------------------------------ equality test

def check_const_is_restatement(family, ys):
    print("=" * 78)
    print("EQUALITY TEST  'const' reading: det G  vs  |sum_L u_L R_L|^2  (the 1D readout)")
    print("=" * 78)
    worst = 0.0
    for y in ys:
        lanes = lane_vectors_3d(family, y, "const")
        V = np.array([v for _, v, _, _ in lanes])
        det = float(np.linalg.det(V @ V.T))
        F = sum(u * R for u, _, R, _ in lanes)
        rel = abs(det - abs(F) ** 2) / max(abs(F) ** 2, 1e-300)
        worst = max(worst, rel)
        print(f"  y={y:9.5f}  det G = {det:.6e}   |F|^2 = {abs(F)**2:.6e}   rel diff {rel:.1e}")
    print(f"  -> worst relative difference {worst:.1e}  (identity expected: the 'const' 3D "
          f"pencil IS the readout squared)")
    return worst


# ------------------------------------------------------------------ anatomy

def locate_min(f, lo, hi):
    y = _golden(f, lo, hi, iters=80)
    return y, f(y)


def anatomy(family_name: str, zeros: list[float], half_width: float = 0.06):
    fam = FAMILIES[family_name]
    print()
    print("=" * 78)
    print(f"ANATOMY  {family_name}: touch location and depth per reading, at each reference zero")
    print("  offset = (argmin of the depth) - (reference ordinate);  depth = value at the argmin")
    print("=" * 78)
    print(f"{'ref zero':>10} | {'1D closure c':>14} {'offset':>9} | {'const kappa3':>13} {'offset':>9} | "
          f"{'mass kappa3':>12} {'offset':>9} | {'winding kappa3':>15} {'offset':>9}")
    rows = []
    for g in zeros:
        lo, hi = g - half_width, g + half_width
        y1, d1 = locate_min(lambda t: closure(fam, t), lo, hi)
        yc, dc = locate_min(lambda t: kappa3(fam, t, "const"), lo, hi)
        ym, dm = locate_min(lambda t: kappa3(fam, t, "mass"), lo, hi)
        yw, dw = locate_min(lambda t: kappa3(fam, t, "winding"), lo, hi)
        print(f"{g:10.5f} | {d1:14.3e} {y1-g:+9.2e} | {dc:13.3e} {yc-g:+9.2e} | "
              f"{dm:12.3e} {ym-g:+9.2e} | {dw:15.3e} {yw-g:+9.2e}")
        rows.append((g, d1, y1 - g, dc, yc - g, dm, ym - g, dw, yw - g))
    return rows


def lane_imbalance(family_name: str, y: float):
    """The lane mass/height imbalance that sets the genuine readings' floor."""
    fam = FAMILIES[family_name]
    print()
    print("=" * 78)
    print(f"LANE IMBALANCE  {family_name} at y = {y:.5f}: per-lane |R|, mass W, winding H")
    print("=" * 78)
    for mode in ("mass", "winding"):
        lanes = lane_vectors_3d(fam, y, mode)
        Hs = [H for _, _, _, H in lanes]
        Rs = [abs(R) for _, _, R, _ in lanes]
        rel = (max(Hs) - min(Hs)) / max(Hs)
        print(f"  {mode:8s}: |R| = {['%.4e' % r for r in Rs]}   third = {['%.4e' % h for h in Hs]}"
              f"   relative imbalance {rel:.3e}")
    # predicted near-touch depth from imbalance alone (two lanes): at the exact zero R_P=R_M=R,
    # kappa3 = |R|^2 (H_P - H_M)^2 / ((|R|^2 + H_P^2)(|R|^2 + H_M^2))
    lanes = lane_vectors_3d(fam, y, "winding")
    if len(lanes) == 2:
        (_, _, R1, H1), (_, _, R2, H2) = lanes
        R = 0.5 * (abs(R1) + abs(R2))
        pred = R * R * (H1 - H2) ** 2 / ((R * R + H1 * H1) * (R * R + H2 * H2))
        print(f"  predicted 'winding' floor at an exact zero from imbalance alone: {pred:.3e}")


def off_event_baseline(family_name: str, y0: float, span: float = 0.5, npts: int = 9):
    fam = FAMILIES[family_name]
    print()
    print("=" * 78)
    print(f"OFF-EVENT BASELINE  {family_name}: depths at points {span} away from y0 = {y0:.4f}")
    print("=" * 78)
    ys = [y0 + span * (0.4 + 0.6 * i / (npts - 1)) for i in range(npts)]
    for mode in ("const", "mass", "winding"):
        vals = np.array([kappa3(fam, t, mode) for t in ys])
        print(f"  {mode:8s}: median {np.median(vals):.3e}   min {vals.min():.3e}   max {vals.max():.3e}")
    vals = np.array([closure(fam, t) for t in ys])
    print(f"  1D c    : median {np.median(vals):.3e}   min {vals.min():.3e}   max {vals.max():.3e}")


def main():
    # chi3: several zeros reachable on the growth path cheaply; eta: gamma_1 only.
    chi3_zeros = [g for g in REFERENCE_ORDINATES["chi3"] if g < 15.9][:4]
    eta_zeros = [REFERENCE_ORDINATES["eta"][0]]
    print("reference ordinates used (validation only):", {"chi3": chi3_zeros, "eta": eta_zeros})

    check_const_is_restatement(FAMILIES["chi3"], [chi3_zeros[0] - 0.02, chi3_zeros[0], chi3_zeros[0] + 0.03, 10.0])

    anatomy("chi3", chi3_zeros)
    lane_imbalance("chi3", chi3_zeros[0])
    off_event_baseline("chi3", chi3_zeros[0])

    anatomy("eta", eta_zeros, half_width=0.03)
    lane_imbalance("eta", eta_zeros[0])
    off_event_baseline("eta", eta_zeros[0], span=0.2, npts=5)


if __name__ == "__main__":
    main()
