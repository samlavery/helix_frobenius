"""Coherence margins — the empirical face of the summed-fiber HB wall.

Measures the hypothesis `hcoh` from RequestProject/SummedFiberHB.lean
(`aligned_strict_sum_HB` / `coherence_implies_conj_axis`): at every
upper-half-plane point z, does a single direction θ exist with

        ‖E_j*(z)‖ < Re(e^{iθ}·E_j(z))     for EVERY bank term j ?

Per-term two-strand kernel (primitive even Dirichlet χ mod q, ε=+1),
from tmp/strand_topology.py (self-checked there to 5.1e-12):

    E_n(s) = χ(n)[ (q/(πn²))^{s/2}·Γ(s/2, πn²/q)
                 + ε·(q/(πn²))^{(1−s)/2}·Γ((1−s)/2, πn²/q) ]

Chart / CONVENTION (fixed and stated):
    s = 1/2 + i·z.  Then:
      * real z  (Im z = 0)  = the CONJUGATION AXIS (critical line).
      * Im z > 0            = OFF-AXIS (upper half-plane in the z-chart).
    Sanity: on the axis (z real) the summed fiber Σ E_n is real up to a
    known global unimodular ray — calibrated below.

Star:  E*(z) = conj( E(conj z) )  per term.  On the axis conj z = z so
    E*(z) = conj(E(z)) and ‖E*‖ = ‖E‖ term-by-term (boundary functions);
    the margin must therefore → 0 as Im z → 0⁺.  Verified.

Geometry of the per-term arc.  Write E_n = ‖E_n‖ e^{iφ_n}, ρ_n = ‖E_n*‖/‖E_n‖.
    Re(e^{iθ} E_n) = ‖E_n‖ cos(θ + φ_n).
    Requirement Re(e^{iθ}E_n) > ‖E_n*‖ = ρ_n ‖E_n‖  ⇔  cos(θ + φ_n) > ρ_n.
    If ρ_n ≥ 1: empty (instant failure).  If ρ_n < 1: θ ∈ (−φ_n − a_n, −φ_n + a_n),
    an open arc of half-width a_n = arccos(ρ_n) centered at c_n = −φ_n.
    Per-term alignment ∃θ ⇔ ∩_n arcs ≠ ∅.

MANDATORY ground-truth also measured at every grid point:
    sum-level HB ratio  R_sum(z) = ‖(ΣE)*(z)‖ / ‖ΣE(z)‖ = ‖Σ E_n*‖/‖Σ E_n‖.
    Strict HB of the SUM ⇔ R_sum < 1.  This can hold without per-term alignment.
"""
import math
import sys

import numpy as np
import mpmath as mp

mp.mp.dps = 30

CUTOFF = 45.0  # kernel cutoff:  π n² / q ≤ CUTOFF


def legendre_chi(q):
    """Quadratic residue character mod prime q (real, primitive, even for q≡1 mod 4)."""
    qr = np.zeros(q, dtype=np.int8)
    qr[(np.arange(1, q, dtype=np.int64) ** 2) % q] = 1

    def chi(n):
        r = n % q
        if r == 0:
            return 0.0
        return 1.0 if qr[r] == 1 else -1.0
    return chi


def bank_terms(q, chi, eps=+1):
    """Return the list of n (1..nmax) with χ(n)≠0 inside the cutoff, and χ values."""
    nmax = int(math.sqrt(CUTOFF * q / math.pi)) + 1
    ns, cs = [], []
    for n in range(1, nmax + 1):
        c = chi(n)
        if c != 0.0:
            ns.append(n)
            cs.append(c)
    return np.array(ns, dtype=np.int64), np.array(cs, dtype=np.float64)


def E_n_of_z(n, c, q, z, eps=+1):
    """Single bank term E_n at chart point z  (s = 1/2 + i z).  Returns mpc."""
    s = mp.mpf("0.5") + 1j * mp.mpc(z)
    x = mp.mpf(math.pi) * (n * n) / q
    r = mp.mpf(q) / (mp.mpf(math.pi) * (n * n))
    term = (r ** (s / 2) * mp.gammainc(s / 2, x, mp.inf)
            + eps * r ** ((1 - s) / 2) * mp.gammainc((1 - s) / 2, x, mp.inf))
    return c * term


def all_E(ns, cs, q, z, eps=+1):
    """Vector of E_n(z) and E_n*(z) for the whole bank at chart point z (mpc arrays)."""
    zc = mp.mpc(z)
    zbar = mp.conj(zc)
    E = np.empty(len(ns), dtype=object)
    Estar = np.empty(len(ns), dtype=object)
    for i, (n, c) in enumerate(zip(ns, cs)):
        E[i] = E_n_of_z(int(n), float(c), q, zc, eps)
        # E*(z) = conj( E(conj z) )
        Estar[i] = mp.conj(E_n_of_z(int(n), float(c), q, zbar, eps))
    return E, Estar


def arc_intersection(centers, halfwidths):
    """Intersect open arcs (c_i - a_i, c_i + a_i) on the circle (mod 2π).

    Returns (nonempty, width, best_theta, binding_indices) where binding_indices
    are the terms whose arc boundary is active at the intersection (smallest arcs
    that pin the feasible set).  Robust O(N²) sweep: candidate θ = each arc
    endpoint; the intersection is the set where ALL arcs are satisfied.
    """
    centers = np.asarray(centers, dtype=float)
    halfwidths = np.asarray(halfwidths, dtype=float)
    N = len(centers)
    # membership test: θ in arc i  ⇔  angular distance(θ, c_i) < a_i
    def in_all(theta):
        d = np.abs(((theta - centers + math.pi) % (2 * math.pi)) - math.pi)
        return d < halfwidths  # boolean vector

    # Candidate points: midpoints between consecutive endpoints won't be needed;
    # sample densely on endpoints + a fine grid to locate a feasible interval,
    # then refine the interval width by scanning endpoints inside it.
    endpoints = np.concatenate([centers - halfwidths, centers + halfwidths])
    endpoints = np.mod(endpoints, 2 * math.pi)
    # test slightly inside each endpoint pair midpoint; also test arc centers.
    cand = np.concatenate([centers, endpoints,
                           (endpoints[:, None] + 1e-9).ravel()])
    cand = np.mod(cand, 2 * math.pi)
    # Also add a coarse grid so we don't miss a wide feasible band.
    cand = np.concatenate([cand, np.linspace(0, 2 * math.pi, 720, endpoint=False)])

    best_theta = None
    for th in cand:
        if np.all(in_all(th)):
            best_theta = th
            break
    if best_theta is None:
        # find how badly it fails: the term with the largest min-distance deficit
        return False, 0.0, None, None

    # Refine: grow an interval around best_theta while ALL arcs still hold.
    # The feasible set is an intersection of arcs = a single arc (convex on circle)
    # when nonempty and total width < 2π.  Find its two boundaries.
    def feasible(theta):
        return np.all(in_all(theta))

    # binary search boundaries
    def boundary(direction):
        lo, hi = 0.0, 2 * math.pi
        # walk out until infeasible
        step = 1e-3
        edge = 0.0
        t = 0.0
        while t < 2 * math.pi:
            if not feasible(best_theta + direction * (t + step)):
                lo, hi = t, t + step
                break
            t += step
        else:
            return 2 * math.pi  # whole circle feasible (shouldn't happen with finite arcs)
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if feasible(best_theta + direction * mid):
                lo = mid
            else:
                hi = mid
        return lo

    right = boundary(+1.0)
    left = boundary(-1.0)
    width = left + right
    theta_center = best_theta + 0.5 * (right - left)

    # binding terms = arcs whose boundary is (near) the feasible-set boundary.
    # An arc i binds on the right if c_i + a_i ≈ best_theta + right.
    def wrap(a):
        return ((a + math.pi) % (2 * math.pi)) - math.pi
    theta_right = best_theta + right
    theta_left = best_theta - left
    bind = []
    tol = 5e-3
    for i in range(N):
        r_edge = centers[i] + halfwidths[i]
        l_edge = centers[i] - halfwidths[i]
        if abs(wrap(r_edge - theta_right)) < tol or abs(wrap(l_edge - theta_left)) < tol:
            bind.append(i)
    return True, width, theta_center, bind


def margin_at_theta(E, Estar, theta):
    """min_j [ Re(e^{iθ} E_j) − ‖E_j*‖ ] / ‖E_j‖   (normalized per-term margin).

    >0 everywhere ⇔ θ aligns the whole bank strictly.  Returns (min_norm_margin,
    min_abs_margin, argmin index)."""
    eit = mp.e ** (1j * mp.mpc(theta))
    best_norm = None
    best_abs = None
    idx = -1
    for j in range(len(E)):
        En = E[j]
        rhs = mp.re(eit * En)          # Re(e^{iθ} E_j)
        lhs = abs(Estar[j])            # ‖E_j*‖
        normEn = abs(En)
        m_abs = float(rhs - lhs)
        m_norm = m_abs / float(normEn) if normEn > 0 else float('inf')
        if best_norm is None or m_norm < best_norm:
            best_norm = m_norm
            best_abs = m_abs
            idx = j
    return best_norm, best_abs, idx


def analyze_point(ns, cs, q, z, eps=+1):
    """Full per-z analysis. Returns a dict of measurements."""
    E, Estar = all_E(ns, cs, q, z, eps)
    normE = np.array([float(abs(e)) for e in E])
    normEs = np.array([float(abs(e)) for e in Estar])
    phi = np.array([float(mp.arg(e)) for e in E])
    ratio = np.where(normE > 0, normEs / normE, np.inf)

    # per-term arcs
    any_empty = np.any(ratio >= 1.0)
    if any_empty:
        arc_ok, width, theta_c, bind = False, 0.0, None, None
        # but still compute best-θ margin via the arc centers to report the deficit
        # choose θ maximizing min margin numerically (grid)
        theta_c = None
    else:
        halfwidths = np.arccos(np.clip(ratio, -1.0, 1.0))
        centers = -phi  # arc centered at −arg E_n
        arc_ok, width, theta_c, bind = arc_intersection(centers, halfwidths)

    # margin at the arc-intersection center (if it exists); else grid-optimal θ
    if theta_c is not None:
        m_norm, m_abs, jidx = margin_at_theta(E, Estar, theta_c)
        theta_used = theta_c
    else:
        # grid search for the θ giving the largest min-margin (to report how negative)
        best = None
        for th in np.linspace(0, 2 * math.pi, 360, endpoint=False):
            mn, ma, ji = margin_at_theta(E, Estar, th)
            if best is None or mn > best[0]:
                best = (mn, ma, ji, th)
        m_norm, m_abs, jidx, theta_used = best

    # sum-level HB ratio (GROUND TRUTH)
    Sum = mp.mpc(0)
    SumStar = mp.mpc(0)
    for j in range(len(E)):
        Sum += E[j]
        SumStar += Estar[j]
    R_sum = float(abs(SumStar) / abs(Sum)) if abs(Sum) > 0 else float('inf')

    return {
        'z': z,
        'arc_ok': arc_ok,
        'arc_width': width if arc_ok else 0.0,
        'theta': theta_used,
        'min_margin_norm': m_norm,
        'min_margin_abs': m_abs,
        'binding_idx': bind,
        'binding_term_n': [int(ns[i]) for i in bind] if (arc_ok and bind) else None,
        'ratio': ratio,
        'normE': normE,
        'normEs': normEs,
        'phi': phi,
        'R_sum': R_sum,
        'sum_abs': float(abs(Sum)),
        'binding_argmin_n': int(ns[jidx]) if jidx >= 0 else None,
        'any_ratio_ge_1': bool(any_empty),
        'max_ratio': float(np.max(ratio)),
    }


def calibrate(ns, cs, q, eps=+1):
    """On the axis (z real): Σ E_n should be real up to a known unimodular ray.
    Report the imaginary/real ratio and the per-term ‖E*‖=‖E‖ identity."""
    lines = []
    for zr in (0.0, 0.37, 1.0, 5.0):
        E, Estar = all_E(ns, cs, q, complex(zr, 0.0), eps)
        Sum = sum(E[j] for j in range(len(E)))
        # per-term star identity on axis
        maxdev = max(abs(float(abs(Estar[j])) - float(abs(E[j])))
                     for j in range(len(E)))
        ray = float(mp.arg(Sum)) if abs(Sum) > 0 else 0.0
        lines.append(f"    z={zr:>5.2f}:  |Σ|={float(abs(Sum)):.6e}  "
                     f"arg(Σ)={ray:+.6e} rad  "
                     f"max_j|‖E*‖−‖E‖|={maxdev:.2e}")
    return lines


# Zeros of Λ(1/2+iz, χ_q) on the conjugation axis (z real), computed from the bank
# itself (sign changes of Re Λ).  γ₁(χ_5)=6.6485 etc.  Used for near-zero x markers.
KNOWN_ZERO_ORDINATES = {
    5: [6.6485, 9.8314, 11.9588],
    13: [3.1193, 7.2316, 8.6254, 10.3364],
    17: [3.7281, 5.6356, 7.2828, 10.6173],
}


def run_for_q(q, out, eps=+1):
    chi = legendre_chi(q)
    ns, cs = bank_terms(q, chi, eps)
    header = f"\n{'='*78}\nq = {q}  (Legendre character, ε=+{eps})  bank size = {len(ns)} terms " \
             f"(n_max={ns[-1]})\n{'='*78}"
    print(header); out.append(header)

    cal = calibrate(ns, cs, q, eps)
    out.append("  CALIBRATION (axis, z real): Σ E_n real up to global ray; per-term ‖E*‖=‖E‖:")
    print("  CALIBRATION (axis, z real):")
    for ln in cal:
        print(ln); out.append(ln)

    ys = [0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0]
    zeros = KNOWN_ZERO_ORDINATES.get(q, [6.0, 9.0])
    # x samples: near known zeros' real parts (= their ordinate t, since s=1/2+iz means
    # z real part IS the height t) and far from them.
    xs_near = zeros
    xs_far = [0.0, 2.0, 15.0, 25.0]
    xs = sorted(set([round(x, 4) for x in xs_near + xs_far]))

    out.append(f"\n  GRID: y=Im z ∈ {ys};  x=Re z ∈ {xs}  (near-zero x: {xs_near})")
    print(f"\n  GRID over y×x  (near-zero x: {xs_near})")

    # main table
    tbl_head = (f"\n  {'y':>6} {'x':>7} | {'arc?':>5} {'arcW':>7} "
                f"{'minMargN':>10} {'bindN':>7} | {'R_sum':>9} {'HB?':>4} "
                f"{'maxRatio':>9} {'|Σ|':>10}")
    print(tbl_head); out.append(tbl_head)
    print("  " + "-" * 92); out.append("  " + "-" * 92)

    results = []
    for y in ys:
        for x in xs:
            z = complex(x, y)
            r = analyze_point(ns, cs, q, z, eps)
            results.append(r)
            near = "*" if any(abs(x - zz) < 0.6 for zz in zeros) else " "
            bindn = r['binding_argmin_n']
            row = (f"  {y:>6.2f} {x:>7.3f}{near}| "
                   f"{'Y' if r['arc_ok'] else 'N':>4} "
                   f"{r['arc_width']:>7.3f} "
                   f"{r['min_margin_norm']:>10.3e} "
                   f"{str(bindn):>7} | "
                   f"{r['R_sum']:>9.5f} "
                   f"{'Y' if r['R_sum'] < 1.0 else 'N':>4} "
                   f"{r['max_ratio']:>9.4f} "
                   f"{r['sum_abs']:>10.3e}")
            print(row); out.append(row)
    return ns, cs, results


def margin_profile(ns, cs, q, out, eps=+1):
    """Margin & R_sum vs y at a fixed representative x (near a zero and far)."""
    zeros = KNOWN_ZERO_ORDINATES.get(q, [6.0])
    out.append(f"\n  MARGIN PROFILE vs y  (q={q}):")
    print(f"\n  MARGIN PROFILE vs y (q={q}):")
    for x, label in [(zeros[0], f"near zero t≈{zeros[0]}"), (0.0, "axis-center x=0"),
                     (25.0, "far x=25")]:
        out.append(f"    x = {x}  ({label}):")
        print(f"    x = {x}  ({label}):")
        line = f"      {'y':>7} {'minMargNorm':>13} {'arcWidth':>10} {'R_sum':>10} {'1-R_sum':>11}"
        print(line); out.append(line)
        for y in [0.001, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0]:
            r = analyze_point(ns, cs, q, complex(x, y), eps)
            l = (f"      {y:>7.3f} {r['min_margin_norm']:>13.4e} "
                 f"{r['arc_width']:>10.4f} {r['R_sum']:>10.6f} {1-r['R_sum']:>11.4e}")
            print(l); out.append(l)


def ratio_structure(ns, cs, q, out, eps=+1):
    """Per-term ratio ‖E_n*‖/‖E_n‖ vs n at several y — which terms dominate the constraint."""
    out.append(f"\n  PER-TERM RATIO STRUCTURE ‖E_n*‖/‖E_n‖ vs n  (q={q}), at x=0:")
    print(f"\n  PER-TERM RATIO STRUCTURE (q={q}) at x=0:")
    ys = [0.01, 0.1, 0.5, 1.0, 2.0]
    hdr = "      n  " + "".join(f"  y={y:<6.2f}" for y in ys) + "   χ(n)"
    print(hdr); out.append(hdr)
    Rs = {}
    for y in ys:
        _, Estar = None, None
        E, Estar = all_E(ns, cs, q, complex(0.0, y), eps)
        normE = np.array([float(abs(e)) for e in E])
        normEs = np.array([float(abs(e)) for e in Estar])
        Rs[y] = np.where(normE > 0, normEs / normE, np.inf)
    show_idx = list(range(min(12, len(ns))))
    for i in show_idx:
        row = f"      {int(ns[i]):>3}  " + "".join(f"  {Rs[y][i]:>8.5f}" for y in ys) \
              + f"   {int(cs[i]):+d}"
        print(row); out.append(row)
    # which term is the max ratio (binding) at each y
    out.append("      binding (max-ratio) term n at each y:")
    print("      binding (max-ratio) term n at each y:")
    for y in ys:
        imax = int(np.argmax(Rs[y]))
        l = f"        y={y:<5.2f}: n={int(ns[imax])}  ratio={Rs[y][imax]:.5f}  (small n? {'yes' if ns[imax]<=3 else 'no'})"
        print(l); out.append(l)


# ============================================================================
# PART II — strand-asymmetric re-weld  E = A - iB
# ============================================================================

def _s_of(z):
    return mp.mpf("0.5") + 1j * mp.mpc(z)


def _S1(n, q, z):
    """First strand S1_n(s) = (q/πn²)^{s/2} Γ(s/2, x)  at chart point z."""
    s = _s_of(z)
    x = mp.mpf(math.pi) * (n * n) / q
    r = mp.mpf(q) / (mp.mpf(math.pi) * (n * n))
    return r ** (s / 2) * mp.gammainc(s / 2, x, mp.inf)


def _S2(n, q, z):
    """Second strand S2_n(s) = (q/πn²)^{(1-s)/2} Γ((1-s)/2, x)  at chart point z."""
    s = _s_of(z)
    x = mp.mpf(math.pi) * (n * n) / q
    r = mp.mpf(q) / (mp.mpf(math.pi) * (n * n))
    return r ** ((1 - s) / 2) * mp.gammainc((1 - s) / 2, x, mp.inf)


def reweld_E(ns, cs, q, z):
    """E(z) = 2·Σ χ(n)·S2_n(z)  and  E*(z) = 2·Σ χ(n)·S1_n(z).

    Also returns the two summed strands (for dominance analysis) and Λ = Σχ·(S1+S2).
    """
    sumS1 = mp.mpc(0)
    sumS2 = mp.mpc(0)
    for i in range(len(ns)):
        n = int(ns[i]); c = float(cs[i])
        sumS1 += c * _S1(n, q, z)
        sumS2 += c * _S2(n, q, z)
    E = 2 * sumS2
    Estar = 2 * sumS1
    Lam = sumS1 + sumS2
    return E, Estar, sumS1, sumS2, Lam


def reweld_point(ns, cs, q, z):
    """HB analysis of the re-welded structure function E at chart point z."""
    E, Estar, sumS1, sumS2, Lam = reweld_E(ns, cs, q, z)
    normE = float(abs(E))
    normEs = float(abs(Estar))
    hb_ratio = normEs / normE if normE > 0 else float('inf')
    Acomp = (E + Estar) / 2
    Bcomp = 1j * (E - Estar) / 2
    return {
        'z': z,
        'hb_ratio': hb_ratio,            # ‖E*‖/‖E‖ ; strict HB ⟺ < 1 for Im z>0
        'margin': 1.0 - hb_ratio,        # HB margin
        'normE': normE, 'normEs': normEs,
        'Acomp_minus_Lam': float(abs(Acomp - Lam)),   # should be 0
        'Bcomp_abs': float(abs(Bcomp)),               # should be >0 off-axis
        'Lam_abs': float(abs(Lam)),
        'Lam_im': float(mp.im(Lam)),                  # 0 on axis
        'sumS1': float(abs(sumS1)), 'sumS2': float(abs(sumS2)),
    }


def run_reweld_for_q(q, out, eps=+1):
    chi = legendre_chi(q)
    ns, cs = bank_terms(q, chi, eps)
    header = f"\n{'='*78}\nPART II  q = {q}  bank = {len(ns)} terms (n_max={ns[-1]})\n{'='*78}"
    print(header); out.append(header)

    # (1) algebra + axis-consistency checks
    out.append("  ALGEBRA CHECK (E=2Σχ S2, E*=2Σχ S1, Acomp=Λ, Bcomp≠0 off-axis):")
    print("  ALGEBRA CHECK:")
    for z in [complex(3.0, 0.7), complex(0.0, 1.2)]:
        r = reweld_point(ns, cs, q, z)
        l = (f"    z={z}: |Acomp-Λ|={r['Acomp_minus_Lam']:.1e}  |Bcomp|={r['Bcomp_abs']:.4e}  "
             f"HBratio={r['hb_ratio']:.6f}")
        print(l); out.append(l)
    # axis consistency: on axis E*=? ; Λ real; A-zeros preserved
    out.append("  AXIS CHECK (z real): Λ real (Im→0), and |E|=|E*| boundary at y=0:")
    print("  AXIS CHECK (z real):")
    for zr in (0.0, 3.0, 6.648):
        r = reweld_point(ns, cs, q, complex(zr, 0.0))
        l = (f"    z={zr:>6.3f}: Λ_im={r['Lam_im']:+.1e}  |Λ|={r['Lam_abs']:.4e}  "
             f"HBratio(y=0)={r['hb_ratio']:.6f}  (→1 on axis)")
        print(l); out.append(l)

    # (1b) locate γ₁ from the A-part to confirm zeros preserved
    zeros = KNOWN_ZERO_ORDINATES.get(q, [6.0])
    z0 = zeros[0]
    lo, hi = z0 - 0.5, z0 + 0.5
    def Are(zr):
        _, _, _, _, Lam = reweld_E(ns, cs, q, complex(zr, 0.0))
        return float(mp.re(Lam))
    a, b = lo, hi
    fa = Are(a)
    root = None
    N = 200
    prev_x, prev_f = a, fa
    for k in range(1, N + 1):
        x = lo + (hi - lo) * k / N
        f = Are(x)
        if prev_f * f < 0:
            aa, bb = prev_x, x
            for _ in range(60):
                mm = 0.5 * (aa + bb)
                if Are(aa) * Are(mm) <= 0:
                    bb = mm
                else:
                    aa = mm
            root = 0.5 * (aa + bb)
            break
        prev_x, prev_f = x, f
    l = f"  A-PART ZERO (γ₁): located at z={root:.5f}  (LMFDB γ₁≈{z0})" if root else \
        f"  A-PART ZERO: no sign change in [{lo},{hi}] (check window)"
    print(l); out.append(l)

    # (2) HB ratio over the grid
    ys = [0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0]
    xs = sorted(set([round(x, 4) for x in zeros + [0.0, 2.0, 15.0, 25.0]]))
    out.append(f"\n  HB RATIO ‖E*‖/‖E‖ over grid  (strict HB ⟺ <1; margin=1−ratio):")
    print(f"\n  HB RATIO GRID:")
    th = f"    {'y':>6} {'x':>7} | {'HBratio':>9} {'margin':>9} {'HB?':>4} | {'|E|':>10} {'||S1|-|S2||':>12}"
    print(th); out.append(th)
    print("    " + "-" * 70); out.append("    " + "-" * 70)
    worst = (1.0, None)   # (min margin, z) — the closest approach to the wall
    for y in ys:
        for x in xs:
            r = reweld_point(ns, cs, q, complex(x, y))
            near = "*" if any(abs(x - zz) < 0.6 for zz in zeros) else " "
            hbok = 'Y' if r['hb_ratio'] < 1.0 else 'N'
            row = (f"    {y:>6.2f} {x:>7.3f}{near}| {r['hb_ratio']:>9.6f} "
                   f"{r['margin']:>9.6f} {hbok:>4} | {r['normE']:>10.3e} "
                   f"{abs(r['sumS1']-r['sumS2']):>12.3e}")
            print(row); out.append(row)
            if r['margin'] < worst[0]:
                worst = (r['margin'], complex(x, y))
    l = f"  >>> CLOSEST APPROACH to wall: margin={worst[0]:.6f} at z={worst[1]}  " \
        f"({'STILL STRICT HB' if worst[0] > 0 else 'HB VIOLATED — OBSTRUCTION'})"
    print(l); out.append(l)

    # (2b) margin law in y at fixed x (near zero, center, far)
    out.append(f"\n  MARGIN LAW  (1−‖E*‖/‖E‖) vs y  (q={q}):")
    print(f"\n  MARGIN LAW vs y (q={q}):")
    for x, lab in [(zeros[0], f"near γ₁ (t≈{zeros[0]})"), (0.0, "center x=0"), (25.0, "far x=25")]:
        out.append(f"    x={x} ({lab}):   y | HBratio | margin | margin/y | log(margin)")
        print(f"    x={x} ({lab}):")
        pl = f"      {'y':>8} {'HBratio':>10} {'margin':>11} {'margin/y':>10} {'ratio_slope':>12}"
        print(pl); out.append(pl)
        prev = None
        for y in [0.001, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0]:
            r = reweld_point(ns, cs, q, complex(x, y))
            m = r['margin']
            # empirical local power: d log(margin)/d log(y)
            slope = ''
            if prev is not None and prev[1] > 0 and m > 0:
                slope = f"{(math.log(m) - math.log(prev[1])) / (math.log(y) - math.log(prev[0])):.3f}"
            l = (f"      {y:>8.4f} {r['hb_ratio']:>10.6f} {m:>11.6e} "
                 f"{m / y:>10.5f} {slope:>12}")
            print(l); out.append(l)
            prev = (y, m)

    # (3) per-term vs summed dominance: which terms carry ‖ΣS2‖ > ‖ΣS1‖
    out.append(f"\n  STRAND DOMINANCE decomposition at x=0 (per-term |S2_n|/|S1_n| and sums):")
    print(f"\n  STRAND DOMINANCE (q={q}) at x=0:")
    for y in [0.1, 0.5, 1.0]:
        out.append(f"    y={y}:  n : |S1_n| |S2_n| ratio(S2/S1)   (χ)")
        print(f"    y={y}:")
        s1tot = mp.mpc(0); s2tot = mp.mpc(0)
        rows = []
        for i in range(len(ns)):
            n = int(ns[i]); c = float(cs[i])
            a1 = _S1(n, q, complex(0.0, y)); a2 = _S2(n, q, complex(0.0, y))
            s1tot += c * a1; s2tot += c * a2
            rows.append((n, float(abs(a1)), float(abs(a2)), c))
        for (n, m1, m2, c) in rows[:8]:
            rr = m2 / m1 if m1 > 0 else float('inf')
            l = f"      n={n:>2}: |S1|={m1:.3e} |S2|={m2:.3e} S2/S1={rr:>8.3f}  χ={int(c):+d}"
            print(l); out.append(l)
        l = (f"      SUMMED: ‖Σχ S1‖={float(abs(s1tot)):.4e}  ‖Σχ S2‖={float(abs(s2tot)):.4e}  "
             f"dominance ‖ΣS2‖/‖ΣS1‖={float(abs(s2tot)/abs(s1tot)):.4f}")
        print(l); out.append(l)


# ============================================================================
# PART II-B — amplitude vs phase: helix strand vs its conjugate partner
# ============================================================================
#
# ONTOLOGY (owner, enforced): the HB comparison is the HELIX STRAND against its
# CONJUGATE PARTNER at the SAME point z — ‖E*(z)‖ < ‖E(z)‖, i.e.
# ‖Σχ·S1(z)‖ < ‖Σχ·S2(z)‖, where S1 = S2* (star-partners, verified per term).
# The two strands share ONE chiral winding; conjugation swaps their radius
# assignment only, never reversing the winding — which is WHY the per-term phase
# is y-even and the defect question is pure amplitude.  This is NOT a mirror /
# above-vs-below comparison.
#
# Because S1(z) = S2*(z) = conj(S2(conj z)), the conjugate-strand quantities at z
# equal the helix-strand quantities evaluated with a conjugated argument — this is
# bookkeeping WITHIN the conjugation anti-involution, not a second (mirror) point.
# So the same-point HB ratio factors EXACTLY:
#
#   ‖E*(z)‖/‖E(z)‖ = ‖Σχ·S1(z)‖/‖Σχ·S2(z)‖ = amp(z) · intf(z),
#     amp(z)  = Σ‖S1_n(z)‖ / Σ‖S2_n(z)‖   (conj-strand radius sum / helix radius sum)
#     intf(z) = I_{S1}(z) / I_{S2}(z),  I_S = ‖Σχ·S(z)‖ / Σ‖S_n(z)‖  (winding coherence)
#
# Strict HB ⟺ ratio < 1 (Im z>0).  Below we report the reciprocal D = 1/ratio =
# ‖E(z)‖/‖E*(z)‖ (helix over conjugate) so HB dominance reads D>1; amp_factor and
# intf_factor below are the reciprocals correspondingly (helix/conj), computed via
# the S1=S2* identity.  Owner's prediction: the defect is carried by AMPLITUDE
# (helix radius sum beats conjugate radius sum) with the two windings equally
# coherent (intf≈1, Δφ_n≈0) — no phase channel.

def _amp_phase_point(ns, cs, q, x, y):
    """Helix-vs-conjugate-strand decomposition of the HB comparison at the SAME
    point z=x+iy.  Uses the star-partner identity S1=S2* : the conjugate-strand
    values at z are the helix-strand S2 values with a conjugated argument (the
    'zm' evaluation below is that anti-involution bookkeeping, not a mirror point).
    D = ‖E(z)‖/‖E*(z)‖ = helix / conjugate; HB dominance ⟺ D>1.  Returns a dict."""
    zp = complex(x, y)
    zm = complex(x, -y)             # anti-involution arg for the conjugate strand S1=S2*
    per = []
    sum_helix = mp.mpc(0); sum_conj = mp.mpc(0)   # Σχ·S2(z) (helix), Σχ·S1(z) (conjugate)
    amp_helix = mp.mpf(0); amp_conj = mp.mpf(0)   # Σ‖S2_n(z)‖, Σ‖S1_n(z)‖ (radius sums)
    for i in range(len(ns)):
        n = int(ns[i]); c = float(cs[i])
        s2 = _S2(n, q, zp)                 # helix strand S2_n(z)
        s1 = _S2(n, q, zm)                 # conjugate strand S1_n(z) = S2_n*(z), via S2(conj z)
        sum_helix += c * s2; sum_conj += c * s1
        a_h = abs(s2); a_c = abs(s1)
        amp_helix += a_h; amp_conj += a_c
        # per-term winding-phase asymmetry between the two strands (predict ≈0 = y-even)
        dphi = float(mp.arg(s2) - mp.arg(s1))
        dphi = ((dphi + math.pi) % (2 * math.pi)) - math.pi   # wrap to (-π,π]
        d_n = float(a_h / a_c) - 1.0 if a_c > 0 else float('inf')  # helix radius over conj radius, −1
        per.append((n, float(a_h), float(a_c), dphi, d_n, c))
    Nh = float(abs(sum_helix)); Nc = float(abs(sum_conj))
    ampH = float(amp_helix); ampC = float(amp_conj)
    I_helix = Nh / ampH if ampH > 0 else float('inf')   # winding coherence of helix strand
    I_conj = Nc / ampC if ampC > 0 else float('inf')    # winding coherence of conjugate strand
    D = Nh / Nc if Nc > 0 else float('inf')             # ‖E(z)‖/‖E*(z)‖ ; HB dominance ⟺ >1
    amp_factor = ampH / ampC if ampC > 0 else float('inf')   # helix radius sum / conj radius sum
    intf_factor = I_helix / I_conj if I_conj > 0 else float('inf')
    return {
        'x': x, 'y': y,
        'D': D,                       # ‖E(z)‖/‖E*(z)‖ = helix/conjugate; HB ⟺ >1
        'amp_factor': amp_factor,     # Σ‖S2_n(z)‖ / Σ‖S1_n(z)‖   (amplitude channel)
        'intf_factor': intf_factor,   # I_{S2}/I_{S1}             (winding-coherence channel)
        'Iplus': I_helix, 'Iminus': I_conj,
        'max_dphi': max(abs(p[3]) for p in per),
        'per': per,
        # check factorization D = amp_factor * intf_factor
        'factor_resid': abs(D - amp_factor * intf_factor),
    }


def run_ampphase_for_q(q, out, eps=+1):
    chi = legendre_chi(q)
    ns, cs = bank_terms(q, chi, eps)
    header = (f"\n{'='*78}\nPART II-B  q = {q}  — amplitude-vs-phase decomposition of "
              f"dominance\n{'='*78}")
    print(header); out.append(header)

    zeros = KNOWN_ZERO_ORDINATES.get(q, [6.0])
    ys = [0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0]
    # x sweep: near zeros, in bulk, and INSIDE the known violation bands
    xs = sorted(set([round(v, 3) for v in
                     zeros + [0.0, 2.0, 8.5, 15.0, 25.0]]))

    # (2)+(4) grid: dominance factorization D = amp * intf, everywhere
    out.append("  DOMINANCE FACTORIZATION (same point z, helix strand S2 vs conjugate strand S1=S2*)")
    out.append("  D=‖E(z)‖/‖E*(z)‖=‖Σχ·S2(z)‖/‖Σχ·S1(z)‖ = amp_factor · intf_factor; HB dominance ⟺ D>1")
    out.append("  amp=Σ‖S2_n‖/Σ‖S1_n‖ (radius sums); intf=I_{S2}/I_{S1} (winding coherence); owner: amp>1, intf≈1")
    th = (f"    {'y':>6} {'x':>7} | {'D':>9} {'amp':>9} {'intf':>9} | "
          f"{'I_S2':>8} {'I_S1':>8} {'maxΔφ':>9} | {'HB?':>4} {'channel':>9}")
    print(header if False else th); out.append(th)
    print("    " + "-" * 92); out.append("    " + "-" * 92)
    worst = None
    fail_channel_report = []
    for y in ys:
        for x in xs:
            r = _amp_phase_point(ns, cs, q, x, y)
            near = "*" if any(abs(x - zz) < 0.6 for zz in zeros) else " "
            hb = 'Y' if r['D'] > 1.0 else 'N'
            # which channel: if D<1, is it amp<1 (defect reversal) or intf<1 (conspiracy)?
            if r['D'] >= 1.0:
                chan = 'ampHB' if r['amp_factor'] >= 1.0 else 'intfHB'
            else:
                # dominance FAILS — attribute
                chan = 'AMPfail' if r['amp_factor'] < 1.0 else 'INTFfail'
                fail_channel_report.append((x, y, r['D'], r['amp_factor'], r['intf_factor']))
            row = (f"    {y:>6.2f} {x:>7.3f}{near}| {r['D']:>9.6f} {r['amp_factor']:>9.6f} "
                   f"{r['intf_factor']:>9.6f} | {r['Iplus']:>8.5f} {r['Iminus']:>8.5f} "
                   f"{r['max_dphi']:>9.2e} | {hb:>4} {chan:>9}")
            print(row); out.append(row)
            if worst is None or r['D'] < worst[0]:
                worst = (r['D'], x, y, r['amp_factor'], r['intf_factor'])

    # verdict on the mechanism
    out.append("")
    l = (f"  >>> WORST dominance: D={worst[0]:.6f} at x={worst[1]},y={worst[2]}  "
         f"(amp={worst[3]:.5f}, intf={worst[4]:.5f})")
    print(l); out.append(l)
    if fail_channel_report:
        amp_fails = sum(1 for f in fail_channel_report if f[3] < 1.0)
        intf_fails = sum(1 for f in fail_channel_report if f[3] >= 1.0)
        l = (f"  >>> DOMINANCE FAILURES: {len(fail_channel_report)} grid pts; "
             f"{amp_fails} via AMPLITUDE (helix radius sum loses, amp<1), "
             f"{intf_fails} via WINDING-COHERENCE (helix winding decoheres, intf<1 while amp≥1)")
        print(l); out.append(l)
    else:
        l = "  >>> NO dominance failures on this x-grid (all D>1 at sampled x)"
        print(l); out.append(l)

    # (1) per-term winding-phase asymmetry between the two strands, Δφ_n vs n
    out.append(f"\n  (1) PER-TERM WINDING-PHASE ASYMMETRY  Δφ_n = arg S2_n(z) - arg S1_n(z)"
               f"  (helix vs conjugate strand, same z):")
    print(f"\n  (1) PER-TERM WINDING-PHASE ASYMMETRY (q={q}):")
    for x in [0.0, 8.5]:
        out.append(f"    x={x}:   n | y=0.1  y=0.5  y=1.0  y=2.0   (Δφ_n rad; predict ≈0 = shared winding)")
        print(f"    x={x}:")
        hdr = f"      {'n':>3} " + "".join(f"{'y='+str(y):>11}" for y in [0.1, 0.5, 1.0, 2.0])
        print(hdr); out.append(hdr)
        for i in range(min(8, len(ns))):
            n = int(ns[i])
            vals = []
            for y in [0.1, 0.5, 1.0, 2.0]:
                r = _amp_phase_point(ns, cs, q, x, y)
                dphi = next(p[3] for p in r['per'] if p[0] == n)
                vals.append(dphi)
            row = f"      {n:>3} " + "".join(f"{v:>11.2e}" for v in vals)
            print(row); out.append(row)
        # max over all n at each y
        mx = f"      max_n|Δφ|: " + "".join(
            f"{_amp_phase_point(ns,cs,q,x,y)['max_dphi']:>11.2e}" for y in [0.1, 0.5, 1.0, 2.0])
        print(mx); out.append(mx)

    # (3) per-term amplitude defect d_n = ‖S2_n(z)‖/‖S1_n(z)‖ - 1 (helix radius over conj radius)
    out.append(f"\n  (3) PER-TERM AMPLITUDE DEFECT  d_n(y) = ‖S2_n(z)‖/‖S1_n(z)‖ - 1  "
               f"(helix strand radius over conjugate strand radius, same z; x=0):")
    print(f"\n  (3) PER-TERM AMPLITUDE DEFECT (q={q}) at x=0:")
    hdr = f"      {'n':>3} " + "".join(f"{'y='+str(y):>12}" for y in [0.1, 0.5, 1.0, 2.0]) + "   sign/mono"
    print(hdr); out.append(hdr)
    for i in range(min(8, len(ns))):
        n = int(ns[i])
        vals = []
        for y in [0.1, 0.5, 1.0, 2.0]:
            r = _amp_phase_point(ns, cs, q, 0.0, y)
            dn = next(p[4] for p in r['per'] if p[0] == n)
            vals.append(dn)
        allpos = all(v > 0 for v in vals)
        row = (f"      {n:>3} " + "".join(f"{v:>12.4e}" for v in vals)
               + f"   {'all>0' if allpos else 'MIXED'}")
        print(row); out.append(row)
    # which terms carry the total defect (contribution to Σ‖S2_n‖ - Σ‖S1_n‖)
    out.append("      total-defect contribution by term (‖S2_n‖-‖S1_n‖ share, helix−conj), x=0, y=1.0:")
    print("      total-defect contribution by term (x=0,y=1.0):")
    r = _amp_phase_point(ns, cs, q, 0.0, 1.0)
    tot = sum(p[1] - p[2] for p in r['per'])
    contribs = sorted(((p[0], (p[1] - p[2]), (p[1] - p[2]) / tot if tot != 0 else 0)
                       for p in r['per']), key=lambda t: -abs(t[1]))
    for (n, absdef, share) in contribs[:6]:
        l = f"        n={n:>2}: (‖S2_n‖-‖S1_n‖)={absdef:>+.4e}  share={share:>7.1%}"
        print(l); out.append(l)


def main():
    out = []
    banner = ("COHERENCE MARGINS — empirical face of the summed-fiber HB wall\n"
              "Chart: s = 1/2 + i·z; real z = conjugation axis, Im z>0 = off-axis.\n"
              "Star: E*(z)=conj(E(conj z)). Kernel: two-strand incomplete-Γ (ε=+1).\n"
              "Question: ∃θ ∀j  ‖E_j*(z)‖ < Re(e^{iθ}E_j(z)) ?  and  R_sum=‖ΣE*‖/‖ΣE‖ < 1 ?")
    print(banner); out.append(banner)

    qs = [5, 13, 17]
    if len(sys.argv) > 1:
        qs = [int(a) for a in sys.argv[1:]]

    for q in qs:
        ns, cs, results = run_for_q(q, out)
        margin_profile(ns, cs, q, out)
        ratio_structure(ns, cs, q, out)

    # ---- PART II: strand-asymmetric re-weld E = A - iB ----
    part2_banner = ("\n\n" + "#" * 78 +
                    "\n# PART II — STRAND-ASYMMETRIC RE-WELD  E = A - iB = 2·Σχ(n)·S2_n\n" +
                    "#" * 78 +
                    "\n# ONTOLOGY (owner, enforced): S1 and S2 are STAR-PARTNERS, S1 = S2* (verified\n"
                    "# per term, diff 0.0).  Both strands share ONE chiral winding; conjugation\n"
                    "# swaps their radius assignment only (never reverses the winding).  The HB\n"
                    "# comparison is the HELIX STRAND vs its CONJUGATE PARTNER at the SAME point z:\n"
                    "#   ‖E*(z)‖ < ‖E(z)‖   i.e.   ‖Σχ·S1(z)‖ < ‖Σχ·S2(z)‖   (S1=S2* = conj strand).\n"
                    "# No mirror / reflection / above-vs-below language; 'conjugation axis' = real z.\n"
                    "# A = Λ (self-dual, = Σχ·K⁺), B = (1/i)·Σχ·K⁻ (anti-self-dual, real on axis).\n"
                    "# Collapse: E = A - iB = 2·Σχ·S2 (helix strand), E* = 2·Σχ·S1 (conjugate strand).\n"
                    "# Strict HB of E  ⟺  SUMMED STRAND DOMINANCE  ‖Σχ·S1‖ < ‖Σχ·S2‖ off-axis.\n"
                    "# THIS is the true 1D wall; per-term dominance is easy, summed can cancel.")
    print(part2_banner); out.append(part2_banner)
    for q in qs:
        run_reweld_for_q(q, out)

    # ---- PART II-B: amplitude-vs-phase decomposition of the dominance ----
    part2b_banner = ("\n\n" + "#" * 78 +
                     "\n# PART II-B — AMPLITUDE vs PHASE decomposition (helix strand vs conj strand)\n" +
                     "#" * 78 +
                     "\n# At the SAME point z, factor the HB comparison ‖E*(z)‖/‖E(z)‖ =\n"
                     "#   ‖Σχ·S1(z)‖/‖Σχ·S2(z)‖  (conjugate strand over helix strand) into\n"
                     "#     amp  = Σ‖S1_n(z)‖ / Σ‖S2_n(z)‖   (radius-sum: conj strand / helix strand)\n"
                     "#     intf = I_{S1}/I_{S2},  I_S = ‖Σχ·S(z)‖ / Σ‖S_n(z)‖  (winding coherence)\n"
                     "#   ‖E*‖/‖E‖ = amp · intf.  Strict HB ⟺ ratio < 1 (Im z>0).\n"
                     "# Owner's prediction: the defect ‖E‖>‖E*‖ is pure AMPLITUDE (amp<1) with the\n"
                     "# two strands' windings equally coherent (intf≈1, Δφ_n≈0) — no phase channel,\n"
                     "# because the shared winding never reverses under conjugation.  Where does it\n"
                     "# fail — amplitude (defect reversal) or interference (winding decoherence)?")
    print(part2b_banner); out.append(part2b_banner)
    for q in qs:
        run_ampphase_for_q(q, out)

    # write results file
    with open("tmp/coherence_margins_results.txt", "w") as f:
        f.write("\n".join(out) + "\n")
    print("\n[written] tmp/coherence_margins_results.txt")


if __name__ == "__main__":
    main()
