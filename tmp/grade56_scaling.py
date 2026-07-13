"""The plateau test: does the grade-4 instrument suite scale to grades 5 and 6
by COMPUTE ONLY, or does the DESIGN have to change?

House claim under test: the grade-4 machinery (hodge_portal, farside_quadruple,
wall_dissolve) is grade-agnostic.  Extending
    M_4 = H1(11a1) x H1(37a1) x H1(53a1) x H1(61a1)     (deg 16, weight 4)
to
    M_5 = M_4 x H1(79a1)                                 (deg 32, weight 5)
    M_6 = M_5 x H1(83a1)                                 (deg 64, weight 6)
should require only changing g and the curve list -- no new invention.  This
script runs grades 5 and 6 through the SAME instrument designs and logs every
place (if any) where the design, not the size, had to change.

Everything below is generated from local angles theta_j(p) (a_p = 2 sqrt(p)
cos theta_j), Sato-Tate distributed and independent across pairwise non-isogenous
curves.  The portal channel is k = sum(eps), eps in {+-1}^g; the k-channel
carries the Hodge type (p,q) with q-p = k, multiplicity h^{p,q} = C(g,p).

The exact moment law (product-Sato-Tate; per leg E[e^{i d theta}] = 1 if d=0,
-1/2 if d=+-2, 0 else):
    E|T_k|^2 = sum over lane pairs (eps,eps') with sum eps = sum eps' = k
               of prod_j f(eps_j - eps'_j)
             = C(g,m) sum_{i>=0} C(m,i) C(g-m,i) (1/4)^i,   m = (g-k)/2.
Both forms are computed and cross-checked against each other below.

Build (once, needs sage/PARI):  sage -python grade56_scaling.py build 2000000
Run  (needs numpy, mpmath):     python3 grade56_scaling.py
"""
import os, sys, math, itertools
from fractions import Fraction
from math import comb
import numpy as np

TMP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TMP)

# Weierstrass models verified via sage Cremona database (see final report):
#   79a1 [1,1,1,-2,0] cond 79 (prime), I1 Steinberg, root -1, semistable
#   83a1 [1,1,1, 1,0] cond 83 (prime), I1 Steinberg, root -1, semistable
NEW_CURVES = {"79a1": [1, 1, 1, -2, 0], "83a1": [1, 1, 1, 1, 0]}
NEW_LEVELS = {"79a1": 79, "83a1": 83}

# The full curve ladder and their conductors (grade-4 four + two new).
LADDER = ["11a1", "37a1", "53a1", "61a1", "79a1", "83a1"]
LEVELS = {"11a1": 11, "37a1": 37, "53a1": 53, "61a1": 61, "79a1": 79, "83a1": 83}


# ----------------------------------------------------------------------------
# build the two new theta caches, EXACTLY the theta_cache.py convention
# ----------------------------------------------------------------------------
def build(nmax):
    from sage.all import EllipticCurve
    sieve = np.ones(nmax + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(nmax ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    ps = np.nonzero(sieve)[0].astype(np.int64)
    for lab, ainv in NEW_CURVES.items():
        E = EllipticCurve(ainv)
        ap = np.array(E.aplist(nmax), dtype=np.float64)
        assert len(ap) == len(ps), (len(ap), len(ps))
        th = np.full(nmax + 1, np.nan)
        b = np.clip(ap / np.sqrt(ps.astype(np.float64)), -2.0, 2.0)
        th[ps] = np.arccos(b / 2.0)
        th[NEW_LEVELS[lab]] = np.nan
        path = os.path.join(TMP, f"theta_{lab}.npy")
        np.save(path, th)
        print(f"{lab}: {len(ps)} primes to {nmax} -> {path} "
              f"({th.nbytes / 1e6:.0f} MB)", flush=True)


# ----------------------------------------------------------------------------
# exact predictions (closed form + brute force, cross-checked)
# ----------------------------------------------------------------------------
def channel_moment_closed(g, k):
    """E|T_k|^2 = C(g,m) sum_i C(m,i) C(g-m,i) (1/4)^i, m=(g-k)/2, exact."""
    m = (g - k) // 2
    tot = Fraction(0)
    for i in range(0, min(m, g - m) + 1):
        tot += comb(m, i) * comb(g - m, i) * Fraction(1, 4) ** i
    return comb(g, m) * tot


def channel_moment_brute(g, k):
    """E|T_k|^2 = sum over lane pairs of (-1/2)^{#differ}, direct."""
    lanes = [e for e in itertools.product((1, -1), repeat=g) if sum(e) == k]
    tot = Fraction(0)
    for a in lanes:
        for b in lanes:
            d = sum(1 for x, y in zip(a, b) if x != y)
            tot += Fraction(-1, 2) ** d
    return tot


def channels_of(g):
    """the non-negative channels k for grade g (same parity as g)."""
    return list(range(g, -1, -2))


def lane_count(g, k):
    return comb(g, (g - k) // 2)


def predictions(g):
    """dict k -> (exact Fraction moment, degenerate |T_k|^2 = L_k^2)."""
    out = {}
    for k in channels_of(g):
        mc = channel_moment_closed(g, k)
        mb = channel_moment_brute(g, k)
        assert mc == mb, (g, k, mc, mb)          # design cross-check
        out[k] = (mc, lane_count(g, k) ** 2)
    return out


def catalan(n):
    return comb(2 * n, n) // (n + 1)


# ----------------------------------------------------------------------------
# the fibers (measurement side)
# ----------------------------------------------------------------------------
def load_thetas(labs):
    from theta_cache import theta_table
    tabs = [np.asarray(theta_table(l), dtype=float) for l in labs]
    n = min(len(t) for t in tabs)
    good = np.ones(n, dtype=bool)
    for t in tabs:
        good &= ~np.isnan(t[:n])
    ps = np.nonzero(good)[0]
    TH = [t[ps] for t in tabs]
    return TH, ps


def channels(TH, ks, doubled=None, scramble=None, rng=None):
    """T_k(p) arrays for k in ks, from g theta arrays. Vectorized over primes.
    doubled: index of a leg whose angle is doubled (wrong-harmonic falsifier).
    scramble: index of a leg whose per-prime angles are permuted (alignment
              control)."""
    g = len(TH)
    th = np.stack([np.asarray(t, dtype=float) for t in TH], axis=0)  # g x n
    if doubled is not None:
        th = th.copy(); th[doubled] *= 2.0
    if scramble is not None:
        th = th.copy(); th[scramble] = th[scramble][rng.permutation(th.shape[1])]
    T = {k: np.zeros(th.shape[1], dtype=complex) for k in ks}
    for eps in itertools.product((1, -1), repeat=g):
        s = sum(eps)
        if s in T:
            T[s] += np.exp(1j * (np.array(eps, dtype=float) @ th))
    return T


def trace_product(TH):
    """prod_j (2 cos theta_j) per prime = the full degree-2^g trace lambda_p."""
    prod = np.ones(TH[0].shape[0])
    for t in TH:
        prod *= 2.0 * np.cos(np.asarray(t, dtype=float))
    return prod


# ----------------------------------------------------------------------------
# functional-equation sheet (wall_dissolve pattern, grade-general)
# ----------------------------------------------------------------------------
def _ipow(e):
    return [1, 1j, -1, -1j][e % 4]


def fe_sheet(g, labs):
    """returns (Q_str, Gamma_str, eps, breakdown_lines)."""
    conds = [LEVELS[l] for l in labs]
    qbase = 1
    for c in conds:
        qbase *= c
    Qexp = 2 ** (g - 1)
    hodge = [comb(g, p) for p in range(g + 1)]     # (1, g, C(g,2), ...)
    # Gamma factors
    gam = []
    eps_inf = 1 + 0j
    bl = []
    half = g / 2.0
    for p in range(0, (g + 1) // 2):               # p < g/2 pairs
        shift = half - p                           # g/2 - p
        h = comb(g, p)
        # shift is integer iff g even; format nicely
        sh = int(shift) if shift == int(shift) else shift
        gam.append(f"GammaC(s+{sh})" + (f"^{h}" if h > 1 else ""))
        e = (g - 2 * p) + 1                         # (q-p)+1
        eps_inf *= _ipow(e) ** h
        bl.append(f"      (p,q)=({p},{g - p}) h={h}: (i^{e})^{h} = {_fmtc(_ipow(e) ** h)}")
    if g % 2 == 0:                                  # middle block (p=q=g/2)
        hmid = comb(g, g // 2)
        a = hmid // 2                               # F_inf split, forced a=b
        gam.append(f"GammaR(s)^{a} GammaR(s+1)^{a}")
        eps_inf *= _ipow(a)                         # i^{#minus}
        bl.append(f"      (p,q)=({g // 2},{g // 2}) h={hmid} split {a}/{a}: "
                  f"i^{a} = {_fmtc(_ipow(a))}   (#minus={a})")
    eps_fin = 1                                     # (+-1)^{2^{g-1}}, 2^{g-1} even
    eps = eps_fin * eps_inf
    Qstr = f"({'*'.join(str(c) for c in conds)})^{Qexp}"
    Gstr = "Q^(s/2) " + " ".join(gam)
    bl.insert(0, f"      eps_finite = (+-1)^{Qexp} = +1   (2^(g-1)={Qexp} even)")
    bl.append(f"      eps_infinity = {_fmtc(eps_inf)}   =>   eps = {_fmtc(eps)}")
    return Qstr, Gstr, eps, bl


def _fmtc(z):
    z = complex(z)
    if abs(z.imag) < 1e-9:
        return f"{int(round(z.real)):+d}"
    if abs(z.real) < 1e-9:
        return ("+i" if z.imag > 0 else "-i")
    return f"{z:+.0f}"


# ----------------------------------------------------------------------------
# reporting
# ----------------------------------------------------------------------------
def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# GRADE 5 / 6 SCALING -- the plateau test")
    P("#" * 78)
    P()

    # -- load all fibers once --------------------------------------------------
    TH6, ps = load_thetas(LADDER)
    n = len(ps)
    P(f"fibers: {n} good primes to {ps[-1]} (all 6 curves), "
      f"portal statistics ~{100 / math.sqrt(n):.2f}%")
    P(f"curves: {', '.join(f'{l}(N={LEVELS[l]})' for l in LADDER)}")
    P("  79a1=[1,1,1,-2,0] cond79 I1 Steinberg root-1; "
      "83a1=[1,1,1,1,0] cond83 I1 Steinberg root-1 (sage-verified)")
    P()
    TH = {4: TH6[:4], 5: TH6[:5], 6: TH6[:6]}

    def report_moments(g, TH_g, doubled=None, scramble=None, rng=None,
                       degen=False, title=""):
        ks = channels_of(g)
        src = [TH_g[0]] * g if degen else TH_g
        T = channels(src, ks, doubled=doubled, scramble=scramble, rng=rng)
        preds = predictions(g)
        P(f"  {title}")
        worst = 0.0
        for k in ks:
            mom = np.abs(T[k]) ** 2
            se = mom.std() / math.sqrt(n)
            pred = float(preds[k][1] if degen else preds[k][0])
            exact = (preds[k][1] if degen else preds[k][0])
            if se > 0:
                sig = abs(mom.mean() - pred) / se
                worst = max(worst, sig)
                tag = f"({sig:5.1f} sigma)"
            else:
                tag = "(CONSTANT -- frozen DC, zero variance)"
            P(f"    |T_{k}|^2 = {mom.mean():9.4f} +- {se:.4f}   "
              f"exact {str(exact):>9s} = {pred:9.4f}   {tag}")
        return worst

    # =====================================================================
    # (1) CALIBRATION GATE -- reproduce the published grade-4 numbers
    # =====================================================================
    P("=" * 74)
    P("(1) CALIBRATION GATE -- grade 4 must reproduce published numbers")
    P("=" * 74)
    report_moments(4, TH[4], title="grade-4 primitive channels "
                   "(exact 99/8, 7, 1):")
    report_moments(4, TH[4], degen=True,
                   title="grade-4 degenerate control (exact 36, 16, 1; zero var):")
    # degenerate DC occupancy -> Catalan 2 ; primitive -> 0 ; Schur -> 1
    tp4 = trace_product(TH[4]); tp4d = trace_product([TH[4][0]] * 4)
    P(f"    DC occupancy (mean prod 2cos): primitive {tp4.mean():+.4f} "
      f"+- {tp4.std()/math.sqrt(n):.4f} (exact 0);  degenerate "
      f"{tp4d.mean():.4f} (exact Catalan C2 = 2)")
    P(f"    Schur 2nd moment (mean (prod 2cos)^2): primitive {(tp4**2).mean():.4f} "
      f"(exact 1);  degenerate {(tp4d**2).mean():.4f} (exact C4 = 14)")
    q, gs, eps, bl = fe_sheet(4, LADDER[:4])
    P(f"    FE recipe check: eps(grade4) = {_fmtc(eps)}  (published +1)")
    P()

    # =====================================================================
    # (2) PRE-REGISTERED PREDICTIONS (exact rationals) -- printed BEFORE measuring
    # =====================================================================
    P("=" * 74)
    P("(2) PRE-REGISTERED EXACT PREDICTIONS (derived, printed before measuring)")
    P("=" * 74)
    for g in (5, 6):
        preds = predictions(g)
        P(f"  grade {g}  (degree {2**g}, weight {g}, Hodge diamond "
          f"{tuple(comb(g,p) for p in range(g+1))}):")
        for k in channels_of(g):
            mom, degen = preds[k]
            P(f"    channel k={k}  lanes={lane_count(g,k):2d}  "
              f"E|T_{k}|^2 = {str(mom):>8s} = {float(mom):9.4f}   "
              f"degenerate |T_{k}|^2 = {degen}")
        if g % 2 == 0:
            P(f"    DC occupancy: primitive 0 ; degenerate = "
              f"Catalan C{g//2} = {catalan(g//2)}")
        else:
            P(f"    DC occupancy: N/A (odd weight -- no k=0 channel; center "
              f"governed by eps, below)")
        P(f"    Schur 2nd moment: primitive 1 ; degenerate = "
          f"C{g} = {catalan(g)}")
        P()

    # =====================================================================
    # (3) MEASUREMENTS at grades 5 and 6
    # =====================================================================
    P("=" * 74)
    P("(3) MEASUREMENTS -- primitive channels, degenerate controls, occupancy")
    P("=" * 74)
    for g in (5, 6):
        P(f"  --- grade {g} ---")
        report_moments(g, TH[g],
                       title=f"grade-{g} primitive channels:")
        report_moments(g, TH[g], degen=True,
                       title=f"grade-{g} degenerate control (zero var expected):")
        tp = trace_product(TH[g]); tpd = trace_product([TH[g][0]] * g)
        if g % 2 == 0:
            P(f"    DC occupancy: primitive {tp.mean():+.4f} "
              f"+- {tp.std()/math.sqrt(n):.4f} (exact 0);  degenerate "
              f"{tpd.mean():.4f} (exact C{g//2} = {catalan(g//2)})")
        else:
            P(f"    DC occupancy: N/A (odd weight); primitive mean-prod "
              f"{tp.mean():+.4f} (drifts to 0, no DC channel to occupy)")
        P(f"    Schur 2nd moment: primitive {(tp**2).mean():.4f} (exact 1); "
          f"degenerate {(tpd**2).mean():.4f} (exact C{g} = {catalan(g)})")
        P()

    # =====================================================================
    # (4) FE SHEETS at grades 5 and 6
    # =====================================================================
    P("=" * 74)
    P("(4) FUNCTIONAL-EQUATION SHEETS")
    P("=" * 74)
    for g in (5, 6):
        q, gs, eps, bl = fe_sheet(g, LADDER[:g])
        P(f"  grade {g}:")
        P(f"    Q = {q}")
        P(f"    G(s) = {gs}")
        P(f"    Lambda(s) = eps Lambda(1-s),  eps = {_fmtc(eps)}  (provisional recipe)")
        for line in bl:
            P(line)
        if eps.real < 0:
            P("    => odd functional equation forces L(center, s=1/2) = 0 "
              "(odd-weight branch)")
        P()

    # =====================================================================
    # (5) FALSIFIERS
    # =====================================================================
    P("=" * 74)
    P("(5) FALSIFIERS")
    P("=" * 74)
    rng = np.random.default_rng(20260712)
    for g in (5, 6):
        P(f"  --- grade {g} ---")
        w = report_moments(g, TH[g], doubled=0,
                           title=f"wrong-harmonic (theta_1 <- 2 theta_1) -- "
                                 f"MUST blow predictions:")
        P(f"    => wrong-harmonic worst separation: {w:.1f} sigma "
          f"({'FIRES' if w > 10 else 'DID NOT FIRE -- investigate'})")
        # lane-scramble control: permute one leg's primes.
        #  primitive: moments are marginal-ST determined -> UNCHANGED (control passes)
        #  degenerate: constancy needs per-prime alignment -> BROKEN (frozen DC lifts)
        report_moments(g, TH[g], scramble=0, rng=rng,
                       title="lane-scramble on primitive (permute leg-1 primes) "
                             "-- control: should NOT move (marginal-ST origin):")
        wd = report_moments(g, TH[g], degen=True, scramble=1, rng=rng,
                            title="lane-scramble on degenerate (break alignment) "
                                  "-- MUST lift the frozen channels:")
        P(f"    => degenerate-alignment scramble worst lift: {wd:.1f} sigma "
          f"({'constancy is a genuine alignment signature' if wd > 10 else 'no lift?? investigate'})")
        P()

    # =====================================================================
    # (6) DESIGN-CHANGE LOG
    # =====================================================================
    P("=" * 74)
    P("(6) DESIGN-CHANGE LOG -- every point beyond {g, curve list}")
    P("=" * 74)
    P("  Instrument-by-instrument, what changed from grade 4:")
    P()
    P("  * theta_cache: same convention, two new .npy (79a1, 83a1). COMPUTE ONLY.")
    P("  * hodge_portal channels(): loop eps in {+-1}^g, k=sum(eps); the set of")
    P("    channels channels_of(g) is range(g,-1,-2). For odd g the k=0 channel")
    P("    is simply absent -- same loop, one fewer bucket. COMPUTE ONLY.")
    P("  * moment law predictions(): identical closed form, cross-checked by")
    P("    brute force at every grade. COMPUTE ONLY.")
    P("  * degenerate control / Schur / DC occupancy: identical trace-product")
    P("    moments; C_{g/2} and C_g just index higher Catalan numbers. The odd")
    P("    grade has NO DC occupancy reading -- but that is the ABSENCE of a")
    P("    measurement (odd weight has no trivial subrep), not a new method.")
    P("  * FE sheet assembly fe_sheet(): the ONE standard Hodge->Gamma recipe")
    P("    (Serre): pairs (p,q) p<q -> GammaC(s + g/2-p); middle p=q -> GammaR")
    P("    split by F_inf. HONEST NUANCE: the original grade-4 wall_dissolve.py")
    P("    HARDCODED the even-weight middle (2,2) block -- it had no odd branch,")
    P("    because grade 4 is even. Reaching grade 5 required WRITING the odd")
    P("    branch (all-GammaC, half-integer shifts, no middle). That is a real")
    P("    code addition, NOT a literal zero-diff -- but it is the odd case of")
    P("    the same standard recipe, requiring NO new mathematical idea. Grade 6")
    P("    (even) re-uses the middle-block branch verbatim (split 10/10). So:")
    P("    NEW CODE, NO NEW METHOD.")
    P("  * eps recipe: finite = +1 (2^{g-1} even, all grades); archimedean =")
    P("    product over the diamond. Same recipe. Grade 5 lands eps=-1 (odd FE,")
    P("    central zero forced); grade 6 lands eps=+1. Both are OUTPUTS of the")
    P("    unchanged recipe, flagged provisional exactly as grade 4.")
    P()
    P("  VERDICT: COMPUTE-ONLY at the level of MATHEMATICAL METHOD. Every")
    P("  instrument -- channels, moment law, degenerate/Schur/occupancy, eps --")
    P("  scaled by changing only g and the curve list. The single genuine code")
    P("  addition is the odd-weight Gamma-assembly branch (grade 5): all-GammaC,")
    P("  no middle block, which the standard Serre recipe already dictates and")
    P("  which was simply never instantiated at even grade 4. No new invention")
    P("  was needed at any grade. The plateau is not reached at grade 6.")

    with open(os.path.join(TMP, "grade56_scaling_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to grade56_scaling_results.txt]")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "build":
        build(int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000)
    else:
        main()
