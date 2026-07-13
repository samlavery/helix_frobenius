"""Mystery #2 (Recognition), calibration rung A: the full recognition loop closed
at grade 4 for CLOCK-RELATION (Lefschetz / isogeny-type) classes, where truth is
known.  The grade-4 analogue of the grade-1 Heegner loop (heegner_recognition.py):
from carrier data alone --

    DETECT a class  ->  ALIGN (recover the relation)  ->  CONSTRUCT the cycle
                     ->  RECOGNIZE with an exact certificate,

no arm peeking at the truth labels.  Truth is used ONLY to grade the outcome at
the very end.

The object at grade 4 is the weight-4 tensor motive M = H1(E1) (x) H1(E2) (x)
H1(E3) (x) H1(E4); its (2,2) block is the homeless Hodge structure whose
algebraic classes are the Lefschetz/Tate classes coming from pairwise isogenies.
An isogeny E_i ~ E_j forces a_p(E_i) = a_p(E_j), so theta_i = theta_j EXACTLY --
a clock-lock, read as a zero-variance freeze on the carrier's angle fibers.

The three test quadruples (truth in parentheses, consulted only at grading):
  (i)   DEGENERATE control 11a1^4        (full diagonal; 6 algebraic classes;
                                          occupancy = Catalan C2 = 2)
  (ii)  MAIN EVENT {11a1,11a2}x{17a1,17a2}
                                         (two isogeny pairs: locks {1,2},{3,4};
                                          11a1~11a2 deg 5, 17a1~17a2 deg 2;
                                          class = product graph, deg 10; occ 1)
  (iii) SCRAMBLED control {11a1,37a1,53a1,61a1}
                                         (no relations; occupancy 0; a clean null
                                          must be returned at every arm)

THE LOOP, arm by arm (all measured before any truth is read):
  1 DETECTION   -- portal freeze/variance of the 3 folded (2,2) pair-directions
                   {12|34},{13|24},{14|23} (hodge_portal PT3 fold).  A direction
                   freezes iff eps.theta == 0 identically (zero-variance cert).
  2 ALIGNMENT   -- from the freeze pattern alone, recover the lock lattice (which
                   legs are clock-locked); the UNIQUE live (2,2) direction names
                   the locked partition.  Then STRENGTHEN, independently, with the
                   period side: hodge_clock_demo's Hecke/period-lattice machinery
                   must certify each recovered lock as a genuine clock phase-lock.
  3 CONSTRUCTION-- for each certified locked pair, EXHIBIT the isogeny (degree +
                   cyclic-kernel order) from the period-lattice comparison
                   j((a tau_i + b)/d) = j(E_j), ad = deg -- the machinery FINDS
                   the degree, it is not assumed.  The grade-4 class = the product
                   of the two graphs (degree = deg1 * deg2).
  4 RECOGNITION -- exact certificates: (a) the degree lands on an integer (report
                   the j-residual landing margin); (b) the predicted channel
                   profile, computed EXACTLY from the recovered relation via the
                   product-Sato-Tate rule, matches the measured portal profile;
                   (c) occupancy matches the invariant-theory count.  Grade vs
                   truth ONLY here.

Falsifiers (mandatory):
  F1 READING-SCALE (primary; warps deprecated per Sam 2026-07-13).  Fibers
     UNTOUCHED -- vary the reading harmonic grid.  The recognition certificate
     (occupancy) must land on its exact integer ONLY on the mu6 fundamental
     (reading winding w=1) and DEGRADE/OVER-SPLIT off it: mod-12 (w=2) reads a
     decoupled object -- the degenerate 2->6, the main pair 1->4, and, sharpest,
     the scrambled NULL hallucinates a class 0->1; off-lattice (w=sqrt2) goes
     transcendental (no integer landing).  Exact prediction = the c(w) =
     E[cos 2w theta] discriminator (harmonic_compat law).  The isogeny FREEZE
     itself is reading-scale INVARIANT (theta_i=theta_j is an exact zero at every
     winding) -- the genuine-algebraicity control a warp would have destroyed.
     [Deprecated-family warp column theta_1<-2 theta_1 retained for the record.]
  F2 the scrambled control must be a clean null at every arm.
  F3 a DELIBERATE false alignment (assert the {13|24} partition, i.e. claim
     11a1~17a1 & 11a2~17a2) must FAIL the construction arm: no integer isogeny
     degree exists between non-isogenous curves -- shown as a landing FAILURE
     (min j-residual stays O(1), never approaches 0).

Register: this closes recognition at grade 4 for CLOCK-RELATION classes
(Lefschetz/isogeny type -- the Tate-for-products regime).  The exotic/Weil-type
classes (invariants with NO pairwise clock relation) are a strictly different
regime and remain the open frontier; the boundary is stated precisely at the end.

Instruments: theta_cache (angle fibers), hodge_clock_demo (period machinery,
imported frozen), sha_hinge (Weierstrass invariants).  Portal fold reimplemented
minimally.  Run: python3 recognition_loop_g4.py     (~1 min, oracle-free).
"""
import os, sys, math, cmath, itertools
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from theta_cache import theta_table
import hodge_clock_demo as HC          # frozen: curve_tau, hecke_alignments, jfun, ...

# ---------------------------------------------------------------- curve data ---
AINV = {
    "11a1": (0, -1, 1, -10, -20),
    "11a2": (0, -1, 1, -7820, -263580),
    "11a3": (0, -1, 1, 0, 0),
    "17a1": (1, -1, 1, -1, -14),
    "17a2": (1, -1, 1, -6, -4),
    "37a1": (0, 0, 1, -1, 0),
    "53a1": (1, -1, 1, 0, 0),
    "61a1": (1, 0, 0, -2, 1),
}
BADLEVEL = {"11a1": 11, "11a2": 11, "11a3": 11, "17a1": 17, "17a2": 17,
            "37a1": 37, "53a1": 53, "61a1": 61}
NMAX_COMMON = 500000           # new caches are 500k; old are 2M -> use the min

# the folded (2,2) pair-directions (hodge_portal PT3), as sign vectors
FOLD = {"12|34": (1, 1, -1, -1), "13|24": (1, -1, 1, -1), "14|23": (1, -1, -1, 1)}
FROZEN_VAR = 1e-9              # zero-variance freeze certificate threshold

# the four test configurations; truth fields consulted ONLY at grading
CASES = [
    dict(cid="i",  name="DEGENERATE  11a1^4",
         legs=["11a1", "11a1", "11a1", "11a1"],
         truth=dict(groups=[[0, 1, 2, 3]], occ=2, frozen={"12|34", "13|24", "14|23"},
                    nclass=6, locks=[], degrees=[])),
    dict(cid="ii", name="MAIN  {11a1,11a2}x{17a1,17a2}",
         legs=["11a1", "11a2", "17a1", "17a2"],
         truth=dict(groups=[[0, 1], [2, 3]], occ=1, frozen={"13|24", "14|23"},
                    nclass=1, locks=[(0, 1), (2, 3)], degrees=[5, 2])),
    dict(cid="iii", name="SCRAMBLED  {11a1,37a1,53a1,61a1}",
         legs=["11a1", "37a1", "53a1", "61a1"],
         truth=dict(groups=[[0], [1], [2], [3]], occ=0, frozen=set(),
                    nclass=0, locks=[], degrees=[])),
]

CATALAN = [1, 1, 2, 5, 14, 42]


# =====================================================================  data  ===
def load_angles():
    """theta arrays for every needed curve on a common good-prime set (p<=NMAX)."""
    labs = sorted({l for c in CASES for l in c["legs"]})
    tab = {l: theta_table(l) for l in labs}
    nmax = min(NMAX_COMMON, min(len(t) for t in tab.values()) - 1)
    ps = np.arange(2, nmax + 1)
    good = np.ones(len(ps), dtype=bool)
    for l in labs:
        good &= ~np.isnan(np.asarray(tab[l][ps], dtype=float))
    ps = ps[good]
    TH = {l: np.asarray(tab[l][ps], dtype=float) for l in labs}
    return ps, TH, len(ps)


def leg_thetas(case, TH):
    return [TH[l] for l in case["legs"]]


# ==============================================================  portal fold  ===
def direction_variances(ths):
    """Variance of c_P = cos(eps_P . theta) for each folded (2,2) direction."""
    out = {}
    for name, eps in FOLD.items():
        arg = sum(e * t for e, t in zip(eps, ths))
        out[name] = float(np.cos(arg).var())
    return out


def pairwise_lock_variances(ths):
    """Var(cos(theta_i - theta_j)) for each leg pair -- the direct lock graph."""
    out = {}
    for i in range(4):
        for j in range(i + 1, 4):
            out[(i, j)] = float(np.cos(ths[i] - ths[j]).var())
    return out


def measured_profile(ths, n):
    """Measured E|T_k|^2 (k=0,2,4) and its standard error, from real fibers."""
    stack = np.stack(ths, 0)
    T = {0: 0j, 2: 0j, 4: 0j}
    for eps in itertools.product((1, -1), repeat=4):
        k = sum(eps)
        if k in T:
            T[k] = T[k] + np.exp(1j * (np.array(eps) @ stack))
    prof = {}
    for k in (0, 2, 4):
        m = np.abs(T[k]) ** 2
        prof[k] = (float(m.mean()), float(m.std() / math.sqrt(n)))
    return prof


# =========================================  exact product-Sato-Tate predictor  ===
def _clock_moment(D):
    """E[exp(i D theta)] for one Sato-Tate clock, D even: 1 (D=0), -1/2 (|D|=2), 0."""
    if D == 0:
        return 1.0
    if abs(D) == 2:
        return -0.5
    return 0.0


def predict_profile(groups):
    """EXACT E|T_k|^2 from the relation alone (legs in a group share one clock)."""
    lanes = list(itertools.product((1, -1), repeat=4))
    prof = {}
    for k in (0, 2, 4):
        Lk = [e for e in lanes if sum(e) == k]
        val = 0.0
        for e in Lk:
            for ep in Lk:
                term = 1.0
                for g in groups:
                    D = sum(e[j] for j in g) - sum(ep[j] for j in g)
                    term *= _clock_moment(D)
                val += term
        prof[k] = val
    return prof


def predict_occupancy(groups):
    """Invariant-theory occupancy = prod_g Catalan(|g|/2) (0 if any |g| odd)."""
    v = 1
    for g in groups:
        if len(g) % 2:
            return 0
        v *= CATALAN[len(g) // 2]
    return v


def predict_frozen(groups):
    """Which folded (2,2) directions freeze: eps has coeff 0 on every clock group."""
    fr = set()
    for name, eps in FOLD.items():
        if all(sum(eps[j] for j in g) == 0 for g in groups):
            fr.add(name)
    return fr


# ===================================  reading-scale (F1) exact predictor  ========
def st_moment(w):
    """E[cos(w theta)] for one Sato-Tate clock, measure (2/pi) sin^2 theta on [0,pi].
    The mu6 discriminator lives here: st_moment(2) = -1/2 (fundamental), integer w
    give rationals (decoupled objects off w=1), incommensurate w give transcendentals."""
    import mpmath as mp
    return float(mp.quad(lambda t: mp.cos(w * t) * mp.sin(t) ** 2, [0, mp.pi]) * 2 / mp.pi)


def power_moment(m, w):
    """E[(2 cos w theta)^m] via the binomial expansion in st_moment."""
    return sum(math.comb(m, j) * st_moment(w * (m - 2 * j)) for j in range(m + 1))


def occ_pred_winding(groups, w):
    """Exact occupancy read at reading winding w: prod_g E[(2 cos w theta_g)^|g|]."""
    v = 1.0
    for g in groups:
        v *= power_moment(len(g), w)
    return v


# ===================================================  period-side certificate  ===
def _divisors(n):
    return [a for a in range(1, n + 1) if n % a == 0]


def best_hecke(tau1, jex2, nmax=36):
    """Search degree-n Hecke alignments j((a tau1+b)/d)=jex2, ad=n; return the
    degrees that land (residual<1e-6), the global-min residual, and its degree."""
    hits, best_res, best_deg = [], float("inf"), None
    for n in range(1, nmax + 1):
        for a in _divisors(n):
            d = n // a
            for b in range(d):
                if math.gcd(math.gcd(a, b), d) != 1:
                    continue
                jv = HC.jfun(HC.sl2_reduce((a * tau1 + b) / d))
                res = abs(jv - jex2) / (1.0 + abs(jex2))
                if res < best_res:
                    best_res, best_deg = res, n
                if res < 1e-6:
                    hits.append(n)
    return sorted(set(hits)), best_res, best_deg


# ==========================================================================  ===
def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# RECOGNITION LOOP -- grade 4, clock-relation (Lefschetz/isogeny) classes")
    P("# detect -> align -> construct -> recognize; truth read ONLY at grading")
    P("#" * 78)
    P()
    ps, TH, n = load_angles()
    P(f"angle fibers: {n} good primes to {ps[-1]} "
      f"(portal statistics ~{100 / math.sqrt(n):.2f}%)")
    P()

    # cache the period tau's once (used by alignment/construction, oracle-free)
    tau, jerr = {}, {}
    for l in sorted({x for c in CASES for x in c["legs"]}):
        tau[l], jerr[l] = HC.curve_tau(AINV[l])
    P("period fibers (tau self-certified by exact algebraic j = c4^3/Delta):")
    for l in tau:
        P(f"  {l}: tau = {tau[l].real:+.5f}{tau[l].imag:+.5f}i   "
          f"|j-j_exact|/(1+|j|) = {jerr[l]:.1e}")
    P(f"  period certificate: {'PASS' if all(e < 1e-6 for e in jerr.values()) else 'FAIL'}")
    P()

    grades = {}
    for case in CASES:
        cid, name = case["cid"], case["name"]
        ths = leg_thetas(case, TH)
        b = [2.0 * np.cos(t) for t in ths]                 # b = a_p/sqrt(p)
        P("=" * 78)
        P(f"CASE ({cid})  {name}")
        P("=" * 78)

        # -- ARM 1: DETECTION -------------------------------------------------
        dv = direction_variances(ths)
        det_frozen = {k for k, v in dv.items() if v < FROZEN_VAR}
        det_live = {k for k in FOLD if k not in det_frozen}
        P("  [1] DETECTION  -- folded (2,2) direction variances (freeze cert):")
        for k in FOLD:
            tag = "FROZEN (zero-variance cert)" if k in det_frozen else "live"
            P(f"        {k}:  Var[cos] = {dv[k]:.3e}   {tag}")
        P(f"      => frozen directions: {sorted(det_frozen) or 'NONE'}")

        # -- ARM 2: ALIGNMENT -------------------------------------------------
        # (a) counting side: recover the lock lattice from the freeze pattern
        pv = pairwise_lock_variances(ths)
        lock_graph = sorted(k for k, v in pv.items() if v < FROZEN_VAR)
        if len(det_frozen) == 3:
            partition = [[0, 1, 2, 3]]
            align_str = "full diagonal (all legs clock-locked)"
        elif len(det_frozen) == 2:
            live = det_live.pop() if det_live else None
            # the unique LIVE direction names the locked partition
            eps = FOLD[live]
            g1 = [j for j in range(4) if eps[j] == 1]
            g2 = [j for j in range(4) if eps[j] == -1]
            partition = [g1, g2]
            align_str = (f"live direction {live} names locked pairs "
                         f"{tuple(x+1 for x in g1)},{tuple(x+1 for x in g2)}")
        else:
            partition = [[0], [1], [2], [3]]
            align_str = "no locks"
        P("  [2] ALIGNMENT")
        P(f"      (a) counting side: {align_str}")
        P(f"          pairwise lock graph (Var<{FROZEN_VAR:g}): "
          f"{[(i+1, j+1) for i, j in lock_graph] or 'none'}")
        # consistency of the two counting readings
        graph_pairs = {frozenset((i, j)) for i, j in lock_graph}
        part_pairs = {frozenset((a, b)) for g in partition
                      for a, b in itertools.combinations(g, 2)}
        cons = "consistent" if graph_pairs == part_pairs else "INCONSISTENT"
        P(f"          folded-fold vs pairwise-graph: {cons}")

        # (b) period side: certify each recovered lock as a genuine phase-lock
        recovered_pairs = [tuple(g) for g in partition if len(g) == 2]
        P("      (b) period side (independent Hecke/period-lattice certificate):")
        period_deg = {}
        if not recovered_pairs and len(det_frozen) == 3:
            # degenerate: identical curve; self-lock is trivially certified
            P("          full-diagonal self-lock: identical curve (trivial cert)")
        if not recovered_pairs and len(det_frozen) < 3:
            P("          no locks recovered -> nothing to certify (null)")
        for (i, j) in recovered_pairs:
            li, lj = case["legs"][i], case["legs"][j]
            degs, bres, bdeg = best_hecke(tau[li], HC.j_exact(AINV[lj]))
            period_deg[(i, j)] = (degs, bres, bdeg)
            ok = len(degs) > 0
            P(f"          pair ({i+1},{j+1}) {li}~{lj}: "
              f"period-lock {'CERTIFIED' if ok else 'NOT FOUND'} "
              f"(deg {degs or '-'}, j-residual {bres:.1e})")

        # -- ARM 3: CONSTRUCTION ---------------------------------------------
        P("  [3] CONSTRUCTION -- exhibit the isogeny (degree + cyclic kernel):")
        constructed = []
        for (i, j) in recovered_pairs:
            degs, bres, bdeg = period_deg[(i, j)]
            if degs:
                deg = degs[0]
                constructed.append(deg)
                P(f"          pair ({i+1},{j+1}): isogeny degree {deg} "
                  f"(cyclic kernel Z/{deg}), landing margin {bres:.1e}")
            else:
                P(f"          pair ({i+1},{j+1}): NO integer degree -> no cycle")
        if constructed:
            cls_deg = 1
            for d in constructed:
                cls_deg *= d
            P(f"          grade-4 class = product of graphs, degree "
              f"{'*'.join(map(str, constructed))} = {cls_deg}")
        elif len(det_frozen) == 3:
            cls_deg = None
            P("          degenerate: 6 diagonal algebraic classes (full (2,2) block)")
        else:
            cls_deg = None
            P("          no algebraic class constructed (null)")

        # -- ARM 4: RECOGNITION ----------------------------------------------
        P("  [4] RECOGNITION -- exact certificates:")
        # (a) occupancy: measured mixed moment vs invariant-theory prediction
        occ_meas = float((b[0] * b[1] * b[2] * b[3]).mean())
        occ_se = float((b[0] * b[1] * b[2] * b[3]).std() / math.sqrt(n))
        occ_pred = predict_occupancy(partition)
        occ_sig = abs(occ_meas - occ_pred) / occ_se if occ_se > 0 else 0.0
        P(f"        (a) occupancy: measured m4 = {occ_meas:.4f} +- {occ_se:.4f}"
          f"   predicted {occ_pred}   ({occ_sig:.1f} sigma)")
        # parity control: odd tensor must carry no invariant
        m3 = float((b[0] * b[1] * b[2]).mean())
        P(f"            parity control m3 = {m3:+.4f} (must be ~0)")
        # (b) channel profile: predicted-from-relation vs measured portal
        pred = predict_profile(partition)
        meas = measured_profile(ths, n)
        P("        (b) channel profile  E|T_k|^2  (predicted-from-relation vs measured):")
        prof_ok = True
        for k in (0, 2, 4):
            pm, se = meas[k]
            sig = abs(pm - pred[k]) / se if se > 0 else 0.0
            frz = "" if se > 0 else "  [frozen channel]"
            if se > 0 and sig > 6:
                prof_ok = False
            P(f"            |T_{k}|^2: predict {pred[k]:8.4f}   measured "
              f"{pm:8.4f} +- {se:.4f}   ({sig:.1f} sigma){frz}")
        # (c) frozen-direction profile match
        pred_frozen = predict_frozen(partition)
        frozen_match = (pred_frozen == det_frozen)
        P(f"        (c) freeze profile: predicted {sorted(pred_frozen) or 'NONE'}"
          f"  measured {sorted(det_frozen) or 'NONE'}  "
          f"{'MATCH' if frozen_match else 'MISMATCH'}")

        # ---- GRADE (truth read here for the first time) --------------------
        t = case["truth"]
        g_frozen = (det_frozen == t["frozen"])
        g_occ = (round(occ_meas) == t["occ"] and occ_sig < 6)
        g_locks = ({frozenset(p) for p in recovered_pairs}
                   == {frozenset(l) for l in t["locks"]})
        g_deg = (sorted(constructed) == sorted(t["degrees"]))
        g_prof = prof_ok and frozen_match
        allg = g_frozen and g_occ and g_locks and g_deg and g_prof
        grades[cid] = allg
        P("  ---- GRADE vs truth ---------------------------------------------")
        P(f"        detection freeze  : {'PASS' if g_frozen else 'FAIL'}  "
          f"(got {sorted(det_frozen) or 'NONE'}, truth {sorted(t['frozen']) or 'NONE'})")
        P(f"        alignment locks   : {'PASS' if g_locks else 'FAIL'}  "
          f"(got {[(i+1,j+1) for i,j in recovered_pairs] or 'none'}, "
          f"truth {[(i+1,j+1) for i,j in t['locks']] or 'none'})")
        P(f"        construction deg  : {'PASS' if g_deg else 'FAIL'}  "
          f"(got {sorted(constructed) or 'none'}, truth {sorted(t['degrees']) or 'none'})")
        P(f"        occupancy         : {'PASS' if g_occ else 'FAIL'}  "
          f"(got {occ_meas:.3f}~{round(occ_meas)}, truth {t['occ']})")
        P(f"        profile match     : {'PASS' if g_prof else 'FAIL'}")
        P(f"        LOOP ({cid})        : {'CLOSED' if allg else 'BROKEN'}")
        P()

    # =====================================================  FALSIFIERS  ========
    P("#" * 78)
    P("# FALSIFIERS")
    P("#" * 78)
    P()
    main_case = CASES[1]
    ths = leg_thetas(main_case, TH)
    GROUPS = {"i": [[0, 1, 2, 3]], "ii": [[0, 1], [2, 3]],
              "iii": [[0], [1], [2], [3]]}
    truth_occ = {"i": 2, "ii": 1, "iii": 0}

    # F1 (PRIMARY -- reading-scale).  Fibers UNTOUCHED; vary the reading winding w.
    P("  F1 (PRIMARY -- reading-scale; warps deprecated per Sam 2026-07-13).")
    P("     Fibers UNTOUCHED -- only the reading harmonic grid varies.  Occupancy")
    P("     must land on its exact integer on the mu6 fundamental (w=1) and")
    P("     over-split/degrade off it.  Exact prediction = the c(w)=E[cos 2w theta]")
    P("     Sato-Tate discriminator (measured meets predicted below):")
    windings = [("mu6 fundamental w=1", 1.0), ("mod-12 doubled  w=2", 2.0),
                ("rational grid   w=3", 3.0), ("off-lattice w=sqrt2", math.sqrt(2))]
    P("       reading grid          case  occupancy(meas / exact)   note")
    rs = {}
    for wname, w in windings:
        for case in CASES:
            cid = case["cid"]
            bw = [2.0 * np.cos(w * t) for t in leg_thetas(case, TH)]
            occw = float((bw[0] * bw[1] * bw[2] * bw[3]).mean())
            pw = occ_pred_winding(GROUPS[cid], w)
            rs[(round(w, 4), cid)] = occw
            if abs(w - 1.0) < 1e-9:
                note = ("mu6: lands on truth" if abs(occw - truth_occ[cid]) < 0.15
                        else "MU6 MISS")
            elif abs(w - 2.0) < 1e-9:
                note = ("NULL -> HALLUCINATED class" if cid == "iii"
                        else "over-split (decoupled)")
            elif abs(w - round(w)) > 1e-9:
                note = ("transcendental (no integer)"
                        if abs(occw - round(occw)) > 0.1 else "near-integer")
            else:
                note = "decoupled object"
            P(f"       {wname:20s} {cid:>4s}  {occw:8.4f} / {pw:8.4f}    {note}")
        P()
    wsq = round(math.sqrt(2), 4)
    mu6_clean = all(abs(rs[(1.0, c["cid"])] - truth_occ[c["cid"]]) < 0.15 for c in CASES)
    mod12_split = (abs(rs[(2.0, "iii")] - 1.0) < 0.2      # scrambled null hallucinates
                   and abs(rs[(2.0, "ii")] - 1.0) > 0.5)  # main pair over-splits off 1
    offlat_trans = abs(rs[(wsq, "ii")] - round(rs[(wsq, "ii")])) > 0.1
    readscale_ok = mu6_clean and mod12_split and offlat_trans
    P(f"      => mu6 fundamental clean (all cases hit their integer): "
      f"{'YES' if mu6_clean else 'NO'}")
    P(f"         mod-12 over-splits AND hallucinates a class in the null: "
      f"{'YES' if mod12_split else 'NO'}")
    P(f"         off-lattice reads transcendental (no integer landing): "
      f"{'YES' if offlat_trans else 'NO'}")
    P(f"         READING-SCALE FALSIFIER: "
      f"{'FIRES as required -- mu6 is THE lattice' if readscale_ok else 'did NOT fire'}")
    # freeze-invariance control: the isogeny lock is reading-scale INVARIANT
    P("      freeze-invariance control (MAIN case): theta_i=theta_j is an EXACT zero,")
    P("      so the frozen set is invariant under the reading winding -- a GENUINE")
    P("      lock, not a w=1 artifact (precisely what a warp would falsely destroy):")
    frz_inv = True
    for wname, w in [("w=1", 1.0), ("w=2", 2.0), ("w=sqrt2", math.sqrt(2))]:
        fset = {k for k, e in FOLD.items()
                if float(np.cos(w * sum(s * t for s, t in zip(e, ths))).var()) < FROZEN_VAR}
        if fset != {"13|24", "14|23"}:
            frz_inv = False
        P(f"        {wname:8s} frozen set = {sorted(fset)}")
    P(f"      => freeze reading-scale invariant: {'CONFIRMED' if frz_inv else 'BROKEN'}")
    P()

    # F1-legacy (DEPRECATED-FAMILY): fiber warp theta_1 <- 2 theta_1.  Record only.
    P("  F1-legacy (DEPRECATED-FAMILY -- fiber warp; retained for the record only):")
    warp = [2.0 * ths[0], ths[1], ths[2], ths[3]]
    dv0 = direction_variances(ths)
    dvw = direction_variances(warp)
    warp_broke = True
    for k in FOLD:
        pa = "  live " if k == "12|34" else "0.250 "
        P(f"        {k}:  Var before {dv0[k]:.3e}  after warp {dvw[k]:.3e}  pred {pa}")
        if k in ("13|24", "14|23") and (dvw[k] < FROZEN_VAR or abs(dvw[k] - 0.25) > 0.03):
            warp_broke = False
    P(f"      => warp breaks the freeze to Var~1/4 "
      f"({'reproduces old spec' if warp_broke else 'miss'}); superseded by the")
    P("         reading-scale probe (warps mutate the fiber; deprecated).")
    P()

    # F2: scrambled control clean null at every arm (graded above)
    P("  F2  scrambled control clean-null: "
      f"{'CONFIRMED' if grades['iii'] else 'FAILED'} "
      "(case (iii) returned no freeze, occupancy 0, no locks, no cycle)")
    P()

    # F3: deliberate FALSE alignment -- assert the {13|24} partition (11a1~17a1)
    P("  F3  deliberate false alignment on the MAIN case: assert partition {13|24}")
    P("      (claim locks {1,3},{2,4}: 11a1~17a1 and 11a2~17a2 -- both FALSE):")
    false_pairs = [(0, 2, "11a1", "17a1"), (1, 3, "11a2", "17a2")]
    f3_fail = True
    for (i, j, li, lj) in false_pairs:
        degs, bres, bdeg = best_hecke(tau[li], HC.j_exact(AINV[lj]))
        landed = len(degs) > 0
        if landed:
            f3_fail = False
        P(f"        pair ({i+1},{j+1}) {li}~{lj}: degrees {degs or '-'}, "
          f"min j-residual {bres:.3e} (best try deg {bdeg}) -> "
          f"{'construction FAILS (no integer degree)' if not landed else 'LANDED?!'}")
    # contrast: the TRUE partition lands
    dtrue, rtrue, _ = best_hecke(tau["11a1"], HC.j_exact(AINV["11a2"]))
    P(f"        contrast: TRUE pair (1,2) 11a1~11a2 lands at deg {dtrue}, "
      f"residual {rtrue:.1e}")
    P(f"      => false alignment {'REJECTED by construction (as required)' if f3_fail else 'NOT rejected -- FALSIFIER FAILED'}")
    P()

    # ==========================================================  VERDICT  =====
    P("#" * 78)
    P("# VERDICT")
    P("#" * 78)
    loops = "  ".join(f"({c})={'CLOSED' if grades[c] else 'BROKEN'}" for c in grades)
    P(f"  recognition loops: {loops}")
    all_closed = all(grades.values())
    fals_ok = readscale_ok and grades["iii"] and f3_fail
    P(f"  falsifiers: F1 reading-scale {'PASS' if readscale_ok else 'FAIL'}"
      f" (mu6-clean, off-mu6 over-splits; warp deprecated)"
      f" | F2 scrambled-null {'PASS' if grades['iii'] else 'FAIL'}"
      f" | F3 false-align-rejected {'PASS' if f3_fail else 'FAIL'}")
    P()
    if all_closed and fals_ok:
        P("  The full recognition loop CLOSES at grade 4 for CLOCK-RELATION classes.")
        P("  From carrier data alone: the isogeny-lock freeze was DETECTED, the lock")
        P("  lattice ALIGNED and independently period-certified, the isogeny degrees")
        P("  (5 and 2) CONSTRUCTED from the period lattice with machine-zero landing,")
        P("  and the class RECOGNIZED against the invariant-theory occupancy and the")
        P("  exact product-Sato-Tate channel profile.  Every falsifier fired exactly")
        P("  where required: the READING-SCALE probe (fibers untouched) landed the")
        P("  occupancy on its exact integer only on the mu6 fundamental and over-split")
        P("  off it -- the scrambled null even hallucinating a class at mod-12 -- while")
        P("  the isogeny freeze stayed reading-scale invariant (a genuine lock); the")
        P("  scrambled quadruple was a clean null at all four arms; and the deliberate")
        P("  false partition was rejected by the construction arm (no integer isogeny")
        P("  degree between non-isogenous curves).")
    else:
        P("  A loop or falsifier did not behave as required -- publish per the")
        P("  falsifiability register and investigate.")
    P()
    P("  HONEST BOUNDARY.  This closes recognition for the LEFSCHETZ/ISOGENY-TYPE")
    P("  regime only: grade-4 classes SOURCED BY PAIRWISE CLOCK RELATIONS")
    P("  (theta_i = theta_j), where the freeze is exact and the period lattice")
    P("  exhibits the correspondence.  The EXOTIC / WEIL-TYPE classes -- Hodge")
    P("  invariants carried with NO pairwise clock relation among the legs (the")
    P("  homeless (2,2) 2-plane of hodge_portal PT3, occupancy WITHOUT any frozen")
    P("  pair-direction) -- are a strictly different object: no leg-pair freezes,")
    P("  no isogeny to construct, and the recognition template here does not reach")
    P("  them.  That regime remains the open frontier.")

    with open(os.path.join(HERE, "recognition_loop_g4_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P("[results written to recognition_loop_g4_results.txt]")


if __name__ == "__main__":
    main()
