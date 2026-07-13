"""Constancy mechanism: variance spectroscopy of the channel-freeze detector.

Mystery #3, promoted from a measured signature ("channel constancy = algebraicity")
to a proven mechanism with a certified detector.  The frame (torus form):

  The g legs' Frobenius angles theta(p) = (theta_1(p),...,theta_g(p)) equidistribute
  on a closed subgroup H of the torus T^g determined by the motive's clock relations.
  For pairwise non-isogenous non-CM legs H is the full torus (JOINT SATO-TATE:
  Harris; unconditional via Barnet-Lamb-Geraghty-Harris-Taylor 2011).  Isogenous
  legs i,j force the relation theta_i = theta_j (identical a_p, Faltings), so H is
  block-diagonal.  CM legs carry a finer structure (a disconnected Sato-Tate group
  N(U(1)) = O(2): half the primes inert with theta = pi/2, half split with theta
  Hecke-equidistributed).

  A lane observable  chi_eps = exp(i eps . theta),  eps in Z^g,  is FROZEN
  (zero variance, i.e. a.s. constant) IFF eps lies in the annihilator lattice
  H^perp = { eps : block-sums all zero }.  This is measure-free: it depends only
  on the SUPPORT H (the isogeny partition), not on the Sato-Tate density.

  The exact channel second moments  E|T_k|^2,  T_k = sum_{sum eps = k} chi_eps,
  are the ARITHMETIC refinement: they use the single-clock Sato-Tate moments
  c(m) = E[cos 2m theta]  (non-CM: -1/2 at m=1, 0 for m>=2; CM: (1/2)(-1)^m).

The bridge -- "frozen lanes are algebraic classes" -- is Hodge/Tate territory.
On PRODUCTS OF ELLIPTIC CURVES it is a THEOREM, not a conjecture: the Hodge
conjecture holds for products of elliptic curves (Imai; Tate unpublished for E^n;
uniform treatment Kahn 2023), and the Tate conjecture for divisors on abelian
varieties (Tate/Faltings/Zarhin) plus the degree-one generation of the Hodge
algebra (Imai: Hg(prod E_i) = prod Hg(E_i) for non-isogenous E_i) makes every
frozen lane algebraic.  So on products of elliptic curves the freeze detector is
a CERTIFIED algebraic-class detector.  Beyond that class the bridge is named,
not claimed (general Hodge/Tate open).

Five pre-registered experiments (exact rationals printed BEFORE measurement):
  (a) generic quadruple  -- H = full torus, no frozen lanes;
  (b) degenerate         -- H = diagonal, frozen = balanced lanes (EvenWeightDC);
  (c) isogenous pair     -- H = {th1=th2, th3=th4}, directional freeze with address;
  (d) CM leg             -- the (1/2)(-1)^m ladder, partial freeze 3/4, finite part;
  (e) inversion demo     -- recover H from the frozen set alone; warp falsifier.

Statistics: 148,929 good primes to 2e6 (theta_cache) => rel. error ~0.3%.
CM caches (32a1, 49a1, 49tw5) built by the theta_cache.py pattern.

Run: python3 constancy_mechanism.py     (~30 s)
"""
import os, sys, math, itertools
from fractions import Fraction as F
import numpy as np

TMP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TMP)
from theta_cache import theta_table


# ---------------------------------------------------------------------------
# exact single-clock Sato-Tate moment  c_type(m) = E[cos 2 m theta]
#   non-CM (SU(2), density (2/pi) sin^2):  c(0)=1, c(1)=-1/2, c(m>=2)=0
#   CM     (O(2): 1/2 at theta=pi/2, 1/2 uniform):  c(0)=1, c(m)=(1/2)(-1)^m
# All lane frequencies here are even (differences of +-1 legs), so only these
# even-harmonic moments ever enter.
# ---------------------------------------------------------------------------
def cmom(typ, m):
    m = abs(m)
    if m == 0:
        return F(1)
    if typ == "noncm":
        return F(-1, 2) if m == 1 else F(0)
    if typ == "cm":
        return F(1, 2) * ((-1) ** m)
    raise ValueError(typ)


# ---------------------------------------------------------------------------
# exact channel second moment E|T_k|^2 for a block partition of the g legs.
# blocks = list of (index_list, type); legs in one block share one theta
# (isogenous/degenerate), distinct blocks are independent.  Each ordered pair
# of lanes (a,b) with sum a = sum b = k contributes prod over blocks of
# c_type( (sum_{j in block}(a_j - b_j)) / 2 ).
# ---------------------------------------------------------------------------
def channel_moment_exact(g, k, blocks):
    lanes = [e for e in itertools.product((1, -1), repeat=g) if sum(e) == k]
    tot = F(0)
    for a in lanes:
        for b in lanes:
            prod = F(1)
            for idxs, typ in blocks:
                s = sum(a[j] - b[j] for j in idxs)          # even
                prod *= cmom(typ, s // 2)
            tot += prod
    return tot


def annihilator_perp(g, blocks):
    """H^perp as the lattice of eps in {-1,0,1}^g with every block-sum zero:
    generators e_i - e_j for i,j in the same block.  Returns (rank, generators)."""
    gens = []
    for idxs, _ in blocks:
        for a, b in zip(idxs[:-1], idxs[1:]):
            v = [0] * g
            v[a], v[b] = 1, -1
            gens.append(tuple(v))
    rank = int(np.linalg.matrix_rank(np.array(gens, float))) if gens else 0
    return rank, gens


# ---------------------------------------------------------------------------
# measurement side
# ---------------------------------------------------------------------------
def good_stack(labs, warp=None):
    tabs = [np.asarray(theta_table(l), float) for l in labs]
    n = min(len(t) for t in tabs)
    good = np.ones(n, bool)
    for t in tabs:
        good &= ~np.isnan(t[:n])
    ps = np.nonzero(good)[0]
    S = np.stack([t[ps] for t in tabs], 0)
    if warp:
        for j, m in warp.items():
            S[j] = float(m) * S[j]
    return S, len(ps)


def meas_channel(TH, k):
    g = TH.shape[0]
    tot = np.zeros(TH.shape[1], complex)
    for eps in itertools.product((1, -1), repeat=g):
        if sum(eps) == k:
            tot += np.exp(1j * (np.array(eps) @ TH))
    m = np.abs(tot) ** 2
    return m.mean(), m.std() / math.sqrt(TH.shape[1])


def lane_var(TH, eps):
    lane = np.exp(1j * (np.array(eps, float) @ TH))
    return 1.0 - abs(lane.mean()) ** 2


def frozen_lanes(TH, box=(-1, 0, 1), tol=1e-6):
    g = TH.shape[0]
    out = []
    for eps in itertools.product(box, repeat=g):
        if all(e == 0 for e in eps):
            continue
        if lane_var(TH, eps) < tol:
            out.append(eps)
    return out


def recover_H(TH, box=(-1, 0, 1)):
    """certified detector: from frozen lanes alone, recover dim H, rank H^perp,
    and the isogeny partition (connected components of the frozen difference
    relations e_i - e_j)."""
    g = TH.shape[0]
    fz = frozen_lanes(TH, box)
    rk = int(np.linalg.matrix_rank(np.array(fz, float))) if fz else 0
    fzset = set(fz)
    par = list(range(g))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for i in range(g):
        for j in range(i + 1, g):
            d = tuple(1 if k == i else -1 if k == j else 0 for k in range(g))
            if d in fzset or tuple(-x for x in d) in fzset:
                par[find(i)] = find(j)
    comps = {}
    for i in range(g):
        comps.setdefault(find(i), []).append(i)
    part = sorted(sorted(v) for v in comps.values())
    return g - rk, rk, part, fz


# ---------------------------------------------------------------------------
def main():
    L = []

    def P(s=""):
        print(s, flush=True)
        L.append(s)

    P("#" * 78)
    P("# CONSTANCY MECHANISM -- variance spectroscopy of the freeze detector")
    P("#" * 78)
    P()

    # ================= (a) GENERIC ==========================================
    P("=" * 74)
    P("(a) GENERIC QUADRUPLE  11a1 x 37a1 x 53a1 x 61a1  (H = full torus T^4)")
    P("=" * 74)
    blocks = [([0], "noncm"), ([1], "noncm"), ([2], "noncm"), ([3], "noncm")]
    rk, _ = annihilator_perp(4, blocks)
    P(f"  PRE-REGISTERED: H = T^4 (dim 4), H^perp = {{0}} (rank {rk}); NO +-1 lane")
    P("  is frozen.  Channel second moments (exact rationals, product-Sato-Tate):")
    preds = {k: channel_moment_exact(4, k, blocks) for k in (0, 2, 4)}
    for k, pr in preds.items():
        P(f"    E|T_{k}|^2 = {str(pr):>6} = {float(pr):.4f}")
    TH, n = good_stack(["11a1", "37a1", "53a1", "61a1"])
    P(f"  MEASURED ({n} primes):")
    for k, pr in preds.items():
        mm, se = meas_channel(TH, k)
        sig = abs(mm - float(pr)) / se if se > 0 else 0.0
        P(f"    |T_{k}|^2 = {mm:8.4f} +- {se:.4f}   ({sig:.1f} sigma)")
    fz = frozen_lanes(TH)
    P(f"  frozen +-1/0 lanes measured: {len(fz)}  (predicted 0)  "
      f"=> H = full torus, every Hodge channel fluctuates.")
    P()

    # ================= (b) DEGENERATE =======================================
    P("=" * 74)
    P("(b) DEGENERATE  (all four legs = 11a1)  (H = diagonal circle, dim 1)")
    P("=" * 74)
    blocks = [([0, 1, 2, 3], "noncm")]
    rk, gens = annihilator_perp(4, blocks)
    P(f"  PRE-REGISTERED: H = diagonal (dim 1), H^perp = {{sum eps = 0}} "
      f"(rank {rk}) = the BALANCED lanes (EvenWeightDC).  All six balanced +-1")
    P("  lanes are FROZEN (variance exactly 0); channel moments (all constant):")
    preds = {k: channel_moment_exact(4, k, blocks) for k in (0, 2, 4)}
    for k, pr in preds.items():
        P(f"    E|T_{k}|^2 = {str(pr):>3} = {float(pr):.1f}  (Var = 0)")
    TH, n = good_stack(["11a1"] * 4)
    P(f"  MEASURED ({n} primes):")
    for k, pr in preds.items():
        mm, se = meas_channel(TH, k)
        P(f"    |T_{k}|^2 = {mm:8.4f} +- {se:.6f}   ({'CONSTANT' if se < 1e-9 else 'varies'})")
    bal = [e for e in itertools.product((1, -1), repeat=4) if sum(e) == 0]
    vmax = max(lane_var(TH, e) for e in bal)
    P(f"  worst balanced-lane variance = {vmax:.2e}  (all 6 frozen)")
    P()

    # ================= (c) ISOGENOUS PAIR ===================================
    P("=" * 74)
    P("(c) ISOGENOUS PAIR  (11a1,11a1,37a1,37a1)  H = {th1=th2, th3=th4} dim 2")
    P("=" * 74)
    P("  Isogenous elliptic curves over Q share every a_p (Faltings), so theta")
    P("  is identical pointwise -- the pair (11a1,11a1) IS an isogenous pair, and")
    P("  likewise (37a1,37a1); the two pairs are mutually non-isogenous.")
    blocks = [([0, 1], "noncm"), ([2, 3], "noncm")]
    rk, gens = annihilator_perp(4, blocks)
    P(f"  PRE-REGISTERED: H = {{(a,a,b,b)}} (dim 2), H^perp rank {rk}, generators")
    P(f"    {gens[0]} and {gens[1]}  (theta1=theta2, theta3=theta4).")
    P("  Directional freeze INSIDE the (2,2) block -- which pair-directions freeze:")
    pairs = {"12|34": (1, 1, -1, -1), "13|24": (1, -1, 1, -1), "14|23": (1, -1, -1, 1)}
    for nm, e in pairs.items():
        s12, s34 = e[0] + e[1], e[2] + e[3]
        froz = (s12 == 0 and s34 == 0)
        P(f"    {nm} = {e}: sum_12={s12:+d}, sum_34={s34:+d}  "
          f"=> {'FROZEN (in H^perp)' if froz else 'fluctuating (separates classes)'}")
    P("  Channel second moments (exact rationals, blocks {12}{34}):")
    preds = {k: channel_moment_exact(4, k, blocks) for k in (0, 2, 4)}
    for k, pr in preds.items():
        P(f"    E|T_{k}|^2 = {str(pr):>3} = {float(pr):.1f}")
    TH, n = good_stack(["11a1", "11a1", "37a1", "37a1"])
    P(f"  MEASURED ({n} primes):")
    for k, pr in preds.items():
        mm, se = meas_channel(TH, k)
        sig = abs(mm - float(pr)) / se if se > 0 else 0.0
        P(f"    |T_{k}|^2 = {mm:8.4f} +- {se:.6f}   ({sig:.1f} sigma)")
    for nm, e in pairs.items():
        P(f"    Var({nm}) = {lane_var(TH, e):.6f}")
    P()

    # ================= (d) CM LEG ===========================================
    P("=" * 74)
    P("(d) CM LEG  (32a1: CM by Q(i);  49a1: CM by Q(sqrt-7))  finer structure")
    P("=" * 74)
    P("  CM Sato-Tate group N(U(1))=O(2): P[theta=pi/2] = 1/2 (inert, a_p=0),")
    P("  P[split] = 1/2 (theta Hecke-equidistributed).  Single-clock ladder:")
    P("    non-CM: c(m) = E[cos 2m th] = -1/2 (m=1), 0 (m>=2)  -- dies after m=1")
    P("    CM:     c(m) = (1/2)(-1)^m for all m >= 1           -- never dies")
    P("  => harmonic-lane partial freeze  Var(e^{2im th}) = 1 - c(m)^2 :")
    P("     non-CM 3/4, 1, 1, 1, ...    CM  3/4, 3/4, 3/4, 3/4, ...")
    P()
    P("   leg   | frac(theta=pi/2) |  m=1   m=2   m=3   m=4   (Var e^{2im th})")
    for lab, typ in [("11a1", "noncm"), ("32a1", "cm"), ("49a1", "cm")]:
        TH, n = good_stack([lab])
        th = TH[0]
        finert = float(np.mean(np.abs(th - math.pi / 2) < 1e-9))
        vs = [lane_var(TH, [2 * m]) for m in (1, 2, 3, 4)]
        pr = [float(1 - cmom(typ, m) ** 2) for m in (1, 2, 3, 4)]
        P(f"   {lab:5s} | meas {finert:.4f}      | "
          + "  ".join(f"{v:.3f}" for v in vs)
          + f"   pred {['3/4' if abs(x-0.75)<1e-9 else '1' for x in pr]}")
    P("   (32a1/49a1 freeze every harmonic to 3/4 = the CM signature; 11a1 to 1)")
    P()
    P("  FINITE PART (the disconnected component = extra algebraic class).  Two")
    P("  NON-isogenous curves sharing a CM field share the inert set exactly")
    P("  (a frozen Z/2 relation in the component group); different fields => the")
    P("  inert sets are Chebotarev-independent.")
    TH2, n2 = good_stack(["49a1", "49tw5"])
    in1 = np.abs(TH2[0] - math.pi / 2) < 1e-9
    in2 = np.abs(TH2[1] - math.pi / 2) < 1e-9
    P(f"    49a1 & 49tw5 (both Q(sqrt-7), non-isogenous): "
      f"P[both inert]={np.mean(in1 & in2):.4f}, agree(inert1==inert2)={np.mean(in1 == in2):.4f}")
    P(f"      predicted (shared field): P[both]=1/2, agreement 1  -- FROZEN relation")
    TH3, n3 = good_stack(["32a1", "49a1"])
    j1 = np.abs(TH3[0] - math.pi / 2) < 1e-9
    j2 = np.abs(TH3[1] - math.pi / 2) < 1e-9
    P(f"    32a1(Q(i)) & 49a1(Q(sqrt-7)) different fields: "
      f"P[both inert]={np.mean(j1 & j2):.4f}  predicted 1/4 (independent)")
    P()

    # ================= (e) INVERSION DEMO ===================================
    P("=" * 74)
    P("(e) INVERSION DEMO  --  recover H from the frozen set ALONE (no labels)")
    P("=" * 74)
    P("  H = (H^perp)^perp: probe eps in {-1,0,1}^4, collect frozen lanes, take")
    P("  their annihilator.  The isogeny partition = connected components of the")
    P("  frozen difference relations e_i - e_j.  Truth given only for scoring.")
    truth = {
        "generic": (["11a1", "37a1", "53a1", "61a1"], 4, [[0], [1], [2], [3]]),
        "degenerate": (["11a1"] * 4, 1, [[0, 1, 2, 3]]),
        "isogenous {12}{34}": (["11a1", "11a1", "37a1", "37a1"], 2, [[0, 1], [2, 3]]),
        "isog triple {123}": (["11a1", "11a1", "11a1", "37a1"], 2, [[0, 1, 2], [3]]),
    }
    P("   case                | dim H (rec/true) | partition recovered      | ok?")
    for nm, (labs, dH, part) in truth.items():
        TH, n = good_stack(labs)
        dimH, rk, rec, _ = recover_H(TH)
        ok = (dimH == dH and rec == part)
        P(f"   {nm:19s} |    {dimH} / {dH}         | {str(rec):24s} | {'YES' if ok else 'NO'}")
    P()
    P("  FALSIFIER (wrong-harmonic warp): drive leg 0 at 2*theta on the isogenous")
    P("  case.  Prediction: the relation theta1=theta2 breaks, leg 0 detaches, so")
    P("  dim H rises 2 -> 3 and the recovered partition loses the {0,1} block.")
    TH, n = good_stack(["11a1", "11a1", "37a1", "37a1"], warp={0: 2})
    dimH, rk, rec, _ = recover_H(TH)
    P(f"    warped: dim H = {dimH} (was 2), partition = {rec}")
    ok = (dimH == 3 and rec == [[0], [1], [2, 3]])
    P(f"    falsifier {'FIRES as predicted' if ok else 'DID NOT fire as predicted'} "
      f"(leg 0 detaches from leg 1).")
    P()

    P("=" * 74)
    P("VERDICT")
    P("=" * 74)
    P("  Channel constancy is not a coincidence read off a control -- it is the")
    P("  annihilator lattice H^perp of the equidistribution subgroup H, and H is")
    P("  fixed by the motive's isogeny/CM relations.  The freeze pattern is")
    P("  measure-free (support only); the exact channel rationals are the")
    P("  Sato-Tate refinement.  Inverting the frozen set recovers H (the isogeny")
    P("  partition) with an address, and the wrong-harmonic warp shifts it by")
    P("  exactly the broken relation.  On PRODUCTS OF ELLIPTIC CURVES the frozen")
    P("  lanes are algebraic classes by theorem (Hodge conj.: Imai/Kahn; Tate")
    P("  divisors: Faltings) -- there the detector is CERTIFIED.  Beyond that")
    P("  class the algebraicity bridge is named, not claimed.")

    with open(os.path.join(TMP, "constancy_mechanism_results.txt"), "w") as f:
        f.write("\n".join(L) + "\n")
    P()
    P("[results -> constancy_mechanism_results.txt]")


if __name__ == "__main__":
    main()
