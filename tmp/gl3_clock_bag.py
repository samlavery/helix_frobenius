#!/usr/bin/env python3
"""
gl3_clock_bag.py -- ratchet GL(3) wall productivity with a BAG OF CLOCKS + adapters.

Baseline (mb_scale_audit): among 144 Deng-Espinosa wall cells, only 28 are "near-vector
productive" -- their measured dip spacing matches the single vector clock Q/S within
[0.75,1.75].  But the failing cells have median ratios ~2.2, 3.7, 4.3: they are LOCKED
ONTO HARMONICS of the vector clock, not failing.  This tests whether a frozen bag of
harmonic/rational clocks + a carrier-scale adapter recovers them -- HONESTLY:

  * TIGHT tolerance (report the ratchet at TOL = 0.06, 0.10, 0.15 so it is not
    tolerance-gaming).
  * SMALL frozen bag (integer harmonics {1..6}, then small rationals p/q, q<=4).
  * PREDICTABILITY audit: is the winning harmonic determined by cell GEOMETRY
    (direction / branch / ln Q), i.e. a frozen adapter LAW, or a per-cell free choice
    (overfitting)?  A bag whose index is geometrically predictable is a real adapter;
    one that is not is reported as such.
  * Residual cells are characterized (what they lock onto) and the next adapter named --
    not declared a limit.

Run: python3 gl3_clock_bag.py
"""
import math
import os
import sys
from collections import Counter, defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mb_gl3_wall_lift as W


def build_rows():
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
                        pred = {"a": Q / prof["Sa"], "b": Q / prof["Sb"],
                                "diag": Q / (prof["Sa"] + prof["Sb"])}
                        for d in ("a", "b", "diag"):
                            amp = W.transform_ray(prof, Q, d)
                            gamma, r2 = W.envelope_gamma(W.NU_GRID, amp)
                            dip, ndips = W.deep_dip_spacing(W.NU_GRID, amp)
                            amax = float(np.max(amp))
                            depth = float(np.min(amp)) / amax if amax > 0 else float("nan")
                            rows.append(dict(csign=csign, branch=branch, n=n, f=f, X=X,
                                             Q=Q, direction=d, r2=r2, dip=dip, ndips=ndips,
                                             pred=pred[d], depth=depth,
                                             ratio=(dip / pred[d] if pred[d] > 0 and np.isfinite(dip) else float("nan"))))
    return rows


def best_harmonic(ratio, bag):
    """closest clock in bag; return (k, rel_err)."""
    if not np.isfinite(ratio) or ratio <= 0:
        return None, float("inf")
    best_k, best_e = None, float("inf")
    for k in bag:
        e = abs(ratio / k - 1.0)
        if e < best_e:
            best_e, best_k = e, k
    return best_k, best_e


INT_BAG = [1, 2, 3, 4, 5, 6]
RAT_BAG = sorted({p / q for q in (1, 2, 3, 4) for p in range(1, 4 * q + 1)})


def main():
    rows = build_rows()
    N = len(rows)
    vis = [r for r in rows if r["ndips"] >= 3]
    coh = [r for r in vis if r["r2"] >= 0.80]
    print(f"GL(3) wall cells: {N} total | visible(>=3 dips) {len(vis)} | coherent(R2>=0.80) {len(coh)}")
    # VANISHING probe: does |V(nu)| actually reach the floor at its deepest dip, or are these
    # only shallow local minima?  depth = min|V|/max|V|.  This test does NOT enforce vanishing;
    # this line reports how close the measured cancellations come to it.
    depths = sorted(r["depth"] for r in rows if np.isfinite(r["depth"]))
    dd = np.array(depths)
    print(f"[vanishing probe] deepest-dip depth min|V|/max|V| across {len(dd)} cells: "
          f"median {np.median(dd):.2e}, min {dd.min():.2e}, "
          f"frac<1e-3 {np.mean(dd<1e-3):.2f}, frac<1e-6 {np.mean(dd<1e-6):.2f}")
    print(f"  => these are {'GENUINE VANISHINGS' if np.median(dd)<1e-6 else 'shallow local minima, NOT vanishings'} "
          f"(the clock is their spacing; depth is a separate question the wall test does not force).")
    print(f"baseline single near-vector clock [0.75,1.75]: "
          f"{sum(1 for r in rows if 0.75 <= r['ratio'] <= 1.75 and np.isfinite(r['ratio']))}/{N} "
          f"(coherent subset {sum(1 for r in coh if 0.75 <= r['ratio'] <= 1.75)}/{len(coh)})")

    # REGULAR CARRIER SCALING first (the basic technique): one fixed global scale H,
    # applied uniformly to the prediction (rescale the carrier), swept over the
    # root-of-unity / small-rational harmonics.  How much does plain scaling alone recover?
    print("\n=== REGULAR carrier scaling: single global H, near-vector [0.75,1.75] on coherent ===")
    # the pi/m carrier-scale family (mu_m cells) the method actually uses, vs plain rationals
    Hs = [("pi/6", math.pi/6), ("pi/4", math.pi/4), ("pi/3", math.pi/3),
          ("1", 1.0), ("5/4", 1.25), ("4/3", 4.0/3),
          ("pi/2", math.pi/2), ("2pi/3", 2*math.pi/3), ("pi", math.pi)]
    base = sum(1 for r in coh if 0.75 <= r["ratio"] <= 1.75)
    best_H, best_n, best_lab = 1.0, base, "1"
    for lab, H in Hs:
        n = sum(1 for r in coh if np.isfinite(r["ratio"]) and 0.75 <= r["ratio"] / H <= 1.75)
        tag = "  <- baseline (no scale)" if lab == "1" else ""
        print(f"  H={lab:>5}={H:.4f}: {n:>2}/{len(coh)} coherent pass near-vector{tag}")
        if n > best_n:
            best_H, best_n, best_lab = H, n, lab
    print(f"  best single regular scale: H={best_lab}={best_H:.4f} -> {best_n}/{len(coh)} "
          f"(baseline {base}); gain {best_n-base:+d}")
    # tight gate too (+/-15%) so a wide window is not doing the work
    print("  same sweep, TIGHT gate ratio/H in [0.90,1.10]:")
    for lab, H in Hs:
        n = sum(1 for r in coh if np.isfinite(r["ratio"]) and 0.90 <= r["ratio"] / H <= 1.10)
        print(f"    H={lab:>5}={H:.4f}: {n:>2}/{len(coh)}")
    print("  [interpretation] if one H sweeps most cells in, regular scaling suffices; if the")
    print("  cells split across several H, the carrier is genuinely multi-cell (needs the bag).")

    print("\n=== RATCHET on the coherent+visible subset (clean signal, honest denominator) ===")
    for tol in (0.06, 0.10, 0.15):
        n_int = sum(1 for r in coh if best_harmonic(r["ratio"], INT_BAG)[1] <= tol)
        n_rat = sum(1 for r in coh if best_harmonic(r["ratio"], RAT_BAG)[1] <= tol)
        print(f"  TOL={tol:.2f}:  integer-harmonic bag {n_int:>2}/{len(coh)}   "
              f"rational bag (q<=4) {n_rat:>2}/{len(coh)}")

    # winning integer harmonic per cell (at TOL=0.10) and its predictability by geometry
    print("\n=== PREDICTABILITY audit (is the winning harmonic a frozen geometric law?) ===")
    tol = 0.10
    by_dir = defaultdict(Counter)
    matched = []
    for r in coh:
        k, e = best_harmonic(r["ratio"], INT_BAG)
        if e <= tol:
            by_dir[r["direction"]][k] += 1
            matched.append((r, k))
    for d in ("a", "b", "diag"):
        tot = sum(by_dir[d].values())
        dist = ", ".join(f"{k}x:{c}" for k, c in sorted(by_dir[d].items()))
        print(f"  direction {d:>4}: {tot} matched  [{dist}]")
    # is k predictable from (direction, branch)?  frozen rule = the modal k per (dir,branch)
    rule = {}
    cnt = defaultdict(Counter)
    for r, k in matched:
        cnt[(r["direction"], r["branch"])][k] += 1
    hit = 0
    for r, k in matched:
        modal = cnt[(r["direction"], r["branch"])].most_common(1)[0][0]
        rule[(r["direction"], r["branch"])] = modal
        if k == modal:
            hit += 1
    print(f"  frozen rule k = modal harmonic per (direction,branch): "
          f"{hit}/{len(matched)} matched cells obey it "
          f"({100.0*hit/max(len(matched),1):.0f}%)  -> "
          f"{'geometric adapter LAW' if hit/max(len(matched),1) > 0.8 else 'not cleanly geometric (report as fit)'}")
    print(f"  rule table: " + "; ".join(f"{k}->{v}x" for k, v in sorted(rule.items())))

    # ADAPTER: apply the frozen rule (predict k from geometry) and count productive
    print("\n=== BAG+ADAPTER (frozen rule, applied to ALL coherent cells; held to TOL) ===")
    for tol in (0.06, 0.10, 0.15):
        good = 0
        for r in coh:
            key = (r["direction"], r["branch"])
            k = rule.get(key)
            if k is None:
                continue
            if np.isfinite(r["ratio"]) and abs(r["ratio"] / k - 1.0) <= tol:
                good += 1
        print(f"  TOL={tol:.2f}: frozen-rule productive {good}/{len(coh)} "
              f"(baseline near-vector {sum(1 for r in coh if 0.75<=r['ratio']<=1.75)})")

    # DYNAMIC-SCALE LAW test: is the ratio a clean function of (csign,branch,dir,Q)?
    print("\n=== DYNAMIC clock-scale law: ratio grouped by (csign,branch,dir,Q) ===")
    print("  a frozen dynamic scale exists iff ratio is tight within each geometry+Q group")
    grp = defaultdict(list)
    for r in coh:
        if np.isfinite(r["ratio"]):
            grp[(r["csign"], r["branch"], r["direction"], r["Q"])].append(r["ratio"])
    consistent = tot = 0
    for key in sorted(grp):
        vals = grp[key]
        if len(vals) < 2:
            continue
        spread = (max(vals) - min(vals)) / max(np.mean(vals), 1e-9)
        tot += 1
        consistent += spread < 0.10
        c, br, d, Q = key
        print(f"  c{c:+d} {br:>5} {d:>4} Q={Q:>4.0f}: ratio {np.mean(vals):.3f} "
              f"(spread {spread:.2f}, n={len(vals)}) {'TIGHT' if spread<0.10 else 'loose'}")
    print(f"  => {consistent}/{tot} multi-cell geometry+Q groups are TIGHT (ratio determined "
          f"by geometry+Q) => dynamic scale is {'a LAW' if consistent/max(tot,1)>0.7 else 'not yet clean'}")

    # RESIDUAL characterization
    print("\n=== RESIDUAL (coherent cells the integer bag misses at TOL=0.10) -- named, not a limit ===")
    resid = [r for r in coh if best_harmonic(r["ratio"], INT_BAG)[1] > 0.10]
    print(f"  residual {len(resid)}/{len(coh)}; their ratios: "
          f"{sorted(round(r['ratio'],2) for r in resid if np.isfinite(r['ratio']))}")
    for r in resid[:12]:
        k_r, e_r = best_harmonic(r["ratio"], RAT_BAG)
        print(f"    c{r['csign']:+d} {r['branch']:>5} {r['direction']:>4} Q={r['Q']:.0f} "
              f"ratio={r['ratio']:.3f} -> nearest rational {k_r} (err {e_r:.2f})")


if __name__ == "__main__":
    main()
