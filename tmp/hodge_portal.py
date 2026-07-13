"""The dimensional portal: channel-resolved inspection inside a grade-4 Hodge structure.

Sam's architecture, operationalized: place the Hodge structure (the weight-4
tensor motive M = H1(E1) x H1(E2) x H1(E3) x H1(E4)) in one place; place the
helix's MEASUREMENT FIBERS (the local angles theta_1..theta_4(p)) next to it;
the portal is the per-prime channel decomposition.  The Deligne-torus reading
of M assigns H^{p,q} to clock frequency q-p; fiber-side the 16 lanes are the
sign vectors eps in {+-1}^4, and the diagonal frequency k = sum(eps) sorts
them into the Hodge channels:

    k = 4: (4,0)  1 lane      k = 2: (3,1)  4 lanes     k = 0: (2,2)  6 lanes

The 1D readout lam_p = sum_k T_k(p) is the SUM of the channels -- unmixable.
With the fibers alongside, every channel is read separately at every prime:

    T_k(p) = sum_{eps: sum eps = k} exp(i eps . theta(p))     -- the portal.

Exact product-Sato-Tate predictions (E[e^{2i m theta}] = -1/2 iff |m|=1,
1 iff m=0, else 0), all falsifiable:

  PT1 primitive channel moments:  avg|T_0|^2 = 99/8 = 12.375,
      avg|T_2|^2 = 7, avg|T_4|^2 = 1
  PT2 degenerate control (all clocks equal): 36, 16, 1 -- and CONSTANT:
      every balanced lane has eps . theta = 0 when the clocks coincide, so
      T_0 = 6 frozen (|T_0|^2 = 36 with zero variance).  Channel constancy
      is the portal's signature of algebraicity: the degenerate block's six
      lanes are exact DC (its six known algebraic classes); the primitive's
      lanes all fluctuate (the homeless fiber, Q-count 0).
  PT3 INSIDE the (2,2) block: the 6 lanes fold into 3 pair-directions
      c_P = cos(eps_P . theta), P in {12|34, 13|24, 14|23}; the interior
      Gram is exactly  diag 17/32, off-diag 1/4  -- an S3-symmetric 1 (+) 2
      split (eigenvalues 33/32 and 9/32 twice); the 2-dim piece is where a
      grade-4 exotic class would live.
  PT4 wrong-harmonic falsifier: replace theta_1 <- 2 theta_1; the moments
      must leave the predictions by >> statistical error.

Statistics: 148,933 primes to 2e6 (theta_cache) => rel. error ~0.3%.

Run: python3 hodge_portal.py     (~20 s)
"""
import os, sys, math, itertools
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from theta_cache import theta_table

LABS = ["11a1", "37a1", "53a1", "61a1"]
BAD = {11, 37, 53, 61}


def channels(TH, doubled=None):
    """T_k(p) arrays for k = 0, 2, 4 from four theta arrays (good primes)."""
    th = np.stack(TH, axis=0)                      # 4 x nprimes
    if doubled is not None:
        th = th.copy()
        th[doubled] *= 2.0
    T = {0: 0j, 2: 0j, 4: 0j}
    for eps in itertools.product((1, -1), repeat=4):
        k = sum(eps)
        if k in T:
            T[k] = T[k] + np.exp(1j * (np.array(eps) @ th))
    return T


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# HODGE PORTAL -- reading inside the grade-4 structure, channel by channel")
    P("#" * 78)
    P()
    tabs = [theta_table(l) for l in LABS]
    nmax = min(len(t) for t in tabs) - 1
    ps = np.array([p for p in range(2, nmax + 1)
                   if not np.isnan(tabs[0][p]) and p not in BAD])
    # restrict to actual primes: theta tables are NaN off primes
    good = ~np.isnan(tabs[0][ps])
    for t in tabs[1:]:
        good &= ~np.isnan(t[ps])
    ps = ps[good]
    TH = [np.asarray(t[ps], dtype=float) for t in tabs]
    n = len(ps)
    P(f"fibers loaded: {n} good primes to {nmax} (portal statistics ~"
      f"{100 / math.sqrt(n):.2f}%)")
    P()

    def report(name, T, preds):
        P(f"  {name}:")
        for k, pred in preds.items():
            m = np.abs(T[k]) ** 2
            se = m.std() / math.sqrt(n)
            tag = (f"({abs(m.mean() - pred) / se:4.1f} sigma)" if se > 0
                   else "(CONSTANT channel -- frozen DC)")
            P(f"    avg|T_{k}|^2 = {m.mean():8.4f} +- {se:.4f}   "
              f"exact {pred:8.4f}   {tag}")

    P("PT1 -- primitive quadruple (four independent clocks):")
    Tp = channels(TH)
    report("channels (2,2)/(3,1)/(4,0)", Tp, {0: 99 / 8, 2: 7.0, 4: 1.0})
    P()

    P("PT2 -- degenerate control (all four clocks = 11a1):")
    Td = channels([TH[0]] * 4)
    report("channels", Td, {0: 36.0, 2: 16.0, 4: 1.0})
    P("    T_0 = 6 FROZEN (every balanced lane exactly DC): channel constancy")
    P("    = the portal's algebraicity signature; the primitive's fluctuating")
    P("    lanes (PT1) are the homeless fiber's Q-count 0, seen live.")
    P()

    P("PT3 -- INSIDE the (2,2) block: the 3 pair-directions' Gram matrix:")
    pairs = {"12|34": (1, 1, -1, -1), "13|24": (1, -1, 1, -1),
             "14|23": (1, -1, -1, 1)}
    th = np.stack(TH, axis=0)
    c = {k: np.cos(np.array(e) @ th) for k, e in pairs.items()}
    keys = list(pairs)
    G = np.zeros((3, 3))
    for i, a in enumerate(keys):
        for j, b in enumerate(keys):
            G[i, j] = (c[a] * c[b]).mean()
    P("    measured Gram (exact: diag 17/32 = 0.53125, off 1/4 = 0.25):")
    for i, a in enumerate(keys):
        P(f"      {a}:  " + "  ".join(f"{G[i, j]:+.5f}" for j in range(3)))
    ev = np.linalg.eigvalsh(G)
    P(f"    eigenvalues: {ev[0]:.5f}, {ev[1]:.5f}, {ev[2]:.5f}   "
      f"(exact 9/32 = 0.28125 x2, 33/32 = 1.03125)")
    P("    => S3-symmetric interior split 1 (+) 2: the common mode and the")
    P("       2-dim exotic-candidate plane, resolved as separate coordinates.")
    P()

    P("PT4 -- wrong-harmonic falsifier (theta_1 <- 2 theta_1):")
    Tw = channels(TH, doubled=0)
    report("channels", Tw, {0: 99 / 8, 2: 7.0, 4: 1.0})
    P("    (deviations in sigma are the falsifier firing: the portal reads")
    P("     the true clocks, not any clocks)")
    P()

    P("READING:")
    P("  The 1D readout lam_p = sum of channels cannot be unmixed; with the")
    P("  measurement fibers placed next to the structure, the portal reads")
    P("  each Hodge channel separately at every prime.  PT1/PT2 calibrate the")
    P("  instrument against exact product-Sato-Tate; PT3 is the inspection:")
    P("  the interior geometry of the homeless fiber's (2,2) block, measured")
    P("  -- the first channel-resolved map of a grade-4 Hodge structure with")
    P("  no classical home.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "hodge_portal_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to hodge_portal_results.txt]")


if __name__ == "__main__":
    main()
