"""
Refinements to the harmonic-chart bench:

  (1) exact WINDOW normalisation of the Landau DC (the full-range formula is
      wrong on a sub-window and the earlier run showed the discrepancy),
  (2) the actual WALL-CELL OCCUPANCY numbers -- the quantity Sam asked for,
  (3) the TRUE noise floor, which is NOT 1/sqrt(N): the zeros are rigid and the
      Landau error term is O(log T), so the bench is ~20x more sensitive than
      the random-null threshold suggests.  This sets the smallest detectable
      wall excess.
  (4) a fine scan of |c_1(H)| across H, locating the spikes.
"""

import numpy as np
from harmonic_chart_bench import (load_zeros, rvm, von_mangoldt_at, harmonics,
                                  cell_counts, chi2_uniform, chi2_sf, TWOPI)


def landau_dc_window(H, j, T1, T2):
    """Exact windowed DC:  -[(T2-T1)/2pi * Lambda(x)/sqrt(x)] / [N(T2)-N(T1)]."""
    x = np.exp(j * H)
    lam = von_mangoldt_at(x)
    if lam == 0.0:
        return 0.0
    return -((T2 - T1) / TWOPI * lam / np.sqrt(x)) / (rvm(T2) - rvm(T1))


def main():
    gam = load_zeros()
    N = gam.size
    T1, T2 = gam[0], gam[-1]

    # ---------------------------------------------------------------- (1)
    print("=" * 78)
    print("(1) WINDOW-CORRECTED CALIBRATION  (measured vs exact Landau DC)")
    print("=" * 78)
    wins = [("full   ", gam), ("low half", gam[:N // 2]), ("high half", gam[N // 2:])]
    print(f"{'window':<11}{'scale':<10}{'measured':>11}{'predicted':>11}"
          f"{'rel err':>10}")
    for wname, g in wins:
        a, b = g[0], g[-1]
        for sname, H in [("log 2", np.log(2)), ("log 3", np.log(3)),
                         ("log 4", np.log(4)), ("log 5", np.log(5)),
                         ("log 7", np.log(7))]:
            c = harmonics(g, H, jmax=1)[0]
            pred = landau_dc_window(H, 1, a, b)
            rel = abs(abs(c) - abs(pred)) / abs(pred)
            print(f"{wname:<11}{sname:<10}{abs(c):>11.5f}{abs(pred):>11.5f}"
                  f"{rel:>9.2%}")

    # ---------------------------------------------------------------- (2)
    print()
    print("=" * 78)
    print("(2) WALL-CELL OCCUPANCY -- the fraction actually asked for")
    print("    wall = phase pi (cellAt H k = -1); bins centred so bin m/2 is the wall")
    print("=" * 78)
    for sname, H, m in [("pi/3", np.pi / 3, 6), ("pi/6", np.pi / 6, 12),
                        ("1 (unit)", 1.0, 6), ("log 3 (prime clock)", np.log(3), 6),
                        ("log 2 (prime clock)", np.log(2), 6)]:
        cnt = cell_counts(gam, H, m)
        wall = cnt[m // 2]
        frac = wall / N
        unif = 1.0 / m
        se = np.sqrt(unif * (1 - unif) / N)
        x2, df = chi2_uniform(cnt)
        print(f"\n  H = {sname},  {m} cells,  N = {N}")
        print(f"    counts        : {list(cnt)}")
        print(f"    wall cell     : {wall}   fraction {frac:.5f}   "
              f"uniform {unif:.5f}")
        print(f"    excess        : {frac - unif:+.5f}  "
              f"({(frac - unif)/se:+.2f} sigma, binomial se {se:.5f})")
        print(f"    chi2({df})     : {x2:.2f}   p = {chi2_sf(x2, df):.4f}")

    # ---------------------------------------------------------------- (3)
    print()
    print("=" * 78)
    print("(3) TRUE NOISE FLOOR (the zeros are rigid; O(log T)/N, not 1/sqrt(N))")
    print("=" * 78)
    rng = np.random.default_rng(11)
    Hs = rng.uniform(0.3, 2.5, 400)
    keep = []
    for H in Hs:                      # drop any H within 1e-2 of a prime clock
        if all(abs(H - np.log(p ** k)) > 1e-2
               for p in (2, 3, 5, 7, 11) for k in (1, 2, 3)):
            keep.append(H)
    keep = np.array(keep)
    mags = np.array([abs(harmonics(gam, H, jmax=1)[0]) for H in keep])
    rand_floor = np.sqrt(3.0 / N)
    print(f"  {keep.size} generic (non-prime-power) scales sampled")
    print(f"  |c_1|  median {np.median(mags):.5f}   mean {mags.mean():.5f}   "
          f"max {mags.max():.5f}   p99 {np.quantile(mags, 0.99):.5f}")
    print(f"  random-null 95% threshold sqrt(3/N) = {rand_floor:.5f}")
    print(f"  ratio: the zeros are {rand_floor/np.median(mags):.1f}x MORE uniform "
          f"than a random set")
    print(f"  Landau error scale  log(T)/N = {np.log(T2)/N:.5f}")
    det = np.quantile(mags, 0.99)
    print(f"\n  SMALLEST DETECTABLE EFFECT: a wall-pinned fraction f contributes")
    print(f"  |c_1| = f, so the bench excludes f > {det:.5f} "
          f"({det*100:.3f}%) at the 99th pct of the generic floor.")
    print(f"  (the pre-registered 1/sqrt(N) figure was {rand_floor*100:.2f}% -- "
          f"the bench is {rand_floor/det:.0f}x better than pre-registered)")

    # ---------------------------------------------------------------- (4)
    print()
    print("=" * 78)
    print("(4) FINE SCAN of |c_1(H)| -- where the spikes actually are")
    print("=" * 78)
    grid = np.linspace(0.60, 1.30, 1401)
    vals = np.array([abs(harmonics(gam, H, jmax=1)[0]) for H in grid])
    order = np.argsort(vals)[::-1][:10]
    print("  top 10 scales by |c_1| on H in [0.60, 1.30]:")
    for i in sorted(order, key=lambda i: -vals[i]):
        H = grid[i]
        x = np.exp(H)
        near = min(((abs(H - np.log(p ** k)), f"log {p}^{k}" if k > 1 else f"log {p}")
                    for p in (2, 3, 5, 7) for k in (1, 2, 3)))
        print(f"    H = {H:.4f}  x = e^H = {x:.4f}  |c_1| = {vals[i]:.5f}"
              f"   nearest clock {near[1]} (d = {near[0]:.4f})")
    print()
    for sname, H in [("pi/3", np.pi / 3), ("pi/6", np.pi / 6), ("1", 1.0)]:
        v = abs(harmonics(gam, H, jmax=1)[0])
        near = min(((abs(H - np.log(p ** k)), f"log {p}^{k}" if k > 1 else f"log {p}")
                    for p in (2, 3, 5, 7) for k in (1, 2, 3)))
        print(f"  H = {sname:<5} = {H:.4f}: |c_1| = {v:.5f}, "
              f"nearest prime clock {near[1]} at distance {near[0]:.4f} "
              f"({near[0]/H:.1%} away)")


if __name__ == "__main__":
    main()
