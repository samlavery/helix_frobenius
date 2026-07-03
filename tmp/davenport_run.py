#!/usr/bin/env python3
"""Driver: exact D(G) where feasible, else stochastic hunt, for rank-3 targets."""
import sys, time
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_rank3 import Group
from davenport_hunt import exact_max_zsf, anneal_hunt, is_zsf, prefix_zsf_len


def name(inv):
    return "C" + "+C".join(str(n) for n in inv)


def run_exact(inv, node_cap=3_000_000):
    G = Group(inv); G.build_add_tables()
    dstar = G.d_star(); M = dstar + 1
    t0 = time.time()
    # First: does a ZSF sequence of length M (=d*+1) exist? (target search)
    ml, wit, nodes, to = exact_max_zsf(G, target=M, node_cap=node_cap)
    dt = time.time() - t0
    if not to:
        # search completed. ml is the true max zero-sum-free length.
        D = ml + 1
        verdict = ("COUNTEREXAMPLE! D>M" if ml >= M else
                   ("D=M confirmed (EXACT)" if D == M else f"D={D}<M?! CHECK"))
        print(f"{name(inv):16} |G|={G.order:4} d*={dstar:3} M={M:3}  "
              f"EXACT max_zsf={ml} D={D}  [{verdict}]  nodes={nodes} {dt:.1f}s")
        return ('exact', inv, ml, D, M, nodes, dt, wit)
    else:
        print(f"{name(inv):16} |G|={G.order:4} d*={dstar:3} M={M:3}  "
              f"EXACT TIMEOUT best_zsf>={ml} (nodes={nodes}, {dt:.1f}s) -> anneal")
        return ('timeout', inv, ml, None, M, nodes, dt, wit)


def run_anneal(inv, iters=40000, restarts=12, seed=1):
    G = Group(inv); G.build_add_tables()
    dstar = G.d_star(); M = dstar + 1
    t0 = time.time()
    res = anneal_hunt(G, target=M, iters=iters, restarts=restarts, seed=seed)
    best_len, wit = res
    dt = time.time() - t0
    hit = best_len >= M
    verdict = ("COUNTEREXAMPLE CANDIDATE (len=M ZSF found!)" if hit
               else f"no ZSF of len M; best ZSF len found = {best_len} (d>={best_len}, so D>={best_len+1}; M={M})")
    print(f"{name(inv):16} |G|={G.order:4} d*={dstar:3} M={M:3}  "
          f"ANNEAL best_zsf_len={best_len}/{M}  [{verdict}]  {dt:.1f}s")
    return ('anneal', inv, best_len, None, M, None, dt, wit if hit else None)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "exact"
    # candidate targets (unresolved, prioritized). Grouped by feasibility.
    small_exact = [
        (2,2,10),(2,2,12),(2,2,14),(2,6,6),(3,6,6),
    ]
    mid = [
        (2,2,18),(2,2,20),(2,4,12),(4,4,12),(3,6,12),(6,6,6),
        (2,10,10),(5,5,10),(2,12,12),
    ]
    if mode == "exact":
        for inv in small_exact:
            run_exact(inv, node_cap=8_000_000)
    elif mode == "anneal":
        for inv in small_exact + mid:
            run_anneal(inv)
    elif mode == "one":
        inv = tuple(int(x) for x in sys.argv[2].split(","))
        run_exact(inv, node_cap=int(sys.argv[3]) if len(sys.argv)>3 else 8_000_000)
