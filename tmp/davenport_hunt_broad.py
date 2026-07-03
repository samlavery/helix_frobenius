#!/usr/bin/env python3
"""Broad stochastic counterexample sweep over unresolved rank-3 groups.
For each group: run the v3 structured+random hunter; report best ZSF size found
(a lower bound on d(G)) vs M. best>=M => counterexample candidate (flag loudly)."""
import sys, time
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_hunt3 import FastHunt
from davenport_candidates import rank3_groups, classify


def name(inv):
    return "C" + "+C".join(str(n) for n in inv)


def main(max_order, per_group_time):
    groups = rank3_groups(max_order)
    targets = []
    for inv in groups:
        resolved, reasons, flags, order, pg = classify(inv)
        # skip p-groups and C3+C3+C3d (truly resolved). Keep n1=2 & Cp+Cp+Cpq
        # (independent check). Skip |G|<32 (already GAP-exhausted, but cheap;
        # keep them as extra validation).
        if pg:
            continue
        if inv[0] == 3 and inv[1] == 3 and inv[2] % 3 == 0:
            continue
        targets.append(inv)
    print(f"# Broad hunt over {len(targets)} unresolved rank-3 groups, "
          f"|G|<={max_order}, {per_group_time}s each\n", flush=True)
    hits = []
    for inv in targets:
        H = FastHunt(inv)
        t0 = time.time()
        best_size, best = H.hunt(restarts=100000, seed=12345,
                                 verbose=False, time_limit=per_group_time)
        dt = time.time() - t0
        gap = H.M - best_size
        flag = ""
        if best_size >= H.M:
            flag = "  *** COUNTEREXAMPLE CANDIDATE ***"
            hits.append((inv, best))
        elif best_size == H.dstar:
            flag = "  (reached d*; no CE)"
        elif best_size < H.dstar:
            flag = f"  (below d*={H.dstar}; hunter underperformed)"
        print(f"{name(inv):16} |G|={H.n:5} d*={H.dstar:3} M={H.M:3}  "
              f"best_ZSF={best_size:3} (gap {gap:+d}) {dt:5.1f}s{flag}", flush=True)
    print(f"\n# COUNTEREXAMPLE CANDIDATES: {len(hits)}", flush=True)
    for inv, w in hits:
        print(f"#   {name(inv)}: {w}", flush=True)


if __name__ == "__main__":
    mo = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    tg = float(sys.argv[2]) if len(sys.argv) > 2 else 15
    main(mo, tg)
