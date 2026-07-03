#!/usr/bin/env python3
"""Exact D(G) sweep over unresolved rank-3 targets, ordered by |G|.
Each group gets a node budget; records EXACT D=M confirmations and any
counterexample (D>M). Writes results incrementally to stdout (flush)."""
import sys, time
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_fast import FastG, exact_search, first_element_reps


def name(inv):
    return "C" + "+C".join(str(n) for n in inv)


# Unresolved rank-3 targets, ordered by |G|. Include n1=2 ones (literature says
# known, but we get INDEPENDENT exact confirmation) and the un-flagged ones.
TARGETS = [
    (2,2,10),(2,2,12),(2,2,14),(2,6,6),(2,2,18),(2,2,20),(3,6,6),
    (2,4,12),(2,2,22),(2,2,24),(2,2,26),(2,2,28),(6,6,6),(2,2,30),
    (4,4,12),(3,6,12),(2,10,10),(5,5,10),(2,6,12),(2,12,12),
]

def sweep(node_cap, only=None):
    results = []
    for inv in TARGETS:
        if only and inv not in only:
            continue
        FG = FastG(inv)
        nreps = len(first_element_reps(FG))
        t0 = time.time()
        ml, wit, nodes, to = exact_search(FG, target=FG.M, node_cap=node_cap)
        dt = time.time() - t0
        D = ml + 1
        if to:
            verdict = f"TIMEOUT (best d>={ml}, so D>={D}); need hunt/more budget"
        elif D > FG.M:
            verdict = f"*** COUNTEREXAMPLE: D={D} > M={FG.M} ***  witness={wit}"
        elif D == FG.M:
            verdict = "EXACT: D=M (conjecture confirmed for this group)"
        else:
            verdict = f"ANOMALY D={D}<M={FG.M}"
        line = (f"{name(inv):14} |G|={FG.n:4} d*={FG.dstar:3} M={FG.M:3} "
                f"reps={nreps:3} nodes={nodes:>10} {dt:6.1f}s  D={D:3}  {verdict}")
        print(line, flush=True)
        results.append((inv, FG.n, FG.dstar, FG.M, D, to, nodes, dt))
    return results


if __name__ == "__main__":
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 30_000_000
    sweep(cap)
