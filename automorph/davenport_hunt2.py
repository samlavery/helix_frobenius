#!/usr/bin/env python3
"""
Stronger rank-3 Davenport counterexample hunt (v2).

Core idea: a counterexample is a zero-sum-free (ZSF) MULTISET of size d*(G)+1.
We always have ZSF multisets of size d*(G) (the canonical basis construction
e1^{n1-1} e2^{n2-1} e3^{n3-1}). The hunt is a walk on the graph of ZSF multisets
trying to increase size to d*(G)+1.

Neighborhood of a ZSF multiset A (as a Counter over elements):
  - ADD g : if A+{g} is ZSF and |A|<target, add it (increases size).
  - SWAP  : remove one occurrence of some element, add a different element,
            keeping ZSF (size preserved, explores plateau).
  - DROP  : remove one element (size down; escape dead ends).

Objective: maximize |A| subject to ZSF. Reaching target=d*(G)+1 => COUNTEREXAMPLE.

Incremental ZSF check on ADD uses the full recomputation of the subset-sum
bitmask (cheap enough for |G| <= few thousand): we cache the mask for the
current multiset and, for an ADD of g, test  (mask | translate(mask,g) | bit g)
has bit0 clear.  On SWAP/DROP we recompute the mask from scratch (order-free).
"""
import sys, random, time
from collections import Counter
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_rank3 import Group, translate_mask


def subset_sum_mask(elems, perm, n):
    """Bitmask of nonempty subset sums of the multiset given as flat list."""
    S = 0
    for g in elems:
        S |= translate_mask(S, perm[g], n) | (1 << g)
    return S


def can_add(mask, g, perm, n):
    """Return new mask if adding g keeps ZSF (bit0 stays clear), else None."""
    new = mask | translate_mask(mask, perm[g], n) | (1 << g)
    if new & 1:
        return None
    return new


class Hunt:
    def __init__(self, G):
        self.G = G
        self.perm = G.perm
        self.n = G.order
        self.elts = list(range(1, self.n))

    def canonical(self):
        G = self.G
        n1, n2, n3 = G.inv
        e1 = G.idx((1, 0, 0)); e2 = G.idx((0, 1, 0)); e3 = G.idx((0, 0, 1))
        return [e1] * (n1 - 1) + [e2] * (n2 - 1) + [e3] * (n3 - 1)

    def random_zsf(self, rng, target):
        """Greedy random ZSF multiset up to size target (or until stuck)."""
        elems = []
        mask = 0
        pool = self.elts[:]
        tries = 0
        while len(elems) < target and tries < target * 6:
            g = rng.choice(pool)
            nm = can_add(mask, g, self.perm, self.n)
            if nm is not None:
                mask = nm
                elems.append(g)
            else:
                tries += 1
        return elems, mask

    def local_search(self, start_elems, target, rng, budget):
        """Hill-climb + occasional random kicks. Returns (best_size, best_elems)."""
        elems = list(start_elems)
        mask = subset_sum_mask(elems, self.perm, self.n)
        best_size = len(elems)
        best_elems = list(elems)
        no_improve = 0

        for step in range(budget):
            # try ADD first (greedy improvement)
            if len(elems) < target:
                rng.shuffle(self.elts)
                added = False
                for g in self.elts:
                    nm = can_add(mask, g, self.perm, self.n)
                    if nm is not None:
                        elems.append(g); mask = nm; added = True
                        break
                if added:
                    if len(elems) > best_size:
                        best_size = len(elems); best_elems = list(elems)
                        no_improve = 0
                        if best_size >= target:
                            return best_size, best_elems
                    continue
            # SWAP: remove one, add a different one keeping ZSF (plateau move)
            no_improve += 1
            if not elems:
                elems, mask = self.random_zsf(rng, target)
                continue
            i = rng.randrange(len(elems))
            removed = elems[i]
            trial = elems[:i] + elems[i+1:]
            tmask = subset_sum_mask(trial, self.perm, self.n)
            # add a random new element != removed
            rng.shuffle(self.elts)
            done = False
            for g in self.elts:
                if g == removed:
                    continue
                nm = can_add(tmask, g, self.perm, self.n)
                if nm is not None:
                    trial.append(g)
                    elems, mask = trial, nm
                    done = True
                    break
            if not done:
                elems, mask = trial, tmask  # just a DROP
            # random restart on long stagnation
            if no_improve > max(300, target * 20):
                if rng.random() < 0.5:
                    elems = list(best_elems)
                else:
                    elems, _ = self.random_zsf(rng, target)
                mask = subset_sum_mask(elems, self.perm, self.n)
                no_improve = 0
        return best_size, best_elems

    def hunt(self, target, restarts=30, budget=4000, seed=0, verbose=False):
        rng = random.Random(seed)
        best = (0, [])
        # start from canonical + many random seeds
        starts = [self.canonical()]
        for _ in range(restarts):
            e, _ = self.random_zsf(rng, target)
            starts.append(e)
        for si, s in enumerate(starts):
            bs, be = self.local_search(s, target, rng, budget)
            if bs > best[0]:
                best = (bs, be)
                if verbose:
                    print(f"    start{si}: best_size={bs}/{target}")
                if bs >= target:
                    # verify
                    m = subset_sum_mask(be, self.perm, self.n)
                    assert not (m & 1), "verify failed!"
                    return best
        return best


def verify_zsf_bruteforce(elems, G):
    """Independent verification via itertools over all 2^len subsets (len<=~24)."""
    import itertools
    n = len(elems)
    for r in range(1, n + 1):
        for combo in itertools.combinations(range(n), r):
            s = 0
            for idx in combo:
                s = G.add_idx(s, elems[idx])
            if s == 0:
                return False, combo
    return True, None


if __name__ == "__main__":
    inv = tuple(int(x) for x in sys.argv[1].split(",")) if len(sys.argv) > 1 else (3,6,6)
    G = Group(inv); G.build_add_tables()
    H = Hunt(G)
    dstar = G.d_star(); M = dstar + 1
    t0 = time.time()
    best_size, best_elems = H.hunt(target=M, restarts=25, budget=3000, seed=1, verbose=True)
    print(f"{inv}: d*={dstar} M={M} -> best ZSF size = {best_size}  ({time.time()-t0:.1f}s)  "
          f"{'*** COUNTEREXAMPLE ***' if best_size>=M else 'no counterexample this run'}")
