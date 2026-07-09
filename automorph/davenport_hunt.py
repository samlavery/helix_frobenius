#!/usr/bin/env python3
"""
Rank-3 Davenport counterexample HUNT.

Goal: find a zero-sum-free sequence of length d*(G)+1 over a rank-3 group G
(=> d(G) > d*(G) => D(G) > M(G), a counterexample to the open conjecture).

Two engines:
  A) exact_max_zsf  : branch-and-bound exhaustive max zero-sum-free length,
                      with automorphism/canonical pruning. Only for small |G|.
  B) anneal_hunt    : simulated annealing / randomized greedy over multisets,
                      objective = length of longest zero-sum-free prefix.
                      Scales to large |G|; finds LOWER bounds on d(G).

If anneal reaches length d*(G)+1 -> candidate counterexample -> verify 3 ways.
If exact proves max = d*(G)      -> new exact value D(G)=M(G) (computer-proof).

Fast tester: we reuse the bitset DP but with a numpy-free pure-int mask and a
precomputed per-generator translate that we cache.
"""
import sys
import random
import time
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_rank3 import Group, translate_mask


# ---- fast incremental zero-sum-free machine -------------------------------

class ZSFMachine:
    """Incrementally maintain reachable-subset-sum bitmask as we push/pop
    elements. Supports checking whether adding g keeps zero-sum-freeness."""

    def __init__(self, G):
        self.G = G
        self.perm = G.perm
        self.n = G.order
        self.S = 0
        self.stack = []  # previous S masks for pop

    def reset(self):
        self.S = 0
        self.stack = []

    def can_add(self, g):
        """Return the new mask if adding g stays zero-sum-free, else None."""
        add = translate_mask(self.S, self.perm[g], self.n) | (1 << g)
        newS = self.S | add
        if newS & 1:
            return None
        return newS

    def push(self, g):
        newS = self.can_add(g)
        if newS is None:
            return False
        self.stack.append(self.S)
        self.S = newS
        return True

    def pop(self):
        self.S = self.stack.pop()


def prefix_zsf_len(seq, G):
    """Longest zero-sum-free prefix length of a multiset given as list."""
    S = 0
    perm = G.perm
    n = G.order
    for i, g in enumerate(seq):
        add = translate_mask(S, perm[g], n) | (1 << g)
        S |= add
        if S & 1:
            return i
    return len(seq)


def is_zsf(seq, G):
    return prefix_zsf_len(seq, G) == len(seq)


# ---- engine A: exact branch and bound -------------------------------------

def exact_max_zsf(G, target=None, node_cap=None, order_by_ord=True):
    """Exhaustive search for max zero-sum-free length.
    Canonical: multiset -> nondecreasing element index. Never use identity.
    target: if set, stop as soon as a ZSF sequence of this length is found
            (used to test 'does a length-(d*+1) ZSF sequence exist?').
    Returns (max_len, witness, nodes, timed_out)."""
    n = G.order
    perm = G.perm
    elts = list(range(1, n))
    best = [0, []]
    nodes = [0]
    timed_out = [False]

    def rec(S, start, depth, seq):
        nodes[0] += 1
        if node_cap is not None and nodes[0] > node_cap:
            timed_out[0] = True
            raise TimeoutError
        if depth > best[0]:
            best[0] = depth
            best[1] = list(seq)
            if target is not None and depth >= target:
                raise StopIteration
        for gi in range(start, len(elts)):
            g = elts[gi]
            add = translate_mask(S, perm[g], n) | (1 << g)
            newS = S | add
            if newS & 1:
                continue
            seq.append(g)
            rec(newS, gi, depth + 1, seq)
            seq.pop()

    try:
        rec(0, 0, 0, [])
    except StopIteration:
        pass
    except TimeoutError:
        pass
    return best[0], best[1], nodes[0], timed_out[0]


# ---- engine B: simulated annealing ----------------------------------------

def anneal_hunt(G, target, iters=200000, restarts=20, seed=0, verbose=False):
    """Search for a zero-sum-free multiset of length `target`.
    State: a list `seq` of element indices (the multiset). Objective to
    MAXIMIZE: prefix_zsf_len after a random shuffle-tolerant scoring.
    Because zero-sum-freeness is order-independent, the true objective is
    'is the whole multiset zero-sum-free'. We build greedily then locally edit.

    Strategy per restart:
      - greedy random build up to as long as possible;
      - then hill-climb / anneal: replace a random element with a random one,
        keep if it does not decrease the zero-sum-free length; accept worse
        moves with Metropolis probability.
    Returns (best_len, witness) ; best_len==target => COUNTEREXAMPLE candidate.
    """
    rng = random.Random(seed)
    n = G.order
    elts = list(range(1, n))
    best_overall = (0, [])

    for r in range(restarts):
        # greedy random build
        seq = []
        mach = ZSFMachine(G)
        pool = elts[:]
        rng.shuffle(pool)
        # try to extend greedily by scanning shuffled elements repeatedly
        stuck_rounds = 0
        while len(seq) < target and stuck_rounds < 3:
            added = False
            rng.shuffle(pool)
            for g in pool:
                if mach.push(g):
                    seq.append(g)
                    added = True
                    if len(seq) >= target:
                        break
            if not added:
                stuck_rounds += 1
        cur_len = len(seq)
        if cur_len > best_overall[0]:
            best_overall = (cur_len, list(seq))
            if verbose:
                print(f"  [r{r}] greedy len {cur_len}/{target}")
        if cur_len >= target:
            return target, seq

        # anneal: keep a fixed-size candidate multiset of length `target-? `,
        # objective = zero-sum-free prefix length under best ordering (we use
        # a heuristic: score = max over a few random shuffles of prefix len).
        # We instead work with a length-`target` multiset and try to make it ZSF.
        # Build a length-`target` multiset (may not be ZSF) by padding.
        work = list(seq)
        while len(work) < target:
            work.append(rng.choice(elts))

        def score(mset):
            # best zero-sum-free prefix over a few shuffles
            best = 0
            for _ in range(4):
                rng.shuffle(mset)
                pl = prefix_zsf_len(mset, G)
                if pl > best:
                    best = pl
                    if best == target:
                        break
            return best

        cur_score = score(work)
        T0, T1 = 2.0, 0.01
        for it in range(iters):
            T = T0 * (T1 / T0) ** (it / iters)
            i = rng.randrange(target)
            old = work[i]
            work[i] = rng.choice(elts)
            new_score = score(work)
            d = new_score - cur_score
            if d >= 0 or rng.random() < pow(2.718281828, d / max(T, 1e-9)):
                cur_score = new_score
                if new_score > best_overall[0]:
                    best_overall = (new_score, list(work))
                    if verbose:
                        print(f"  [r{r} it{it}] score {new_score}/{target} T={T:.3f}")
                    if new_score >= target:
                        # verify it's genuinely ZSF as a multiset
                        if is_zsf(work, G):
                            return target, list(work)
            else:
                work[i] = old
        if best_overall[0] >= target:
            break

    return best_overall


if __name__ == "__main__":
    # smoke test on a known counterexample-free small group
    G = Group((3, 3, 3))
    G.build_add_tables()
    dstar = G.d_star()
    print(f"C3^3: d*={dstar}, M={dstar+1}")
    ml, wit, nodes, to = exact_max_zsf(G)
    print(f"  exact max zsf = {ml} (D={ml+1}, expected M={dstar+1}) nodes={nodes} timeout={to}")
