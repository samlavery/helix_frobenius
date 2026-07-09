#!/usr/bin/env python3
"""
Fast numpy-based zero-sum-free machinery + exact search + hunt.
Reachable-subset-sum set represented as a boolean numpy array of length |G|.
Group-translate by g is a fixed index permutation -> vectorized fancy indexing.
"""
import sys, time, random
import numpy as np
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_rank3 import Group


class FastG:
    def __init__(self, inv):
        self.G = Group(inv)
        self.inv = tuple(inv)
        self.n = self.G.order
        self.dstar = self.G.d_star()
        self.M = self.dstar + 1
        # perm[g] : array where perm[g][x] = x +_G g  (destination index of x)
        self.G.build_add_tables()
        self.perm = np.array(self.G.perm, dtype=np.int64)  # shape (n,n)

    def add_mask(self, mask, g):
        """mask: bool array len n of reachable nonempty subset sums.
        Return new reachable set after appending element g.
        new = mask | mask-translated-by-g | {g}."""
        translated = np.zeros(self.n, dtype=bool)
        # x reachable -> x+g reachable
        translated[self.perm[g][mask]] = True
        new = mask | translated
        new[g] = True
        return new

    def zsf_ok_after_add(self, mask, g):
        """Return (ok, newmask): ok False if identity (index0) becomes reachable."""
        new = self.add_mask(mask, g)
        return (not new[0]), new

    def is_zsf(self, elems):
        mask = np.zeros(self.n, dtype=bool)
        for g in elems:
            mask = self.add_mask(mask, g)
            if mask[0]:
                return False
        return True


# ---------------- exact search with automorphism + pruning ----------------

def unit_automorphisms(inv):
    """Return a list of automorphisms of G = C_{n1}xC_{n2}xC_{n3} as functions
    on coordinate triples, restricted to the 'diagonal' multiplier + permutation
    subgroup that is cheap to apply. We use:
      - coordinate multiplication by units u_i in (Z/n_i)^* on each factor,
      - permutation of equal-order factors.
    This is a SUBGROUP of Aut(G) (not all of it when factors share primes), but
    it is a valid group of automorphisms => sound for orbit reduction of the
    FIRST element. Using a subgroup only weakens pruning, never correctness."""
    import math
    from itertools import permutations, product
    r = len(inv)
    def units(m):
        return [u for u in range(1, m) if math.gcd(u, m) == 1]
    Us = [units(m) for m in inv]
    # factor permutations that respect orders (permute only equal-order factors)
    perms = [p for p in permutations(range(r))
             if tuple(inv[p[i]] for i in range(r)) == tuple(inv)]
    autos = []
    for p in perms:
        for u in product(*Us):
            autos.append((p, u))
    return autos


def first_element_reps(FG):
    """Representatives of nonidentity elements under the (sub)automorphism group,
    to seed the first element of the search (orbit reduction)."""
    inv = FG.inv
    r = len(inv)
    autos = unit_automorphisms(inv)
    G = FG.G
    seen = set()
    reps = []
    for x in range(1, FG.n):
        if x in seen:
            continue
        # build orbit
        cx = G.coords(x)
        orbit = set()
        for (p, u) in autos:
            c = tuple(cx[p[i]] for i in range(r))
            c = tuple((c[i] * u[i]) % inv[i] for i in range(r))
            orbit.add(G.idx(c))
        if x == min(orbit):
            reps.append(x)
        seen |= orbit
    return reps


def exact_search(FG, target=None, node_cap=None, verbose=False):
    """Max ZSF length via DFS. First element from automorphism reps; subsequent
    elements canonical nondecreasing index. Returns (maxlen, witness, nodes, timeout)."""
    n = FG.n
    perm = FG.perm
    G = FG.G
    # neg[g] = index of -g. Adding g to a ZSF set S hits 0 iff -g in reach(S).
    neg = np.array([G.idx(tuple((-c) % m for c, m in zip(G.coords(g), FG.inv)))
                    for g in range(n)], dtype=np.int64)
    reps = first_element_reps(FG)
    best = [0, []]
    nodes = [0]
    to = [False]

    def add_mask(mask, g):
        translated = np.zeros(n, dtype=bool)
        translated[perm[g][mask]] = True
        new = mask | translated
        new[g] = True
        return new

    def rec(mask, start, depth, seq):
        nodes[0] += 1
        if node_cap and nodes[0] > node_cap:
            to[0] = True
            raise TimeoutError
        if depth > best[0]:
            best[0] = depth; best[1] = list(seq)
            if target and depth >= target:
                raise StopIteration
        # UPPER-BOUND PRUNE: an element g can only ever be added (now or later,
        # in this or a deeper node) if g itself is not already a reachable sum
        # combined with... we use the necessary condition: g is addable in the
        # NEXT step only if adding it keeps ZSF. The set of g>=start that are
        # addable-right-now is a superset of what any descendant can append
        # first, and each descendant append only shrinks the addable set. So
        # depth + (#addable g>=start) is a valid upper bound on reachable depth.
        addable = []
        for g in range(start, n):
            # quick necessary check: g not making 0 reachable
            # (0 reachable iff mask[-g] set, i.e. mask at inverse of g, or g==0)
            if mask[neg[g]]:
                continue
            addable.append(g)
        if depth + len(addable) <= best[0]:
            return
        for g in addable:
            new = add_mask(mask, g)
            # new[0] cannot be true here since g passed the mask[neg[g]] test,
            # but keep the guard for safety.
            if new[0]:
                continue
            seq.append(g)
            rec(new, g, depth + 1, seq)
            seq.pop()

    empty = np.zeros(n, dtype=bool)
    try:
        for g in reps:
            new = add_mask(empty, g)
            if new[0]:
                continue
            rec(new, g, 1, [g])
    except StopIteration:
        pass
    except TimeoutError:
        pass
    return best[0], best[1], nodes[0], to[0]


if __name__ == "__main__":
    # timing sanity
    for inv in [(2,2,10),(3,3,3),(2,4,4)]:
        FG = FastG(inv)
        t0 = time.time()
        ml, wit, nodes, to = exact_search(FG, target=FG.M, node_cap=20_000_000)
        D = ml + 1
        print(f"{inv}: d*={FG.dstar} M={FG.M} max_zsf={ml} D={D} "
              f"{'D=M' if D==FG.M else ('CE!' if D>FG.M else '??')} "
              f"nodes={nodes} to={to} {time.time()-t0:.1f}s  reps={len(first_element_reps(FG))}")
