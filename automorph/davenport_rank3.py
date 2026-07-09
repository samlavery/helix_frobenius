#!/usr/bin/env python3
"""
Davenport constant D(G) for rank-3 finite abelian groups: tester + hunt.

Conjecture under attack:  D(G) = M(G)  for rank-3 finite abelian G,
where  G = C_{n1} (+) C_{n2} (+) C_{n3},  n1 | n2 | n3,
       d*(G) = (n1-1)+(n2-1)+(n3-1),
       M(G)  = D*(G) = 1 + d*(G),
       D(G)  = 1 + d(G),  d(G) = max length of a zero-sum-free sequence over G.

Equivalent forms:
   D(G) = M(G)   <=>   d(G) = d*(G).
A COUNTEREXAMPLE is a zero-sum-free sequence of length d*(G)+1 = M(G).

Status (verified via literature, tmp/factorization_theory_notes.md + web):
   proven for rank<=2 and all p-groups;  FALSE for every rank>=4;  OPEN at rank 3.

Group element encoding:  a triple (a,b,c) with 0<=a<n1, 0<=b<n2, 0<=c<n3
   maps to a flat index  idx = (a*n2 + b)*n3 + c  in [0, |G|).
   Identity = index 0.

Zero-sum-free DP tester (bitset over |G| elements):
   Maintain the set S of NONEMPTY subset sums reachable so far as an int bitmask.
   Adding element g:  S  <-  S | translate(S, g) | bit(idx(g)),
   where translate(S,g) sends each set bit x to bit (x +_G g).
   The prefix is zero-sum-free iff bit 0 (the identity) never enters S.
"""

import sys
import itertools
import random


# ----------------------------------------------------------------------
# Group machinery
# ----------------------------------------------------------------------

class Group:
    """Finite abelian group C_{n1} (+) ... (+) C_{nk}, flat-indexed."""

    def __init__(self, invariants):
        # invariants: tuple (n1, n2, ...), not required sorted for the encoding,
        # but for M(G) we use them as given.
        self.inv = tuple(invariants)
        self.k = len(self.inv)
        self.order = 1
        for n in self.inv:
            self.order *= n
        # strides for mixed-radix flat index
        self.stride = [1] * self.k
        for i in range(self.k - 2, -1, -1):
            self.stride[i] = self.stride[i + 1] * self.inv[i + 1]

    def idx(self, coords):
        s = 0
        for c, st in zip(coords, self.stride):
            s += c * st
        return s

    def coords(self, idx):
        out = []
        for i in range(self.k):
            out.append((idx // self.stride[i]) % self.inv[i])
        return tuple(out)

    def add_idx(self, x, y):
        cx = self.coords(x)
        cy = self.coords(y)
        cz = tuple((a + b) % n for a, b, n in zip(cx, cy, self.inv))
        return self.idx(cz)

    def d_star(self):
        return sum(n - 1 for n in self.inv)

    def M(self):
        return 1 + self.d_star()

    def build_add_tables(self):
        """Precompute, for each g, a tuple perm where perm[x] = x +_G g.
        Used to translate the bitmask fast."""
        n = self.order
        self.perm = [None] * n
        for g in range(n):
            p = [0] * n
            for x in range(n):
                p[x] = self.add_idx(x, g)
            self.perm[g] = tuple(p)

    def build_shift_masks(self):
        """For the bitset translate we need, for each g, the ability to compute
        translate(S,g) = OR over set bits x of bit(x+g).
        We precompute perm (index map). translate uses per-bit remap.
        For speed on the hot path we instead precompute, for each g, a list
        of (src_bit, dst_bit) is too slow; we use the vectorized approach in
        translate_mask below via precomputed perm and a fallback.
        """
        pass


# ----------------------------------------------------------------------
# Zero-sum-free tester (bitset DP)
# ----------------------------------------------------------------------

def translate_mask(mask, perm, n):
    """Return the bitmask of { perm[x] : bit x set in mask }.
    perm is a tuple of length n. This is the group-addition of the whole
    reachable set by a fixed element g (perm = translate-by-g)."""
    out = 0
    m = mask
    while m:
        low = m & (-m)
        x = low.bit_length() - 1
        out |= (1 << perm[x])
        m ^= low
    return out


def is_zero_sum_free(seq, G):
    """seq: list of group-element indices. Return True iff no nonempty
    subsequence sums to the identity (index 0)."""
    S = 0  # bitmask of reachable nonempty subset sums
    perm = G.perm
    for g in seq:
        # new sums: {g} itself, plus every existing sum + g
        add = (S >> 0)  # placeholder, replaced below
        newbits = translate_mask(S, perm[g], G.order) | (1 << g)
        S |= newbits
        if S & 1:  # bit 0 = identity reachable => a zero-sum subsequence exists
            return False
    return True


def zero_sum_free_prefix_len(seq, G):
    """Length of the longest zero-sum-free prefix of seq (how many we can add
    before identity becomes reachable)."""
    S = 0
    perm = G.perm
    for i, g in enumerate(seq):
        newbits = translate_mask(S, perm[g], G.order) | (1 << g)
        S |= newbits
        if S & 1:
            return i  # first i elements were zero-sum-free, adding this broke it
    return len(seq)


# ----------------------------------------------------------------------
# Exact D(G) by branch-and-bound search for a long zero-sum-free sequence
# ----------------------------------------------------------------------

def max_zsf_length(G, cap=None, use_canonical=True, time_budget_nodes=None):
    """Exhaustive search for the maximum length of a zero-sum-free sequence.
    Returns (max_len, witness_seq).  cap: stop as soon as a sequence of this
    length is found (used to test 'is there a length-cap ZSF sequence?').

    Search state: current sequence (multiset), current reachable-sum bitmask S.
    Canonical ordering: only append elements with index >= last appended index
    among 'fresh' choices to break the ordering symmetry of a multiset
    (a zero-sum-free sequence is a multiset; order does not matter, so we may
    assume nondecreasing index order).  Element 0 (identity) is never used.
    """
    n = G.order
    perm = G.perm
    best = [0, []]
    nodes = [0]

    # candidate elements: all nonidentity elements, ascending index
    elts = list(range(1, n))

    def recurse(S, start, depth, seq):
        nodes[0] += 1
        if time_budget_nodes is not None and nodes[0] > time_budget_nodes:
            raise TimeoutError
        if depth > best[0]:
            best[0] = depth
            best[1] = list(seq)
            if cap is not None and depth >= cap:
                raise StopIteration
        # try to extend
        for gi in range(start, len(elts)):
            g = elts[gi]
            add = translate_mask(S, perm[g], n) | (1 << g)
            newS = S | add
            if newS & 1:
                continue  # would create a zero-sum
            seq.append(g)
            # canonical: next element index >= gi (nondecreasing) => multiset
            recurse(newS, gi, depth + 1, seq)
            seq.pop()

    try:
        recurse(0, 0, 0, [])
    except StopIteration:
        pass
    except TimeoutError:
        return (best[0], best[1], nodes[0], True)  # timed out
    return (best[0], best[1], nodes[0], False)


def davenport(G, **kw):
    res = max_zsf_length(G, **kw)
    d = res[0]
    return d + 1, res  # D(G) = d(G)+1


# ----------------------------------------------------------------------
# Validation anchors
# ----------------------------------------------------------------------

def validate():
    print("=" * 70)
    print("VALIDATION: tester against known Davenport constants")
    print("=" * 70)
    ok = True

    # D(C_n) = n
    for nval in [2, 3, 5, 7, 10, 13]:
        G = Group((nval,))
        G.build_add_tables()
        D, res = davenport(G)
        exp = nval
        flag = "OK" if D == exp else "FAIL"
        if D != exp:
            ok = False
        print(f"  D(C_{nval}) = {D}  (expected {exp})  [{flag}]  nodes={res[2]}")

    # D(C_n^2) = 2n-1
    for nval in [2, 3, 4, 5]:
        G = Group((nval, nval))
        G.build_add_tables()
        D, res = davenport(G)
        exp = 2 * nval - 1
        flag = "OK" if D == exp else "FAIL"
        if D != exp:
            ok = False
        print(f"  D(C_{nval}^2) = {D}  (expected {exp})  [{flag}]  nodes={res[2]}")

    # Rank-3 p-group anchors: D(C_2^3)=4, D(C_2^2+C_4)? p-group => M(G).
    # For p-groups D(G)=M(G) (Olson). Use these as anchors.
    anchors = [
        ((2, 2, 2), 1 + 3 * 1),          # M = 1+3 = 4
        ((2, 2, 4), 1 + 1 + 1 + 3),      # M = 1+ (1+1+3) = 6
        ((3, 3, 3), 1 + 3 * 2),          # M = 1+6 = 7
        ((2, 4, 4), 1 + 1 + 3 + 3),      # M = 8  (2-group)
    ]
    for inv, exp in anchors:
        G = Group(inv)
        G.build_add_tables()
        D, res = davenport(G)
        flag = "OK" if D == exp else "FAIL"
        if D != exp:
            ok = False
        cx = "x".join(f"C{n}" for n in inv)
        print(f"  D({cx}) = {D}  (expected M(G)={exp})  [{flag}]  nodes={res[2]}")

    print()
    print("VALIDATION", "PASSED" if ok else "FAILED")
    return ok


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "validate":
        validate()
    else:
        validate()
