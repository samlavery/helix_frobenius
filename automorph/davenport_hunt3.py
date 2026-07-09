#!/usr/bin/env python3
"""
Fast numpy hunter for rank-3 Davenport counterexamples (v3).
Combines: (a) structured-construction families adapted from known counterexamples,
          (b) fast randomized extend-repair local search on the numpy machine.
A counterexample = ZSF multiset of size d*(G)+1.
"""
import sys, time, random
import numpy as np
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_fast import FastG


class FastHunt:
    def __init__(self, inv):
        self.FG = FastG(inv)
        self.G = self.FG.G
        self.n = self.FG.n
        self.inv = tuple(inv)
        self.perm = self.FG.perm
        self.M = self.FG.M
        self.dstar = self.FG.dstar
        # neg index
        self.neg = np.array(
            [self.G.idx(tuple((-c) % m for c, m in zip(self.G.coords(g), inv)))
             for g in range(self.n)], dtype=np.int64)

    def reach_mask(self, elems):
        m = np.zeros(self.n, dtype=bool)
        for g in elems:
            tr = np.zeros(self.n, dtype=bool)
            tr[self.perm[g][m]] = True
            m |= tr
            m[g] = True
        return m

    def is_zsf(self, elems):
        return not self.reach_mask(elems)[0]

    def addable_set(self, mask):
        """elements g s.t. adding g keeps ZSF: g addable iff not mask[neg[g]]."""
        idx = np.where(~mask[self.neg])[0]
        return idx[idx != 0]  # exclude identity

    def greedy_extend(self, elems, mask, rng, target):
        """Extend a ZSF multiset greedily/randomly until size target or stuck."""
        elems = list(elems)
        m = mask.copy()
        while len(elems) < target:
            add = self.addable_set(m)
            if len(add) == 0:
                break
            g = int(rng.choice(add))
            tr = np.zeros(self.n, dtype=bool)
            tr[self.perm[g][m]] = True
            m |= tr; m[g] = True
            elems.append(g)
        return elems, m

    # ---- structured families ----
    def basis(self):
        e = [self.G.idx(tuple(1 if j == i else 0 for j in range(3)))
             for i in range(3)]
        return e

    def structured_seeds(self):
        """Yield structured ZSF multisets to seed local search, adapted from
        known counterexample shapes."""
        G = self.G; inv = self.inv
        n1, n2, n3 = inv
        e1, e2, e3 = self.basis()
        seeds = []
        # (0) canonical extremal (size d*)
        seeds.append([e1]*(n1-1) + [e2]*(n2-1) + [e3]*(n3-1))
        # (1) GS/GLP-style: replace some basis multiplicity with 'diagonal' cosets.
        #     Try e1+e2, e1+e3, e2+e3 combos plus reduced basis powers.
        d12 = G.add_idx(e1, e2); d13 = G.add_idx(e1, e3); d23 = G.add_idx(e2, e3)
        d123 = G.add_idx(d12, e3)
        seeds.append([d12]*(min(n1,n2)-1) + [e3]*(n3-1) + [e2]*(max(0,n2-n1)))
        seeds.append([e1]*(n1-1) + [d23]*(min(n2,n3)-1) + [e3]*(max(0,n3-n2)))
        seeds.append([d13]*(min(n1,n3)-1) + [e2]*(n2-1))
        seeds.append([d123]*(min(inv)-1) + [e2]*(n2-1) + [e3]*(n3-1))
        # (2) 'half' shifts (GLP used (n+-1)/2 multiples on odd-order factors)
        if n3 % 2 == 1:
            h = (n3 + 1)//2
            g = G.idx((0,0,h))
            seeds.append([e1]*(n1-1)+[e2]*(n2-1)+[g]*(n3-1))
        # keep only the ZSF ones, trimmed to a ZSF prefix
        out = []
        for s in seeds:
            # trim to longest ZSF prefix by greedy testing
            m = np.zeros(self.n, dtype=bool); keep=[]
            for g in s:
                if g == 0: continue
                if m[self.neg[g]]:  # would hit zero
                    continue
                tr=np.zeros(self.n,dtype=bool); tr[self.perm[g][m]]=True
                m|=tr; m[g]=True; keep.append(g)
            if keep:
                out.append(keep)
        return out

    def hunt(self, restarts=200, budget_swaps=400, seed=0, verbose=False, time_limit=None):
        rng = np.random.default_rng(seed)
        t0 = time.time()
        best = (0, [])
        target = self.M

        # 1) structured seeds, each greedily extended
        for s in self.structured_seeds():
            m = self.reach_mask(s)
            e2, m2 = self.greedy_extend(s, m, rng, target)
            if len(e2) > best[0]:
                best = (len(e2), e2)
                if verbose: print(f"  struct seed -> {len(e2)}/{target}")
                if len(e2) >= target: return best

        # 2) random restarts of extend-repair
        for r in range(restarts):
            if time_limit and time.time()-t0 > time_limit:
                break
            elems, m = self.greedy_extend([], np.zeros(self.n, dtype=bool), rng, target)
            if len(elems) > best[0]:
                best = (len(elems), list(elems))
                if verbose: print(f"  [r{r}] greedy {len(elems)}/{target}")
                if len(elems) >= target: return best
            # repair: swap out random elements to try to open an extra slot
            for _ in range(budget_swaps):
                if len(elems) < target:
                    elems, m = self.greedy_extend(elems, m, rng, target)
                    if len(elems) >= target:
                        if self.is_zsf(elems): return (target, elems)
                if not elems: break
                i = rng.integers(len(elems))
                trial = elems[:i] + elems[i+1:]
                m = self.reach_mask(trial)
                add = self.addable_set(m)
                # prefer adding an element different from removed
                if len(add):
                    g = int(rng.choice(add))
                    tr=np.zeros(self.n,dtype=bool); tr[self.perm[g][m]]=True
                    m|=tr; m[g]=True; trial.append(g)
                elems = trial
                if len(elems) > best[0]:
                    best=(len(elems), list(elems))
                    if len(elems)>=target and self.is_zsf(elems):
                        return (target, elems)
        return best


def run(inv, restarts=300, seed=1, verbose=True, time_limit=60):
    H = FastHunt(inv)
    t0=time.time()
    best_size, best = H.hunt(restarts=restarts, seed=seed, verbose=verbose, time_limit=time_limit)
    ce = best_size >= H.M
    print(f"{inv}: d*={H.dstar} M={H.M} -> best ZSF size {best_size}/{H.M}  "
          f"({time.time()-t0:.1f}s)  {'*** COUNTEREXAMPLE ***' if ce else 'no CE (d>= '+str(best_size)+')'}")
    if ce:
        print("  witness:", best)
        # sanity: verify
        print("  verify is_zsf:", H.is_zsf(best), "len", len(best))
    return best_size, best, H.M


if __name__ == "__main__":
    inv = tuple(int(x) for x in sys.argv[1].split(",")) if len(sys.argv)>1 else (6,6,6)
    tl = int(sys.argv[2]) if len(sys.argv)>2 else 60
    run(inv, time_limit=tl)
