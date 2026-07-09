#!/usr/bin/env python3
"""repair_syndrome.py -- GATE REPAIR, demonstrated end-to-end on the functional equation.

Claim under test (the harmonization/repair frame): a fiber broken in a finitely-described
(periodic) way is not a gate counterexample but a REPAIR CANDIDATE: the gate loss itself is
the syndrome; scanning per-place corrections localizes the fault, names the correction, and
repairs the fiber to gate satisfaction -- the Brauer-zero-trap pattern at the FE level, and
Part I's repair of Altug's broken clocking/windows, replayed on a broken fiber.

Setup: weight-12 anchor (Delta), theta self-duality phi(1/t) = t * phi(t) (eps=+1, the
validated Sym^1 anchor of sym_r_fe2.py), kernel g(x) = 2 x^{11/2} e^{-2 pi x}.
BREAK: swap theta_2 <-> theta_3 (the 'detuned' fiber; provably non-automorphic as-is).
REPAIR LOOP (greedy, oracle-free -- the only loss is the FE closure):
  for each prime p <= 13, grid theta'_p in [0,pi], measure FE loss; fix the best
  improvement; repeat.  Success = faults localized to exactly {2,3}, corrections land on
  the true angles, final loss returns to the true-fiber baseline.
Run: python3 tmp/repair_syndrome.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_closure_3d as S

N = 4000
TS = np.array([0.25, 0.35, 0.5, 0.7, 1.0])
PRIMES = [2, 3, 5, 7, 11, 13]

spf = S.spf_sieve(N)
lam_d, _ = FC.FAMILIES["delta"].coeff(N)
th_true = {p: math.acos(max(-1, min(1, lam_d[p].real / 2)))
           for p in range(2, N + 1) if spf[p] == p}
n = np.arange(1, N + 1, dtype=float)

def g(x):
    return 2.0 * x ** 5.5 * np.exp(-2.0 * math.pi * x)

def phi(lam, t):
    return float(np.sum(lam[1:N + 1] * g(n * t)))

def fe_loss(th):
    lam = np.asarray(S.sym_r_lambda(1, th, spf, N), dtype=float)
    tot = 0.0
    for t in TS:
        a, b = phi(lam, 1.0 / t), t * phi(lam, t)
        tot += abs(a - b) / (abs(a) + abs(b) + 1e-300)
    return tot / len(TS)

def main():
    th_bad = dict(th_true)
    th_bad[2], th_bad[3] = th_true[3], th_true[2]
    base_true = fe_loss(th_true)
    base_bad = fe_loss(th_bad)
    print(f"FE loss, true fiber   : {base_true:.3e}   (truncation baseline)")
    print(f"FE loss, broken fiber : {base_bad:.3e}   (theta_2 <-> theta_3 swapped)")
    grid = np.linspace(0.0, math.pi, 121)
    th = dict(th_bad)
    for rnd in range(1, 4):
        print(f"\nround {rnd}: per-place syndrome scan (loss drop if theta'_p replaces current)")
        best = None
        for p in PRIMES:
            cur = th[p]
            losses = []
            for tp in grid:
                th[p] = float(tp)
                losses.append(fe_loss(th))
            th[p] = cur
            losses = np.array(losses)
            i = int(np.argmin(losses))
            drop = fe_loss(th) - losses[i]
            tag = f"p={p:>2}: argmin theta'={grid[i]:.3f} (true {th_true[p]:.3f}, current {cur:.3f})  min-loss={losses[i]:.3e}  drop={drop:.3e}"
            print("   " + tag)
            if best is None or losses[i] < best[1]:
                best = (p, losses[i], float(grid[i]), drop)
        p, ml, tp, drop = best
        if drop < 1e-12:
            print("   -> no place improves: repair converged")
            break
        th[p] = tp
        print(f"   -> REPAIR: place p={p} reset to {tp:.3f}; loss now {fe_loss(th):.3e}")
    final = fe_loss(th)
    print(f"\nfinal loss {final:.3e} vs true baseline {base_true:.3e}")
    errs = {p: abs(th[p] - th_true[p]) for p in PRIMES}
    print("angle errors vs true:", {p: f"{e:.4f}" for p, e in errs.items()})
    ok = final < 10 * base_true and all(errs[p] < 0.03 for p in PRIMES)
    print("VERDICT:", "REPAIRED -- fault localized to {2,3}, corrections landed on the true"
          " angles, gate restored (syndrome-driven, oracle-free)." if ok else
          "NOT fully repaired at this grid/truncation -- report as measured.")

if __name__ == "__main__":
    main()
