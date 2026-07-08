#!/usr/bin/env python3
"""detuned_closure_control.py -- does the adapted cell closure detect automorphy?

The 'can we live without Poisson' discriminator.  Given two-sided continuation, the FE
reduces to axis phase-lock (the standing wave); the arithmetic bill is paid by either
(A) continuation itself -- if the adapted closure FAILS on a non-automorphic fiber, cell
    closure is an automorphy detector and carries the arithmetic; or
(B) axis reality -- if the adapted closure SUCCEEDS on a non-automorphic fiber, closure is
    arithmetic-blind and the standing wave alone carries the load.

CONTROL FIBER: Delta's Satake angles with theta_2 <-> theta_3 swapped, multiplicatively
rebuilt ("detuned Delta") -- same duality-stable class, same growth, same generator suite,
almost surely not automorphic (coefficient swap destroys modularity).
Also: a fully random-angle fiber (theta_p ~ U(0,pi), Sato-Tate-free), same class.

Run the SAME native-growth four-generator forcing as the true fibers (30/30 there).
Run: python3 tmp/detuned_closure_control.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_closure_3d as S
from forcible_closure import (omega_sieve, omega_distinct_sieve, theta_sieve,
                              per_cell_force_grown)

def main():
    N = 200000
    spf = S.spf_sieve(N)
    Om = omega_sieve(spf, N)
    om = omega_distinct_sieve(spf, N)
    logn = np.log(np.arange(1, N + 1, dtype=float))
    logn = np.concatenate([[0.0], logn])[:N + 1]
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    th_true = {p: math.acos(max(-1, min(1, lam_d[p].real / 2)))
               for p in range(2, N + 1) if spf[p] == p}

    th_detuned = dict(th_true)
    th_detuned[2], th_detuned[3] = th_true[3], th_true[2]   # swap two local angles

    rng = np.random.default_rng(23)
    th_random = {p: float(rng.uniform(0.0, math.pi)) for p in th_true}

    fibers = {
        "Delta TRUE (automorphic anchor)": th_true,
        "Delta DETUNED (theta_2<->theta_3)": th_detuned,
        "RANDOM angles (Sato-Tate-free)": th_random,
    }
    print(f"N={N}; native growth cells, four generators (Omega, omega, log n, Theta[fiber])")
    print(f"{'fiber':<36} {'med |D_C|':>10} {'max rel':>10} {'max|x|':>8} {'fails':>6}  resistant cells")
    for name, th in fibers.items():
        a = S.sym_r_lambda(1, th, spf, N)
        Th = theta_sieve(spf, th, N)
        med, mxr, wm, nxt, nf, fi = per_cell_force_grown(a, [Om, om, logn, Th], N)
        print(f"{name:<36} {med:>10.2e} {mxr:>10.2e} {wm:>8.2f} {nf:>6d}  {fi}")
    print("\n[read] TRUE must reproduce 30/30 (harness sanity).  If DETUNED/RANDOM also close")
    print("       30/30, adapted closure is arithmetic-blind: continuation is cheap on this")
    print("       class and the FE bill is paid entirely by axis reality (the standing wave).")
    print("       If they resist, cell closure itself is the automorphy detector.")

if __name__ == "__main__":
    main()
