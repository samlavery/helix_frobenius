#!/usr/bin/env python3
"""Implementation B, part 2: crossing point, Delta/S robustness, growth law,
and the analytic strip-failure of the Montgomery-Taylor kernel itself."""
import numpy as np
import sys
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")
from att034b_stripB import solveB, audit, MT


def sec(t):
    print("\n" + "=" * 78 + f"\n{t}\n" + "=" * 78, flush=True)


if __name__ == "__main__":
    job = sys.argv[1]

    if job == "cross":
        sec("crossing A*: where Z(A) = 1.3274993 (the unconditional M-T value)")
        for D in [0.04, 0.02]:
            lo, hi = 0.0, 0.5
            for _ in range(14):
                mid = 0.5 * (lo + hi)
                Z, cv, xs, st = solveB(2 * mid, Delta=D, S=2.0, dip=True)
                if Z < MT:
                    lo = mid
                else:
                    hi = mid
            print(f"  Delta={D}: A* = {0.5*(lo+hi):.5f}  (strip half-width "
                  f"W* = {lo+hi:.5f});  Selberg factor e^(-A*/4) = "
                  f"{np.exp(-0.5*(lo+hi)/4):.5f}", flush=True)

    elif job == "robust":
        sec("Delta- and S-robustness of Z(A)")
        print("   A      S    D=0.05      D=0.04      D=0.025     D=0.02  "
              "  Richardson(0.04,0.02)", flush=True)
        for A in [0.0, 0.10, 0.25, 0.50]:
            for S in [2.0, 3.0]:
                vals = {}
                for D in [0.05, 0.04, 0.025, 0.02]:
                    Z, cv, xs, st = solveB(2 * A, Delta=D, S=S, dip=True)
                    vals[D] = Z
                rich = vals[0.02] + (vals[0.02] - vals[0.04]) / 3
                print(f" {A:5.2f} {S:5.1f}  " +
                      "  ".join(f"{vals[D]:.7f}" for D in
                                [0.05, 0.04, 0.025, 0.02]) +
                      f"   {rich:.7f}", flush=True)

    elif job == "growth":
        sec("growth of Z(A) for large strip width (Z(inf) = +infinity)")
        print("     A       W        Z(A)     2-Z(A)     dZ/dW", flush=True)
        prev = None
        for A in [0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20]:
            W = 2 * A
            Z, cv, xs, st = solveB(W, Delta=0.04, S=2.0, dip=True)
            sl = "" if prev is None else f"{(Z-prev[1])/(W-prev[0]):.4f}"
            print(f"  {A:5.1f}  {W:5.1f}  {Z:10.6f}  {2-Z:9.6f}   {sl}  [{st}]",
                  flush=True)
            prev = (W, Z)

    elif job == "mt":
        sec("does the Montgomery-Taylor kernel itself satisfy strip positivity?")
        # v(s) = cos(sqrt2 s) on |s|<=1/2 ; g = |V|^2, V(u) = int v(s)e^{isu}ds
        r2 = np.sqrt(2.0)

        def V(u):
            u = np.asarray(u, dtype=complex)
            def term(a):
                # int_{-1/2}^{1/2} cos(r2 s) cos(s u) ds  = sum of sinc terms
                return np.where(np.abs(a) < 1e-9, 0.5,
                                np.sin(a / 2) / np.where(np.abs(a) < 1e-9, 1, a))
            return term(r2 + u) + term(r2 - u)

        v = np.linspace(-40, 40, 400001)
        print(f"  on the real line: min g = {np.real(V(v)**2).min():.3e} "
              f"(>=0, as it must be)", flush=True)
        print("     w        min_v Re g(v+iw)", flush=True)
        for w in [1e-4, 1e-3, 1e-2, 0.05, 0.1, 0.2, 0.5, 1.0]:
            val = np.real(V(v + 1j * w) ** 2)
            print(f"  {w:8.5f}   {val.min():+.6e}   at v = "
                  f"{v[val.argmin()]:+.4f}", flush=True)
        print("\n  ANALYTIC REASON: V is real-entire with real zeros; near a real"
              "\n  zero v0, V(v0+iw) = i w V'(v0) + O(w^2), so"
              "\n      Re g = Re[V^2] = -w^2 V'(v0)^2 + O(w^3) < 0"
              "\n  for every w != 0.  Any admissible kernel that TOUCHES zero on"
              "\n  the real line (all optimisers of this extremal problem do)"
              "\n  fails strip positivity at every strip width.", flush=True)

    elif job == "charge":
        sec("the Selberg charge and the optimised final constant")
        print("  Selberg 1946 (Titchmarsh Thm 9.19(B)): N(sigma,T) << "
              "T^{1-(sigma-1/2)/4} log T,", flush=True)
        print("  i.e. #{rho : beta-1/2 > A/log T} <= C e^{-A/4} N(T).",
              flush=True)
        print("\n     A      Z(A)      2-Z(A)     e^{-A/4}   2-Z(A)-C e^{-A/4}"
              "  (C=1)        (C=0!)", flush=True)
        best = (-9, None)
        for A in [0.0, 0.05, 0.1, 0.15, 0.2, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0,
                  12.0, 16.0, 20.0, 25.0]:
            Z, cv, xs, st = solveB(2 * A, Delta=0.04, S=2.0, dip=True)
            ch = np.exp(-A / 4)
            print(f"  {A:5.2f}  {Z:9.6f}  {2-Z:9.6f}  {ch:9.6f}   "
                  f"{2-Z-ch:+11.6f}       {2-Z:+.6f}", flush=True)
            if 2 - Z - ch > best[0]:
                best = (2 - Z - ch, A)
        print(f"\n  best over A (C=1): {best[0]:.6f} at A={best[1]}   "
              f"vs zeta23 Theorem D 0.6725007", flush=True)
