#!/usr/bin/env python3
"""
dual_closure_test.py -- the Part III binary, on Altug's ACTUAL geometric transform.

Object (Altug I Thm 4.2 = III Thm 1.1 master formula), assembled by poisson_dual.py:
  (4)+Sum() = (p^{k/2}/2) sum_-+ sum_f (1/f^3) sum_l (1/l^2) sum_{xi in Z} Kl_{l,f}(xi,-+p^k) A_{l,f}(xi)
The xi!=0 terms are the piece Altug can only BOUND (Prop 5.2 uniform Fourier decay -> o(X)).

BINARY (owner protocol): apply nothing to L(s,pi) by substitution.  Take the REAL dual terms
dual_xi = pref*Kl*A and ask whether the xi!=0 channel CLOSES EXACTLY or only stays bounded:
  * magnitude tail  M = sum_{xi!=0} |dual_xi|      (Altug's o(X) bound; the loose size)
  * SIGNED tail     S = sum_{xi!=0} dual_xi         (the actual contribution; may cancel)
  * ratio |S|/M -> 0  AND |S| -> floor as xi_max grows  ==>  EXACT CLOSURE (clock cancels),
    Altug's bound is loose and the xi!=0 channel contributes ~0, not just o(X).
  * |S| ~ M, not falling  ==>  only bounded, no exact closure.
Also the TOTAL signed sum T = dual_0 + S: for the standard rep (r=1) L(s,std) has no pole,
so T should sit at the floor (residue 0) -- and we test whether that is achieved by EXACT
xi!=0 cancellation (S->0) with dual_0 already ~0 (oddness of U_1), i.e. a genuine closure.

Standard rep r=1 FIRST (Altug III is the standard case); r=0 anchor; r=2 as control.
Live output: tmp/dual_closure_results.txt
Run: python3 tmp/dual_closure_test.py
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poisson_dual as PD

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dual_closure_results.txt")


def measure(r, p, k, sign, xi_max, fmax=2, lmax=3, nx=500):
    prof = PD.dual_profile(r, p=p, k=k, sign=sign, fmax=fmax, lmax=lmax, xi_max=xi_max, nx=nx)
    dual0 = prof.get(0, 0j)
    signed_tail = sum(v for xi, v in prof.items() if xi != 0)
    mag_tail = sum(abs(v) for xi, v in prof.items() if xi != 0)
    total = dual0 + signed_tail
    return dual0, signed_tail, mag_tail, total


def main():
    f = open(OUT, "w")

    def emit(s=""):
        print(s, flush=True)
        f.write(s + "\n")
        f.flush()

    t0 = time.time()
    emit("Part III binary: xi!=0 channel -- EXACT CLOSURE (signed cancels to floor) vs o(X) bound")
    emit("real master-formula dual terms dual_xi = pref*Kl_{l,f}(xi)*A_{l,f}(xi); p=2,k=1, elliptic branch")
    emit("=" * 90)
    emit(f"{'r':>3} {'xi_max':>7} {'|dual_0|':>12} {'|signed tail S|':>16} "
         f"{'mag tail M':>12} {'|S|/M':>9} {'|total T|':>12}")
    for r in (0, 1, 2):
        prev = None
        for xi_max in (10, 20, 40, 80):
            d0, S, M, T = measure(r, 2, 1, -1, xi_max)
            ratio = abs(S) / M if M > 0 else float("nan")
            emit(f"{r:>3} {xi_max:>7} {abs(d0):>12.3e} {abs(S):>16.3e} "
                 f"{M:>12.3e} {ratio:>9.4f} {abs(T):>12.3e}")
            prev = (abs(S), abs(T))
        # verdict per r
        emit(f"    -> r={r}: as xi_max grows, |S| {'FALLS to floor (exact closure)' if prev and prev[0] < 1e-6 else 'stays O(mag) -> only bounded' if ratio > 0.3 else 'partially cancels (|S|/M small) -- closure candidate'}")
        emit("")
    emit(f"[done] {time.time()-t0:.0f}s -- results in {OUT}")
    f.close()


if __name__ == "__main__":
    main()
