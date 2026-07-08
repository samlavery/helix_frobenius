#!/usr/bin/env python3
"""transfer_exponent.py -- measure the transfer exponent theta_W: the growth exponent of
the RAW coefficient primitive A(x) = sum_{n<=x} a_n.

THE TRANSFER, PROVED (sub-random-walk continuation): if A(x) << x^theta then
sum a_n n^{-s} is analytic on Re s > theta (partial summation, classical); the dual
primitive is conj(A), same theta; so BOTH completed readouts are analytic on the strip
theta < Re s < kappa - theta, which contains the weld axis iff  theta < kappa/2.
The per-fiber arithmetic input of the chain is therefore the single exponent condition
   theta_W < 1/2   ("the fiber beats the random walk"),
false for random multiplicative systems (LIL: theta = 1/2 exactly), true for automorphic
fibers (classically theta <= 1/3 for r<=4 via Voronoi; measured here for the open r).

Fit: theta_hat = slope of log(running max |A|) vs log x over the top two decades.
Run: python3 tmp/transfer_exponent.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_closure_3d as S

def theta_fit(a, N):
    A = np.cumsum(a[1:N + 1])
    absA = np.abs(A)
    runmax = np.maximum.accumulate(absA)
    x = np.arange(1, N + 1, dtype=float)
    lo = N // 100                          # top two decades
    sl = slice(lo, N)
    coef = np.polyfit(np.log(x[sl]), np.log(np.maximum(runmax[sl], 1e-12)), 1)[0]
    return coef, absA[-1], runmax[-1]

def main():
    N = 200000
    spf = S.spf_sieve(N)
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    th_true = {p: math.acos(max(-1, min(1, lam_d[p].real / 2)))
               for p in range(2, N + 1) if spf[p] == p}
    th_detuned = dict(th_true)
    th_detuned[2], th_detuned[3] = th_true[3], th_true[2]
    rng = np.random.default_rng(23)
    th_random = {p: float(rng.uniform(0.0, math.pi)) for p in th_true}

    fibers = {
        "Delta (automorphic)": S.sym_r_lambda(1, th_true, spf, N),
        "Sym^5 Delta (open r)": S.sym_r_lambda(5, th_true, spf, N),
        "Sym^13 Delta (open r)": S.sym_r_lambda(13, th_true, spf, N),
        "Delta DETUNED (th2<->th3)": S.sym_r_lambda(1, th_detuned, spf, N),
        "RANDOM angles": S.sym_r_lambda(1, th_random, spf, N),
    }
    print(f"N={N}, sqrt(N)={math.sqrt(N):.0f}.  theta_hat = slope of log(runmax|A|) vs log x (top 2 decades)")
    print(f"{'fiber':<28} {'theta_hat':>9} {'|A(N)|':>9} {'runmax|A|':>10}  {'beats sqrt? (theta<1/2)':>24}")
    for name, a in fibers.items():
        th, aN, rm = theta_fit(np.asarray(a, dtype=float), N)
        verdict = "YES" if th < 0.5 else "NO"
        print(f"{name:<28} {th:>9.3f} {aN:>9.1f} {rm:>10.1f}  {verdict:>24}")
    print("\n[read] theta<1/2 => both completed readouts analytic on a strip containing the weld")
    print("       axis (the transfer, proved by partial summation); theta=1/2 (random walk) =>")
    print("       the co-convergence gap never closes. The chain's per-fiber arithmetic input")
    print("       is exactly this exponent.")

if __name__ == "__main__":
    main()
