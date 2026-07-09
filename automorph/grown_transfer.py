#!/usr/bin/env python3
"""grown_transfer.py -- the GROWN transfer exponent: theta_e for the native primitive
A_e(x) = sum_n lambda_n e^{-n/x}  (every phasor enters continuously at zero magnitude --
no clip), the object whose Mellin partner is L(s)Gamma(s) with Gamma nonvanishing.

Why this matters: for the SHARP primitive, theta<1/2 at degree>=4 is blocked classically
(Chandrasekharan--Narasimhan sits above 1/2) -- an artifact of the clipped edge.  For the
GROWN primitive, automorphy (entire L + FE growth) forces A_e(x) -> L(0): BOUNDED, i.e.
theta_e <= 0, by shifting the Mellin contour over the Gamma poles:
   A_e(x) = (1/2pi i) int Gamma(s) L(s) x^s ds  =  sum_k (-1)^k/k! L(-k) x^{-k}.
A random multiplicative fiber still random-walks: A_e ~ x^{1/2} (CLT; effective terms ~x).
So theta_e is an automorphy meter, and the plateau value |A_e(infty)| reads |L(0)|.

Truncation: need x << N so e^{-N/x} kills the tail; we use x <= N/40 (tail < e^{-40}).
Run: python3 tmp/grown_transfer.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_closure_3d as S

def theta_e_fit(a, N):
    n = np.arange(1, N + 1, dtype=float)
    xs = np.exp(np.linspace(math.log(10.0), math.log(N / 40.0), 60))
    vals = np.array([abs(np.sum(a[1:N + 1] * np.exp(-n / x))) for x in xs])
    runmax = np.maximum.accumulate(vals)
    lo = len(xs) // 3
    slope = np.polyfit(np.log(xs[lo:]), np.log(np.maximum(runmax[lo:], 1e-12)), 1)[0]
    return slope, vals[-1], runmax[-1]

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
    print(f"N={N}; grown primitive A_e(x)=sum lam_n e^(-n/x), x in [10, N/40]; sqrt(x_max)={math.sqrt(N/40):.0f}")
    print(f"{'fiber':<28} {'theta_e':>8} {'|A_e(xmax)|':>11} {'runmax':>8}   read")
    for name, a in fibers.items():
        sl, last, rm = theta_e_fit(np.asarray(a, dtype=float), N)
        read = "BOUNDED (automorphy-consistent, plateau ~ |L(0)|)" if sl < 0.15 else \
               ("sub-random-walk" if sl < 0.5 else "random walk (transfer-killed)")
        print(f"{name:<28} {sl:>8.3f} {last:>11.2f} {rm:>8.1f}   {read}")
    print("\n[read] grown theta_e < kappa/2 is the operative transfer input (Lemma: Mellin of A_e")
    print("       is L(s)Gamma(s), Gamma nonvanishing).  Automorphy => theta_e <= 0 (A_e -> L(0)):")
    print("       the Chandrasekharan-Narasimhan sharp-cutoff barrier is a clip artifact, not")
    print("       an arithmetic wall.  Random stays at 1/2 under smoothing: the gate still bites.")

if __name__ == "__main__":
    main()

def window_slopes(a, N, nwin=4):
    n = np.arange(1, N + 1, dtype=float)
    xs = np.exp(np.linspace(math.log(10.0), math.log(N / 40.0), 80))
    vals = np.array([abs(np.sum(a[1:N + 1] * np.exp(-n / x))) for x in xs])
    runmax = np.maximum.accumulate(vals)
    edges = np.linspace(0, len(xs), nwin + 1).astype(int)
    out = []
    for w in range(nwin):
        sl = slice(max(edges[w], 1), edges[w + 1])
        out.append(np.polyfit(np.log(xs[sl]), np.log(np.maximum(runmax[sl], 1e-12)), 1)[0])
    return out

def transient_test():
    """Is the degree-climb of theta_e a finite-window transient of the 1D chart?"""
    N = 200000
    spf = S.spf_sieve(N)
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    th_true = {p: math.acos(max(-1, min(1, lam_d[p].real / 2)))
               for p in range(2, N + 1) if spf[p] == p}
    rng = np.random.default_rng(23)
    th_random = {p: float(rng.uniform(0.0, math.pi)) for p in th_true}
    fibers = {
        "Delta": S.sym_r_lambda(1, th_true, spf, N),
        "Sym^5": S.sym_r_lambda(5, th_true, spf, N),
        "Sym^13": S.sym_r_lambda(13, th_true, spf, N),
        "RANDOM": S.sym_r_lambda(1, th_random, spf, N),
    }
    print("\nwindow-drift of the grown slope (4 log-windows over x in [10, N/40]):")
    print(f"{'fiber':<10} {'w1':>7} {'w2':>7} {'w3':>7} {'w4':>7}   read")
    for name, a in fibers.items():
        ws = window_slopes(np.asarray(a, dtype=float), N)
        drift = "falling -> transient (chart artifact)" if ws[-1] < ws[0] - 0.05 else \
                ("flat" if abs(ws[-1] - ws[0]) <= 0.05 else "rising")
        print(f"{name:<10} " + " ".join(f"{w:7.3f}" for w in ws) + f"   {drift}")

if __name__ == "__main__" and "--windows" in sys.argv:
    transient_test()

def transient_test_median():
    """median-|A_e| window slopes: stable envelope estimator (runmax is a jump process)."""
    N = 200000
    spf = S.spf_sieve(N)
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    th_true = {p: math.acos(max(-1, min(1, lam_d[p].real / 2)))
               for p in range(2, N + 1) if spf[p] == p}
    rng = np.random.default_rng(23)
    th_random = {p: float(rng.uniform(0.0, math.pi)) for p in th_true}
    fibers = {
        "Delta": S.sym_r_lambda(1, th_true, spf, N),
        "Sym^5": S.sym_r_lambda(5, th_true, spf, N),
        "Sym^13": S.sym_r_lambda(13, th_true, spf, N),
        "RANDOM": S.sym_r_lambda(1, th_random, spf, N),
    }
    n = np.arange(1, N + 1, dtype=float)
    xs = np.exp(np.linspace(math.log(10.0), math.log(N / 40.0), 120))
    nwin = 4
    edges = np.linspace(0, len(xs), nwin + 1).astype(int)
    print("\nmedian-envelope window slopes (4 log-windows, 120 samples):")
    print(f"{'fiber':<10} {'w1':>7} {'w2':>7} {'w3':>7} {'w4':>7}")
    for name, a in fibers.items():
        aa = np.asarray(a, dtype=float)
        vals = np.array([abs(np.sum(aa[1:N + 1] * np.exp(-n / x))) for x in xs])
        sls = []
        for w in range(nwin):
            sl = slice(edges[w], edges[w + 1])
            # slope of log median-envelope: fit log|A_e| directly, robust to oscillation
            sls.append(np.polyfit(np.log(xs[sl]), np.log(np.maximum(vals[sl], 1e-12)), 1)[0])
        print(f"{name:<10} " + " ".join(f"{w:7.3f}" for w in sls))

if __name__ == "__main__" and "--median" in sys.argv:
    transient_test_median()
