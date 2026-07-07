#!/usr/bin/env python3
"""
forcible_closure.py -- test the per-crossing forcible-closure reframe of A1.

CLAIM under test: the readout-preserving chart-conversion warp omega(n)=beta^{Omega(n)}
(beta a unit-modulus scalar, Omega(n)=# prime factors with multiplicity -- a LEGITIMATE
completely-multiplicative unit-modulus warp, NOT arbitrary per-term phases) delivers what
A1's residual extinction needs, for CUSPIDAL fibers:
  (E) ENTIRENESS  = DC mode -> 0 : |A(X)|/X -> 0, A(X)=sum_{n<=X} a_n omega(n).
  (B) BOUNDEDNESS = warped primitive controlled : |A(X)| = O(X^{1/2+eps}).
and whether a PER-CELL adapted beta (1 param) or (beta, vertical-shift) (2 param) can
FORCE the per-cell residual D_C toward zero (controllability).

We test Delta (cuspidal, entireness CLASSICALLY known -> baseline/consistency) and the
OPEN cases Sym^5, Sym^13 (entireness of L(Sym^r Delta) not classical for r>=5).
The warp is readout-preserving: A(X) O(1)/o(X) is the warped-Abel primitive; the readout
folds omega back through the kernel. If (E)+(B) hold for the open Sym^r, the warp mechanism
gives residual extinction; per-cell forcing is the constructive strengthening.
Run: python3 tmp/forcible_closure.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_closure_3d as S

def omega_sieve(spf, N):
    Om = np.zeros(N + 1, dtype=np.int64)
    for n in range(2, N + 1):
        Om[n] = Om[n // int(spf[n])] + 1
    return Om

def global_warp(a, Om, logn, N, theta):
    """A(X)=sum a_n beta^{Omega(n)}, beta=e^{i theta}; return DC=|A(N)|/N, growth exponent."""
    w = np.exp(1j * theta * Om[1:N + 1])
    A = np.cumsum(a[1:N + 1] * w)
    X = np.arange(1, N + 1)
    dc = abs(A[-1]) / N
    tail = slice(N // 5, N)
    expo = np.polyfit(np.log(X[tail]), np.log(np.maximum(np.abs(A[tail]), 1e-9)), 1)[0]
    return dc, abs(A[-1]), expo

def per_cell_force(a, Om, logn, N, ncells=40, npar=1):
    """partition [1,N] into ncells; per cell minimize |D_C| over the warp params.
    npar=1: theta (winding).  npar=2: (theta, phi) with extra factor e^{i phi log n}."""
    edges = np.linspace(1, N, ncells + 1).astype(int)
    grid = np.linspace(0, 2 * math.pi, 360, endpoint=False)
    rg, rf = [], []
    for c in range(ncells):
        lo, hi = edges[c], edges[c + 1]
        ac = a[lo:hi]; Oc = Om[lo:hi]; Lc = logn[lo:hi]
        Dglob = abs(np.sum(ac * np.exp(1j * (math.pi / 3) * Oc)))
        if npar == 1:
            Dv = np.array([abs(np.sum(ac * np.exp(1j * t * Oc))) for t in grid])
            Df = Dv.min()
        else:
            phis = np.linspace(-0.5, 0.5, 41)
            best = np.inf
            for t in grid[::3]:
                base = ac * np.exp(1j * t * Oc)
                for ph in phis:
                    v = abs(np.sum(base * np.exp(1j * ph * Lc)))
                    if v < best:
                        best = v
            Df = best
        rg.append(Dglob); rf.append(Df)
    return np.median(rg), np.median(rf), math.sqrt(N / ncells)

def main():
    N = 200000
    spf = S.spf_sieve(N)
    Om = omega_sieve(spf, N)
    logn = np.log(np.arange(1, N + 1, dtype=float))
    logn = np.concatenate([[0.0], logn])[:N + 1]
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    th_d = {p: math.acos(max(-1, min(1, lam_d[p].real / 2))) for p in range(2, N + 1) if spf[p] == p}

    fibers = {
        "Delta (cuspidal, entire KNOWN)": np.array([lam_d[n].real for n in range(N + 1)]),
        "Sym^5 Delta (r>=5 OPEN)": S.sym_r_lambda(5, th_d, spf, N),
        "Sym^13 Delta (OPEN)": S.sym_r_lambda(13, th_d, spf, N),
    }
    print(f"N={N}, sqrt(N)={math.sqrt(N):.0f}; warp omega(n)=beta^Omega(n), beta=e^(i*pi/3)")
    print("=" * 84)
    print(f"{'fiber':<34} {'|A|/N unwarp':>12} {'|A|/N warp':>11} {'growth warp':>11}")
    for name, a in fibers.items():
        dc0, _, _ = global_warp(a, Om, logn, N, 0.0)
        dcw, Aw, ew = global_warp(a, Om, logn, N, math.pi / 3)
        print(f"{name:<34} {dc0:>12.2e} {dcw:>11.2e} {ew:>11.3f}")
    print("\n[read] entireness (E): |A|/N -> 0 (DC mode dies); boundedness (B): growth exp <~ 0.5-0.6.")
    print("       If warp gives (E)+(B) on the OPEN Sym^r, the readout-preserving warp delivers")
    print("       residual extinction where the raw projection did not.")

    print("\nper-cell forcing (adapt warp params per cell to close D_C):")
    print(f"{'fiber':<34} {'|D_C| glob':>11} {'1-param':>10} {'2-param':>10} {'sqrt(cell)':>11}")
    for name, a in fibers.items():
        g, f1, sc = per_cell_force(a, Om, logn, N, npar=1)
        _, f2, _ = per_cell_force(a, Om, logn, N, npar=2)
        print(f"{name:<34} {g:>11.2e} {f1:>10.2e} {f2:>10.2e} {sc:>11.0f}")
    print("\n[read] 1-param cannot zero a complex residual (2 real eqns, 1 unknown); 2-param should")
    print("       drive |D_C| far below the sqrt(cell) noise floor -> per-cell forcing is real.")

if __name__ == "__main__":
    main()
