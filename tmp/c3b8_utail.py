#!/usr/bin/env python3
"""
C3 batch 8 — TARGET B, part 2: sign of the cumulative leaf U_x(s) on and below the window.

Fast fixed-grid version (the adaptive-quad version in tmp/c3b8_window.py was too slow:
each Cred evaluation costs a k-sum of complex-order Bessel calls).

  Cred(u,x) = sum_{k>=1} k^2 tau_x(k) F(k*A1(u), x),   A1(u) = 2 pi e^{2u}
  F(A,x)    = (A^2+9) K_{ix}(A) + 6A K'_{ix}(A),  K'_{ix}(A) = -Re K_{1+ix}(A)
  tau_x(k)  = sum_{ab=k} cos(x log(a/b))

  sign(cellDensity x u) = sign(Cred(u,x))
  sign(U_x(s))          = sign( Ured(s,x) ),
  Ured(s,x) = int_s^inf (u-s)^2 e^{5u} Cred(u,x) du

Composite Simpson on [s, umax] with a precomputed Cred grid; umax chosen so that
A1(umax) >= max(6|x|, 200), beyond which |Cred| <= 4(A1+3)^2 e^{-A1} (batch-7 compiled
bound, threshold lowered in tmp/c3b8_A2.lean) makes the tail negligible against the
printed digits.  Numerics may falsify; they never prove.
"""
import sys
from mpmath import mp, mpf, mpc, exp, log, pi, besselk, nstr

mp.dps = 30


def divisors(k):
    ds = []
    i = 1
    while i * i <= k:
        if k % i == 0:
            ds.append(i)
            if i * i != k:
                ds.append(k // i)
        i += 1
    return ds


def tau(x, k):
    s = mpf(0)
    for a in divisors(k):
        b = k // a
        s += mp.cos(x * log(mpf(a) / mpf(b)))
    return s


def F(A, x):
    K = besselk(mpc(0, x), A).real
    Kd = -besselk(mpc(1, x), A).real
    return (A**2 + 9) * K + 6 * A * Kd


def A1(u):
    return 2 * pi * exp(2 * u)


def Cred(u, x):
    a1 = A1(u)
    Kmax = int(mp.floor(abs(x) / a1)) + 35
    s = mpf(0)
    for k in range(1, Kmax + 1):
        s += mpf(k) ** 2 * tau(x, k) * F(k * a1, x)
    return s


def f12(v):
    return nstr(v, 12)


def simpson(vals, h):
    n = len(vals) - 1
    if n % 2 == 1:
        vals = vals[:-1]
        n -= 1
    s = vals[0] + vals[-1]
    for i in range(1, n):
        s += (4 if i % 2 == 1 else 2) * vals[i]
    return s * h / 3


def main():
    print("=" * 92)
    print("C3 BATCH 8 — TARGET B part 2: sign of the cumulative leaf U_x(s)")
    print(f"mpmath dps = {mp.dps};  composite Simpson on a precomputed Cred grid")
    print("=" * 92)
    sys.stdout.flush()

    xs = [mpf(0), mpf(1), mpf(10), mpf('14.134725'), mpf('21.022'), mpf(60)]
    N = 80
    bad = []

    for x in xs:
        top = log(20 * (abs(x) + 1) ** 2 / (2 * pi)) / 2      # window top u1(x)
        target = max(6 * abs(x), mpf(200))
        umax = log(target / (2 * pi)) / 2
        if umax < top:
            umax = top + mpf('0.5')
        h = umax / N
        grid = [i * h for i in range(N + 1)]
        print(f"\n--- x = {f12(x)}   u1(x) = {f12(top)}   umax = {f12(umax)} ---")
        sys.stdout.flush()
        cg = []
        for u in grid:
            cg.append(Cred(u, x))
        # report the sign pattern of Cred on the grid
        nneg = sum(1 for c in cg if c < 0)
        print(f"    Cred grid: {nneg} of {N+1} points negative;  Cred(0)={f12(cg[0])}")
        sys.stdout.flush()
        # U_x(s) for several s, integrating the SAME grid from index i0 on
        for frac in [mpf(0), mpf('0.25'), mpf('0.5'), mpf('0.75'), mpf(1)]:
            s = top * frac
            i0 = int(mp.floor(s / h))
            if i0 >= N - 2:
                continue
            sub = [(grid[i] - s) ** 2 * exp(5 * grid[i]) * cg[i] for i in range(i0, N + 1)]
            val = simpson(sub, h)
            print(f"    s={f12(s):>14}  Ured={f12(val):>18}  "
                  f"{'NEG' if val < 0 else 'POS'}")
            sys.stdout.flush()
            if val < 0:
                bad.append((x, s, val))

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  U_x(s) negative instances: {len(bad)}")
    for (x, s, v) in bad:
        print(f"    COUNTEREXAMPLE x={f12(x)} s={f12(s)} Ured={f12(v)}")
    if not bad:
        print("  no counterexample to U_x(s) >= 0 found on the tested grid")


if __name__ == "__main__":
    main()
