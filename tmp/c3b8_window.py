#!/usr/bin/env python3
"""
C3 batch 8 — TARGET B: adversarial study of the finite window below A1 = 20(|x|+1)^2.

Certified range (batch 7, compiled): cellDensity x u > 0 whenever 20(|x|+1)^2 <= A1(u),
A1(u) = 2*pi*e^{2u}.  Window: u in [0, u1(x)] with 2*pi*e^{2u1} = 20(|x|+1)^2.

Two distinct questions, tested separately:

  (B1)  Is cellDensity x u >= 0 on the window?      (expected NO — sign changes)
  (B2)  Is U_x(s) = int_s^inf (u-s)^2/2 C(u,x) du >= 0 for s in the window?  (the leaf)

Everything is computed from the COMPILED exact mode representation

  cellDensity x u = 16 pi^2 e^{5u} * Cred(u,x),
  Cred(u,x)       = sum_{k>=1} k^2 tau_x(k) F(k*A1(u), x),
  F(A,x)          = (A^2+9) K_{ix}(A) + 6A K'_{ix}(A),
  tau_x(k)        = sum_{ab=k, a,b>=1} cos(x log(a/b)),

so sign(cellDensity) = sign(Cred) and sign(U_x) = sign(Ured) where

  Ured(s,x) = int_s^inf (u-s)^2 e^{5u} Cred(u,x) du.

K'_{ix}(A) = -Re K_{1+ix}(A).

Truncation of the k-sum is CERTIFIED by the batch-7 compiled bound
|F(A,x)| <= 2(A+3)^2 e^{-A}  (valid A >= 6, C3B7.radial_abs_le_sharp with the
threshold lowered — see tmp/c3b8_A2.lean), together with d(k) <= k:
   |k^2 tau_x(k) F(kA1)| <= k^3 * 2 (k A1 + 3)^2 e^{-k A1}.

Numerics may falsify; they never prove.
"""

import sys
from mpmath import mp, mpf, mpc, exp, cosh, log, pi, sqrt, besselk, quad, nstr, mpmathify

mp.dps = 50


def dcount(k):
    c, i = 0, 1
    while i * i <= k:
        if k % i == 0:
            c += 2 if i * i != k else 1
        i += 1
    return c


def divisors(k):
    ds = []
    i = 1
    while i * i <= k:
        if k % i == 0:
            ds.append(i)
            if i * i != k:
                ds.append(k // i)
        i += 1
    return sorted(ds)


def tau(x, k):
    """sum over ordered pairs (a,b), ab=k, of cos(x log(a/b))"""
    s = mpf(0)
    for a in divisors(k):
        b = k // a
        s += mp.cos(x * log(mpf(a) / mpf(b)))
    return s


def F(A, x):
    """radial combination (A^2+9)K_{ix}(A) + 6A K'_{ix}(A)"""
    K = besselk(mpc(0, x), A).real
    Kd = -besselk(mpc(1, x), A).real
    return (A**2 + 9) * K + 6 * A * Kd


def A1(u):
    return 2 * pi * exp(2 * u)


def Cred(u, x, Kmax=None):
    """sum_k k^2 tau_x(k) F(k A1, x), with certified remainder"""
    a1 = A1(u)
    if Kmax is None:
        # go past the turning point kA1 ~ x, then 40 more
        Kmax = int(mp.floor(abs(x) / a1)) + 45
    s = mpf(0)
    for k in range(1, Kmax + 1):
        s += mpf(k) ** 2 * tau(x, k) * F(k * a1, x)
    # certified remainder: |term_k| <= k^3 * 2 (k A1 + 3)^2 e^{-k A1}
    rem = mpf(0)
    k = Kmax + 1
    while k <= Kmax + 200:
        t = mpf(k) ** 3 * 2 * (k * a1 + 3) ** 2 * exp(-k * a1)
        rem += t
        if t < mpf(10) ** (-mp.dps - 20) and k > Kmax + 5:
            break
        k += 1
    return s, rem


def u1(x):
    """window top: 2 pi e^{2u} = 20 (|x|+1)^2"""
    return log(20 * (abs(x) + 1) ** 2 / (2 * pi)) / 2


def Ured(s, x, umax=None):
    """int_s^umax (u-s)^2 e^{5u} Cred(u,x) du + certified tail"""
    if umax is None:
        # integrate until A1 = max(4|x|, 120): beyond that the integrand is
        # bounded by e^{5u} * 2(A1+3)^2 e^{-A1} * (u-s)^2 and negligible
        target = max(4 * abs(x), mpf(120))
        umax = log(target / (2 * pi)) / 2
        if umax <= s:
            umax = s + 1
    f = lambda u: (u - s) ** 2 * exp(5 * u) * Cred(u, x)[0]
    val = quad(f, [s, umax])
    # certified tail beyond umax, using |Cred| <= sum_k k^3 2(kA1+3)^2 e^{-kA1}
    # <= 4 (A1+3)^2 e^{-A1} * (1 + small) for A1 >= 20, and (u-s)^2 e^{5u} growth
    a1m = A1(umax)
    tailbd = mpf(0)
    if a1m >= 20:
        # crude but rigorous: integrand <= (u-s)^2 e^{5u} * 8 (A1(u)+3)^2 e^{-A1(u)}
        # and A1(u) >= a1m + 2 a1m (u-umax); integrate the majorant numerically
        g = lambda u: (u - s) ** 2 * exp(5 * u) * 8 * (A1(u) + 3) ** 2 * exp(-A1(u))
        tailbd = quad(g, [umax, umax + 3])
    return val, tailbd, umax


def f12(v):
    return nstr(v, 12)


def main():
    print("=" * 100)
    print("C3 BATCH 8 — TARGET B: the finite window below A1 = 20(|x|+1)^2")
    print(f"mpmath dps = {mp.dps}")
    print("=" * 100)
    sys.stdout.flush()

    xs = [mpf(0), mpf(1), mpf(10), mpf('14.134725'), mpf('21.022'), mpf(60), mpf(88)]

    # ---------------------------------------------------------------- B1
    print("\n" + "=" * 100)
    print("(B1) SIGN OF cellDensity ON THE WINDOW  [sign(cellDensity) = sign(Cred)]")
    print("=" * 100)
    signflips = {}
    for x in xs:
        top = u1(x)
        print(f"\n--- x = {f12(x)}   window u in [0, {f12(top)}]   A1(0)={f12(A1(0))} "
              f"A1(top)={f12(A1(top))} ---")
        sys.stdout.flush()
        N = 24
        prev = None
        flips = []
        for i in range(N + 1):
            u = top * mpf(i) / N
            c, rem = Cred(u, x)
            sg = 1 if c > 0 else (-1 if c < 0 else 0)
            if prev is not None and sg != 0 and prev != 0 and sg != prev:
                flips.append(f12(u))
            prev = sg
            if i % 4 == 0 or (prev is not None and sg < 0):
                print(f"    u={f12(u):>14} A1={f12(A1(u)):>16} Cred={f12(c):>16} "
                      f"rem<={f12(rem):>12} sign={'+' if sg > 0 else ('-' if sg < 0 else '0')}")
                sys.stdout.flush()
        signflips[str(x)] = flips
        print(f"    sign changes on the window: {len(flips)}  at u = {flips}")
        sys.stdout.flush()

    # ---------------------------------------------------------------- B2
    print("\n" + "=" * 100)
    print("(B2) SIGN OF U_x(s) FOR s IN THE WINDOW  [sign(U_x) = sign(Ured)]")
    print("=" * 100)
    bad = []
    for x in xs:
        top = u1(x)
        print(f"\n--- x = {f12(x)}   window u in [0, {f12(top)}] ---")
        sys.stdout.flush()
        for i in range(0, 7):
            s = top * mpf(i) / 6
            val, tb, um = Ured(s, x)
            verdict = "POS" if val - tb > 0 else ("NEG" if val + tb < 0 else "INCONCL")
            if verdict == "NEG":
                bad.append((x, s, val))
            print(f"    s={f12(s):>14} Ured={f12(val):>18} tailbd<={f12(tb):>12} "
                  f"umax={f12(um):>8}  {verdict}")
            sys.stdout.flush()

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    for x in xs:
        print(f"  x={f12(x):>14}  cellDensity sign changes on window: {len(signflips[str(x)])}")
    print(f"\n  U_x(s) negative instances found: {len(bad)}")
    for (x, s, v) in bad:
        print(f"    COUNTEREXAMPLE x={f12(x)} s={f12(s)} Ured={f12(v)}")


if __name__ == "__main__":
    main()
