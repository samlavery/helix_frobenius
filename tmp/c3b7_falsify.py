#!/usr/bin/env python3
"""
C3 batch 7 — adversarial falsification of the batch-6 candidate

    modeBound_tail_lt_head :
      (sum_{z != (0,0)} modeBound x u z)  <  modeTerm x u (0,0)
    under  hu : max (modeThreshold x) (8 (|x|+1)^2) <= modeA 0 0 u.

Everything below is the ACTUAL inequality (not its asymptotics), at mpmath
precision, with a CERTIFIED truncation bound on the k-sum.

Unfolded objects, all divided by the common positive factor pi^2 e^{5u}:

  A1        = modeA 0 0 u = 2 pi e^{2u}            (head radial variable)
  a=n+1, b=m+1, k=ab, A_z = k A1
  C_j       = kixConst j A1 = int_0^inf e^{-A1/2} e^{(j-A1/2)w - (A1/4)w^2} dw
  head      = (A1^2+9) K_{ix}(A1) + 6 A1 K'_{ix}(A1)
  tail      = sum_{k>=2} d(k) k^2 [ (A_z^2+9) C_0 + 6 A_z C_1 ] e^{-(A_z-A1)}
  thresh(x) = max( max(8, 4(|x|+1)^2+1), 8(|x|+1)^2 )

For the batch-7 REPAIR:

  headLow   = (A1^2 - 6A1 + 6) * e^{-A1 cosh h} * h/4,   h = 1/(|x|+1)
              (the PROVABLE lower bound: C3B6.Theta.kix_zero_lower composed with
               C3B5.A2.radial_ge; no asymptotics anywhere)
  tailSharp = sum_{k>=2} d(k) k^2 * 2 (A_z+3)^2 e^{-A_z}
              (sharp majorant |radial(A)| <= 2(A+3)^2 e^{-A}, which follows from
               coshMoment j A <= e^{-A} e^{j^2/A} (1 + 4/A))

K'_{ix}(A) = -Re K_{1+ix}(A), since K_{nu-1}+K_{nu+1} = -2 K'_nu and
K_{ix-1} = K_{1-ix} = conj(K_{1+ix}) for real A>0.

No repository artifact is read.  Numerics may only falsify, never prove.
"""

import sys
from mpmath import (mp, mpf, mpc, exp, cosh, cos, sqrt, pi, quad, inf,
                    besselk, erfc, nstr)

mp.dps = 40


def divisor_count(k):
    c, i = 0, 1
    while i * i <= k:
        if k % i == 0:
            c += 2 if i * i != k else 1
        i += 1
    return c


def kixConst(j, A):
    """closed form of int_0^inf e^{-A/2} exp((j-A/2)w - (A/4)w^2) dw"""
    b = A / 4
    c = mpf(j) - A / 2
    return (exp(-A / 2) * exp(c**2 / (4 * b)) * (1 / sqrt(b))
            * (sqrt(pi) / 2) * erfc(-c / (2 * sqrt(b))))


def kixConst_quad(j, A):
    return quad(lambda w: exp(-A / 2) * exp((mpf(j) - A / 2) * w - (A / 4) * w**2),
                [0, inf])


def Kix(x, A):
    return besselk(mpc(0, x), A).real


def Kix_quad(x, A):
    return quad(lambda w: exp(-A * cosh(w)) * cos(x * w), [0, inf])


def Kixd(x, A):
    return -besselk(mpc(1, x), A).real


def Kixd_quad(x, A):
    return quad(lambda w: -cosh(w) * exp(-A * cosh(w)) * cos(x * w), [0, inf])


def head(x, A1):
    return (A1**2 + 9) * Kix(x, A1) + 6 * A1 * Kixd(x, A1)


def modeThreshold(x):
    return max(mpf(8), 4 * (abs(x) + 1)**2 + 1)


def thresh(x):
    return max(modeThreshold(x), 8 * (abs(x) + 1)**2)


def tail_batch6(x, A1, K=60):
    C0, C1 = kixConst(0, A1), kixConst(1, A1)
    M = (A1**2 + 9) * C0 + 6 * A1 * C1
    s = mpf(0)
    for k in range(2, K + 1):
        Az = k * A1
        s += divisor_count(k) * k**2 * ((Az**2 + 9) * C0 + 6 * Az * C1) * exp(-(Az - A1))
    r = exp(-A1)
    rem = mpf(K + 1)**5 * r**K * mpf('1.05') * M
    return s, rem


def tail_sharp(x, A1, K=60):
    s = mpf(0)
    for k in range(2, K + 1):
        Az = k * A1
        s += divisor_count(k) * k**2 * 2 * (Az + 3)**2 * exp(-Az)
    r = exp(-A1)
    rem = mpf(K + 1)**5 * 2 * (A1 + 3)**2 * r**(K + 1) * mpf('1.05')
    return s, rem


def head_low(x, A1):
    h = 1 / (abs(x) + 1)
    return (A1**2 - 6 * A1 + 6) * exp(-A1 * cosh(h)) * h / 4


def f(v):
    return nstr(v, 12)


def row(x, A1, label):
    hd = head(x, A1)
    t6, r6 = tail_batch6(x, A1)
    ts, rs = tail_sharp(x, A1)
    hl = head_low(x, A1)
    v6 = "HOLDS" if (t6 + r6) < hd else ("FAILS" if t6 > hd else "INCONCL")
    vS = "HOLDS" if (ts + rs) < hl else ("FAILS" if ts > hl else "INCONCL")
    print(f"  A1={f(A1):>16} [{label:>12}] head={f(hd):>14} tail6={f(t6):>14} "
          f"r6={f(t6/hd):>12} {v6:>7} | headLow={f(hl):>14} tailS={f(ts):>14} "
          f"rS={f(ts/hl):>12} {vS:>7}")
    sys.stdout.flush()
    return v6, vS, t6 / hd, ts / hl


def main():
    print("=" * 100)
    print("C3 BATCH 7 — hostile falsification of modeBound_tail_lt_head")
    print(f"mpmath dps = {mp.dps};  k-sum truncated at K=60 with certified remainder")
    print("=" * 100)
    sys.stdout.flush()

    print("\n[VALIDATION] bounded-domain checks only (no unbounded quadrature)")
    # (i) besselk(i x, A) must be real and must satisfy the modified-Bessel ODE
    #     A^2 K'' + A K' - (A^2 - x^2) K = 0, with K'' from  K'' = K + K'/A ... rearranged.
    for (xv, Av) in [(0, 8), (0, 16), (1, 10), (10, 40), ('21.022', 100), (60, 300)]:
        x, A = mpf(xv), mpf(Av)
        K = besselk(mpc(0, x), A)
        Kd = -besselk(mpc(1, x), A)
        # K'' from the ODE would be circular; instead check Wronskian-free recurrence
        # K_{nu-1} - K_{nu+1} = -2 nu K_nu / A  at nu = i x:
        lhs = besselk(mpc(0, x) - 1, A) - besselk(mpc(0, x) + 1, A)
        rhs = -2 * mpc(0, x) * besselk(mpc(0, x), A) / A
        rec = abs(lhs - rhs) / (abs(rhs) + mpf(10)**(-mp.dps))
        print(f"   x={str(xv):>8} A={Av:>5}  K={f(K.real)} (|Im|={f(abs(K.imag))})"
              f"  K'={f(Kd)}  recurrence rel-err={f(rec)}")
        sys.stdout.flush()

    print("\n[VALIDATION] kixConst closed form vs BOUNDED quadrature on [0,W], W chosen so")
    print("             the analytic tail beyond W is below 1e-30 of the value")
    for (jv, Av) in [(0, 8), (1, 8), (0, 16), (1, 32)]:
        A = mpf(Av)
        a = kixConst(jv, A)
        W = mpf(20)   # integrand <= e^{-A/2} e^{jW} e^{-(A/4)W^2}; at A>=8, W=20: e^{-800}
        b = quad(lambda w: exp(-A / 2) * exp((mpf(jv) - A / 2) * w - (A / 4) * w**2), [0, W])
        tailbd = exp(-A / 2) * exp(mpf(jv) * W - (A / 4) * W**2) * (4 / A)
        print(f"   j={jv} A={Av:>4}  closed={f(a)} quad[0,20]={f(b)} rel={f(abs(a-b)/abs(a))}"
              f"  analytic tail<={f(tailbd)}")
        sys.stdout.flush()

    xs = [mpf(0), mpf('1e-6'), mpf('0.01'), mpf('0.05'), mpf('0.1'), mpf('0.13'),
          mpf('0.2'), mpf('0.5'), mpf(1), mpf(10), mpf('21.022'), mpf(60),
          mpf(88), mpf(200)]

    print("\n" + "=" * 100)
    print("MAIN SWEEP")
    print("=" * 100)
    fails6, failsS = [], []
    for x in xs:
        T = thresh(x)
        print(f"\n--- x = {f(x)}   threshold(x) = {f(T)} ---")
        sys.stdout.flush()
        for (mult, label) in [(mpf(1), "AT thresh"), (mpf('1.0001'), "just above"),
                              (mpf('1.25'), "moderate"), (mpf(2), "2x"),
                              (mpf(10), "far above")]:
            A1 = T * mult
            v6, vS, r6, rS = row(x, A1, label)
            if v6 != "HOLDS":
                fails6.append((x, A1, label, r6))
            if vS != "HOLDS":
                failsS.append((x, A1, label, rS))

    print("\n" + "=" * 100)
    print("CROSSOVER SCAN, x = 0 — batch-6 candidate (exact head vs batch-6 tail)")
    print("=" * 100)
    for v in ['8', '8.5', '9', '9.5', '10', '11', '12', '14', '16']:
        A1 = mpf(v)
        hd, (t6, _) = head(mpf(0), A1), tail_batch6(mpf(0), A1)
        print(f"   A1={f(A1):>8} head={f(hd):>16} tail={f(t6):>16} ratio={f(t6/hd):>14}"
              f"  {'FAILS' if t6 > hd else 'holds'}")
        sys.stdout.flush()

    print("\n" + "=" * 100)
    print("CROSSOVER SCAN, x = 0 — batch-7 SHARP repair (provable headLow vs sharp tail)")
    print("=" * 100)
    for v in ['8', '10', '12', '12.5', '13', '14', '16', '20']:
        A1 = mpf(v)
        hl, (ts, _) = head_low(mpf(0), A1), tail_sharp(mpf(0), A1)
        print(f"   A1={f(A1):>8} headLow={f(hl):>16} tailSharp={f(ts):>16} ratio={f(ts/hl):>14}"
              f"  {'FAILS' if ts > hl else 'holds'}")
        sys.stdout.flush()

    print("\n" + "=" * 100)
    print("SHARP REPAIR at the candidate batch-7 threshold  A1 = 16 (|x|+1)^2")
    print("=" * 100)
    worst = mpf(0)
    for x in xs:
        A1 = 16 * (abs(x) + 1)**2
        hl = head_low(x, A1)
        ts, rs = tail_sharp(x, A1)
        ratio = (ts + rs) / hl
        worst = max(worst, ratio)
        print(f"   x={f(x):>14} A1={f(A1):>18} (tailS+rem)/headLow={f(ratio):>14}"
              f"  {'FAILS' if ratio >= 1 else 'holds'}")
        sys.stdout.flush()
    print(f"\n   worst ratio over sweep = {f(worst)}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"batch-6 candidate failures: {len(fails6)}")
    for (x, A1, lab, r) in fails6:
        print(f"    COUNTEREXAMPLE  x={f(x)}  A1={f(A1)}  [{lab}]  tail/head={f(r)}")
    print(f"batch-7 sharp-repair failures: {len(failsS)}")
    for (x, A1, lab, r) in failsS:
        print(f"    x={f(x)}  A1={f(A1)}  [{lab}]  tailS/headLow={f(r)}")


if __name__ == "__main__":
    main()
