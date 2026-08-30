#!/usr/bin/env python3
"""
C3 batch 7 — numerical check of the *provable chain* that the Lean repair will follow.

Every inequality below is one I intend to compile.  This script only checks that the
CHAIN OF BOUNDS I can prove is strong enough; it proves nothing.

Chain (all after dividing by the common positive pi^2 e^{5u}):

 (1) coshMoment j A  <=  e^{-A} e^{j^2/A} (1 + 4/A)                   [sharp majorant]
 (2) |radial(A)|     <=  2 (A+3)^2 e^{-A}                for A >= 8   [from (1)]
 (3) headLow         =   (A1^2-6A1+6) e^{-A1 cosh h} h/4  <= head     [kix_zero_lower]
 (4) (a b) >= a+b-1  and  (abA1+3)^2 <= (ab)^2 (A1+3)^2
 (5) sum_{a>=2} a^4 e^{-a A1}  <=  32 e^{-2A1}            for A1>=16
 (6) S := sum_{a>=1} a^4 e^{-a A1} <= e^{-A1}(1 + 32 e^{-A1})
 (7) S^2 - e^{-2A1}  <=  65 e^{-3A1}                      for A1>=16
 (8) tailProvable    =   2 (A1+3)^2 e^{A1} (S^2 - e^{-2A1}) <= 130 (A1+3)^2 e^{-2A1}

Target:  tailProvable < headLow  at  A1 >= T (|x|+1)^2  for T in {16, 20}.
"""
import sys
from mpmath import mp, mpf, mpc, exp, cosh, sqrt, pi, besselk, erfc, nstr

mp.dps = 40


def f(v):
    return nstr(v, 12)


def divisor_count(k):
    c, i = 0, 1
    while i * i <= k:
        if k % i == 0:
            c += 2 if i * i != k else 1
        i += 1
    return c


def head_low(x, A1):
    h = 1 / (abs(x) + 1)
    return (A1**2 - 6 * A1 + 6) * exp(-A1 * cosh(h)) * h / 4


def head_exact(x, A1):
    return (A1**2 + 9) * besselk(mpc(0, x), A1).real - 6 * A1 * besselk(mpc(1, x), A1).real


def tail_true_sharp(x, A1, K=60):
    """sum over (n,m)!=(0,0) of (ab)^2 * 2(A_z+3)^2 e^{-A_z}, grouped by k=ab"""
    s = mpf(0)
    for k in range(2, K + 1):
        Az = k * A1
        s += divisor_count(k) * k**2 * 2 * (Az + 3)**2 * exp(-Az)
    return s


def S_true(A1, N=200):
    return sum(mpf(a)**4 * exp(-a * A1) for a in range(1, N + 1))


def tail_provable(A1):
    """the closed form the Lean proof will end at: 130 (A1+3)^2 e^{-2A1}"""
    return 130 * (A1 + 3)**2 * exp(-2 * A1)


def tail_factorised_exact(A1):
    """2 (A1+3)^2 e^{A1} (S^2 - e^{-2A1}) — step (8) before the final rounding"""
    S = S_true(A1)
    return 2 * (A1 + 3)**2 * exp(A1) * (S**2 - exp(-2 * A1))


def main():
    print("=" * 96)
    print("C3 BATCH 7 — provable-chain verification (candidates only; nothing proved here)")
    print("=" * 96)

    print("\n[STEP 5/6/7] intermediate constants, A1 >= 16")
    for v in ['16', '20', '24', '32', '64']:
        A1 = mpf(v)
        tail2 = S_true(A1) - exp(-A1)                     # sum_{a>=2} a^4 e^{-aA1}
        bd5 = 32 * exp(-2 * A1)
        S = S_true(A1)
        lhs7 = S**2 - exp(-2 * A1)
        bd7 = 65 * exp(-3 * A1)
        print(f"  A1={f(A1):>6}  sum_{{a>=2}}={f(tail2)}  <= 32e^-2A1={f(bd5)}  {'OK' if tail2 <= bd5 else 'VIOLATED'}"
              f"   | S^2-e^-2A1={f(lhs7)} <= 65e^-3A1={f(bd7)}  {'OK' if lhs7 <= bd7 else 'VIOLATED'}")
        sys.stdout.flush()

    print("\n[STEP 8] the factorised bound really dominates the true sharp tail")
    for v in ['16', '20', '24', '32']:
        A1 = mpf(v)
        t_true = tail_true_sharp(mpf(0), A1)
        t_fac = tail_factorised_exact(A1)
        t_prov = tail_provable(A1)
        print(f"  A1={f(A1):>6}  trueSharp={f(t_true)}  factorised={f(t_fac)}  provable130={f(t_prov)}"
              f"   ratios fac/true={f(t_fac/t_true)} prov/true={f(t_prov/t_true)}"
              f"  {'OK' if t_prov >= t_true else 'VIOLATED'}")
        sys.stdout.flush()

    xs = [mpf(0), mpf('1e-6'), mpf('0.01'), mpf('0.05'), mpf('0.1'), mpf('0.2'),
          mpf('0.3'), mpf('0.5'), mpf('0.7'), mpf(1), mpf(2), mpf(5), mpf(10),
          mpf('14.134725'), mpf('21.022'), mpf(60), mpf(88), mpf(200)]

    for T in [mpf(16), mpf(20)]:
        print("\n" + "=" * 96)
        print(f"FINAL PROVABLE COMPARISON at threshold  A1 = {int(T)} (|x|+1)^2")
        print("=" * 96)
        worst = mpf(0)
        worstx = None
        bad = []
        for x in xs:
            A1 = T * (abs(x) + 1)**2
            hl = head_low(x, A1)
            tp = tail_provable(A1)
            r = tp / hl
            if r > worst:
                worst, worstx = r, x
            if r >= 1:
                bad.append((x, A1, r))
            print(f"   x={f(x):>14} A1={f(A1):>18} tailProv={f(tp):>16} headLow={f(hl):>16}"
                  f" ratio={f(r):>14}  {'FAILS' if r >= 1 else 'holds'}")
            sys.stdout.flush()
        print(f"\n   worst ratio = {f(worst)} at x = {f(worstx)};  failures = {len(bad)}")

    # scan h in (0,1] densely at the threshold: h = 1/(|x|+1), worst case is the interior
    print("\n" + "=" * 96)
    print("DENSE h-SCAN at A1 = T/h^2  (h = 1/(|x|+1) in (0,1]) — locate the true worst case")
    print("=" * 96)
    for T in [mpf(16), mpf(20)]:
        worst, worsth = mpf(0), None
        for i in range(1, 201):
            h = mpf(i) / 200
            A1 = T / h**2
            x = 1 / h - 1
            hl = head_low(x, A1)
            tp = tail_provable(A1)
            r = tp / hl
            if r > worst:
                worst, worsth = r, h
        print(f"   T={int(T)}:  worst ratio = {f(worst)}  at h = {f(worsth)}  (x = {f(1/worsth - 1)})"
              f"   {'FAILS' if worst >= 1 else 'holds'}")
        sys.stdout.flush()

    print("\n" + "=" * 96)
    print("SANITY: headLow really is below the exact head (it is a lower bound)")
    print("=" * 96)
    for x in [mpf(0), mpf('0.1'), mpf(1), mpf(10), mpf(60)]:
        A1 = 20 * (abs(x) + 1)**2
        print(f"   x={f(x):>10} A1={f(A1):>16} headLow={f(head_low(x,A1)):>16}"
              f" head={f(head_exact(x,A1)):>16}  {'OK' if head_low(x,A1) <= head_exact(x,A1) else 'VIOLATED'}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
