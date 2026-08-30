#!/usr/bin/env python3
"""
C3 batch 9 — corrected numerics.  Repairs the two defects OpenAI found in batch 8.

DEFECT 1 (tmp/c3b8_utail.py).  For non-grid-aligned s it started at floor(s/h), so it
integrated BELOW s and applied Simpson with an endpoint != s.
REPAIR: every quadrature grid is built on [s, umax] with the left endpoint EXACTLY s.

DEFECT 2 (both scripts).  Cred truncated the k-sum at Kmax and then "bounded" the residual
by a FINITE partial sum of the majorant (loop to Kmax+200 with an early break).  That is a
partial sum, not an enclosure of the infinite residual.
REPAIR: closed-form enclosure, below.

--------------------------------------------------------------------------------------
RIGOROUS RESIDUAL ENCLOSURE (all inputs are COMPILED Lean facts)

  Cred(u,x) = sum_{k>=1} k^2 tau_x(k) F(k A1, x),   A1 = A1(u) = 2 pi e^{2u}
  |tau_x(k)| <= d(k) <= k                                    (|cos| <= 1)
  |F(A,x)|   <= 2 (A+3)^2 e^{-A}     for A >= 6              [C3B8.radial_abs_le_sharp6]
  k A1 >= A1 >= 2 pi > 6                                     [C3B8.modeA_head_ge_six]
  (k A1 + 3)^2 <= k^2 (A1+3)^2       for k >= 1

  => |k^2 tau_x(k) F(k A1,x)| <= 2 (A1+3)^2 k^5 e^{-k A1}

  sum_{k>K} k^5 r^k, r = e^{-A1}:
     k = K+1+j  =>  k^5 <= (K+1)^5 (1+j)^5   and   (1+j)^5 <= 120 e^{1+j}   (t^5/5! <= e^t)
     => sum_{k>K} k^5 r^k <= (K+1)^5 r^{K+1} * 120 e / (1 - e r)      (needs e r < 1)

  RESID(K,A1) := 2 (A1+3)^2 (K+1)^5 e^{-(K+1)A1} * 120 e / (1 - e^{1-A1})

This is a genuine enclosure of the infinite residual.  Labelled RIGOROUS.

The u-tail beyond umax is enclosed the same way (K = 0 gives |Cred| <= B(u)), then
  B(u) <= 32 pi^2 Cg e^{9u} e^{-A1(u)},  A1(u) >= A1(M) + 2 A1(M)(u-M),
  int_M^inf (u-s)^2 e^{9u} e^{-A1(u)} du
      <= e^{9M} e^{-A1(M)} * int_0^inf (v + (M-s))^2 e^{-(2A1(M)-9) v} dv
       = e^{9M} e^{-A1(M)} * (d^2/c + 2d/c^2 + 2/c^3),  d = M-s, c = 2A1(M)-9.
Labelled RIGOROUS.

The Simpson quadrature on [s, umax] is NOT rigorous (no derivative enclosure).  It is
reported as HIGH-PRECISION NON-RIGOROUS, with N, 2N, 4N refinement printed so the reader
can see the stability directly.

Numerics may falsify only.  Nothing here proves anything.
"""
import sys
from mpmath import mp, mpf, mpc, exp, log, pi, e, besselk, nstr

mp.dps = 40


def divisors(k):
    ds, i = [], 1
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


def resid(K, a1):
    """RIGOROUS enclosure of sum_{k>K} |k^2 tau F(k A1)|"""
    er = e * exp(-a1)
    if er >= 1:
        return mpf('inf')
    return (2 * (a1 + 3) ** 2 * mpf(K + 1) ** 5 * exp(-(K + 1) * a1)
            * 120 * e / (1 - er))


def Cred(u, x, K=None):
    """(value, RIGOROUS residual enclosure)"""
    a1 = A1(u)
    if K is None:
        K = int(mp.floor(abs(x) / a1)) + 40
    s = mpf(0)
    for k in range(1, K + 1):
        s += mpf(k) ** 2 * tau(x, k) * F(k * a1, x)
    return s, resid(K, a1)


def utail_enclosure(s, M):
    """RIGOROUS bound on |int_M^inf (u-s)^2 e^{5u} Cred(u,x) du| / (nothing dropped).
    Uses |Cred(u)| <= 32 pi^2 Cg e^{9u} e^{-A1(u)} with Cg = 120 e/(1-e^{1-A1(M)}),
    which is resid(0,A1) rearranged with (A1+3)^2 <= 4 A1^2 = 16 pi^2 e^{4u}."""
    aM = A1(M)
    er = e * exp(-aM)
    if er >= 1:
        return mpf('inf')
    Cg = 120 * e / (1 - er)
    c = 2 * aM - 9
    if c <= 0:
        return mpf('inf')
    d = M - s
    poly = d**2 / c + 2 * d / c**2 + 2 / c**3
    return 32 * pi**2 * Cg * exp(9 * M) * exp(-aM) * poly


def simpson_grid(vals, h):
    n = len(vals) - 1
    assert n % 2 == 0, "Simpson needs an even number of subintervals"
    tot = vals[0] + vals[-1]
    for i in range(1, n):
        tot += (4 if i % 2 == 1 else 2) * vals[i]
    return tot * h / 3


def f12(v):
    return nstr(v, 12)


def Ured_aligned(s, x, M, N):
    """Simpson on [s, M] with left endpoint EXACTLY s (defect-1 repair).
    Returns (quadrature value, worst pointwise k-residual contribution, u-tail enclosure)."""
    h = (M - s) / N
    vals, worstres = [], mpf(0)
    for i in range(N + 1):
        u = s + i * h                      # EXACTLY s at i = 0
        c, rr = Cred(u, x)
        w = (u - s) ** 2 * exp(5 * u)
        vals.append(w * c)
        worstres = max(worstres, w * rr)
    val = simpson_grid(vals, h)
    kres = worstres * (M - s)              # crude but valid bound on the k-residual's effect
    return val, kres, utail_enclosure(s, M)


def main():
    print("=" * 100)
    print("C3 BATCH 9 — corrected numerics (defect-1 and defect-2 repairs)")
    print(f"mpmath dps = {mp.dps}")
    print("RIGOROUS = closed-form enclosure; NONRIG = high-precision Simpson (no derivative bound)")
    print("=" * 100)
    sys.stdout.flush()

    # ---------------------------------------------------------- residual sanity
    print("\n[RIGOROUS] residual enclosure resid(K, A1) at the k-cutoffs actually used")
    for (xv, uv) in [(0, 0), (14.134725, 0), (21.022, 0), (60, 0), (88, 0), (88, 1)]:
        x, u = mpf(xv), mpf(uv)
        a1 = A1(u)
        K = int(mp.floor(abs(x) / a1)) + 40
        print(f"   x={str(xv):>10} u={str(uv):>3} A1={f12(a1):>14} K={K:>4} "
              f"resid={f12(resid(K, a1))}")
        sys.stdout.flush()

    # ---------------------------------------------------------- B1 re-audit
    print("\n" + "=" * 100)
    print("(B1) SIGN OF cellDensity — RE-AUDITED with the corrected enclosure")
    print("=" * 100)
    for xv in [0, 1, 10, 14.134725, 21.022, 60, 88]:
        x = mpf(xv)
        top = log(20 * (abs(x) + 1) ** 2 / (2 * pi)) / 2
        print(f"\n--- x = {f12(x)}  window [0, {f12(top)}] ---")
        sys.stdout.flush()
        flips, prev = [], None
        for i in range(13):
            u = top * mpf(i) / 12
            c, rr = Cred(u, x)
            decided = abs(c) > rr
            sg = (1 if c > 0 else -1) if decided else 0
            tag = ("+" if sg > 0 else ("-" if sg < 0 else "UNDECIDED"))
            if prev not in (None, 0) and sg not in (0,) and sg != prev:
                flips.append(f12(u))
            if sg != 0:
                prev = sg
            if i % 3 == 0 or sg < 0:
                print(f"    u={f12(u):>14} Cred={f12(c):>16} resid={f12(rr):>12} "
                      f"{tag}  [{'RIGOROUS' if decided else 'UNDECIDED'}]")
                sys.stdout.flush()
        print(f"    sign changes (rigorously decided points only): {len(flips)} at {flips}")
        sys.stdout.flush()

    # ---------------------------------------------------------- B2 with alignment + refinement
    print("\n" + "=" * 100)
    print("(B2) U_x(s) — grid aligned exactly at s; N, 2N, 4N refinement")
    print("=" * 100)
    bad = []
    for xv in [0, 1, 10, 14.134725, 21.022, 60]:
        x = mpf(xv)
        top = log(20 * (abs(x) + 1) ** 2 / (2 * pi)) / 2
        M = log(max(6 * abs(x), mpf(220)) / (2 * pi)) / 2
        if M < top:
            M = top + mpf('0.5')
        print(f"\n--- x = {f12(x)}  u1={f12(top)}  M={f12(M)}  A1(M)={f12(A1(M))} ---")
        sys.stdout.flush()
        for frac in [mpf(0), mpf('0.37'), mpf('0.63'), mpf(1)]:
            s = top * frac
            row = []
            for N in [40, 80, 160]:
                v, kr, ut = Ured_aligned(s, x, M, N)
                row.append((N, v, kr, ut))
            N4, v4, kr4, ut4 = row[-1]
            decided = abs(v4) > kr4 + ut4
            print(f"    s={f12(s):>14}")
            for (N, v, kr, ut) in row:
                print(f"        N={N:>4} Ured={f12(v):>18}  [NONRIG]")
            print(f"        k-resid<={f12(kr4):>12}  u-tail<={f12(ut4):>12}  "
                  f"sign={'POS' if v4 > 0 else 'NEG'}  "
                  f"[{'enclosure-decided' if decided else 'quadrature-limited'}]")
            sys.stdout.flush()
            if v4 < 0:
                bad.append((x, s, v4))

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"  U_x(s) negative instances: {len(bad)}")
    for (x, s, v) in bad:
        print(f"    COUNTEREXAMPLE x={f12(x)} s={f12(s)} Ured={f12(v)}")
    if not bad:
        print("  no counterexample found (NONRIG quadrature; falsification only)")


if __name__ == "__main__":
    main()
