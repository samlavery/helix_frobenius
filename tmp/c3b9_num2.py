#!/usr/bin/env python3
"""
C3 batch 9 — numerics ADDENDUM.  Repairs a defect in tmp/c3b9_num.py that its own
N,2N,4N refinement exposed, and adds a positive control on the new Lean theorem.

SELF-CAUGHT DEFECT (c3b9_num.py, B2 block).  The "enclosure-decided" label compared the
quadrature value against the k-residual and u-tail enclosures only, and IGNORED the Simpson
error.  At x=60, s=0 the refinement printed
    N= 40  -2.62298356112e-37
    N= 80  +2.22858395109e-37
    N=160  +1.33534395891e-37
— a SIGN FLIP between N=40 and N=80 — yet the row was still labelled "sign=POS
[enclosure-decided]".  It is not decided.  The deep-s rows are worse: the value climbs
monotonically with N by tens of orders of magnitude (x=14.134725, s=3.296:
1.7e-2033 -> 4.5e-2009 -> 2.0e-1997), i.e. Simpson is resolving nothing there, because the
integrand varies by hundreds of orders of magnitude inside a single subinterval.

REPAIR, two parts:
  (1) quadrature: mpmath adaptive `quad` on geometric breakpoints instead of fixed Simpson,
      with `error=True`, and a CONVERGENCE GATE — a row is only reported as decided if
      (a) the mpmath error estimate, (b) the k-residual enclosure and (c) the u-tail
      enclosure are all below |value|.  Otherwise it prints QUAD-LIMITED and the sign
      claim is withdrawn.
  (2) tiers are printed on every row: RIGOROUS (closed-form enclosure), NONRIG (adaptive
      high precision, gated), EXPLORATORY (neither).

POSITIVE CONTROL on C3B9.ramp_window_le_tailT_window (compiled, exit 0):
    W1(s,w) = int_{(s,w]} (u-s)^2/2 C(u,x) du            [route 1's window]
    W2(s,w) = int_{(s,w]} tailT(C)(r) dr = U(s) - U(w)   [route 2's window]
The theorem says W1 <= W2 whenever 0<=s<=w and w clears the certified height.  A numerical
violation would mean my Lean statement does not mean what I think it means.  Numerics may
falsify only; agreement is a control, not evidence for the theorem.

The k-residual enclosure RESID(K,A1) and the u-tail enclosure are unchanged from
tmp/c3b9_num.py and remain RIGOROUS (derived from the compiled C3B8.radial_abs_le_sharp6).
"""
import sys
from mpmath import mp, mpf, mpc, exp, log, pi, e, besselk, nstr, quad, inf

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
    return sum(mp.cos(x * log(mpf(a) / mpf(k // a))) for a in divisors(k))


def F(A, x):
    return (A**2 + 9) * besselk(mpc(0, x), A).real - 6 * A * besselk(mpc(1, x), A).real


def A1(u):
    return 2 * pi * exp(2 * u)


def resid(K, a1):
    """RIGOROUS enclosure of sum_{k>K} |k^2 tau_x(k) F(k A1, x)|."""
    er = e * exp(-a1)
    if er >= 1:
        return mpf('inf')
    return (2 * (a1 + 3) ** 2 * mpf(K + 1) ** 5 * exp(-(K + 1) * a1)
            * 120 * e / (1 - er))


def Cred(u, x):
    a1 = A1(u)
    K = int(mp.floor(abs(x) / a1)) + 40
    s = mpf(0)
    for k in range(1, K + 1):
        s += mpf(k) ** 2 * tau(x, k) * F(k * a1, x)
    return s, resid(K, a1)


def utail_enclosure(s, M):
    """RIGOROUS bound on |int_M^inf (u-s)^2 e^{5u} Cred du|."""
    aM = A1(M)
    er = e * exp(-aM)
    if er >= 1:
        return mpf('inf')
    Cg = 120 * e / (1 - er)
    c = 2 * aM - 9
    if c <= 0:
        return mpf('inf')
    d = M - s
    return 32 * pi**2 * Cg * exp(9 * M) * exp(-aM) * (d**2 / c + 2 * d / c**2 + 2 / c**3)


def f12(v):
    return nstr(v, 12)


def breakpoints(s, M, n=6):
    """Geometric mesh clustered at s, where the integrand's mass sits."""
    pts = [s]
    span = M - s
    for i in range(n, 0, -1):
        pts.append(s + span / mpf(2) ** i)
    pts.append(M)
    out = [pts[0]]
    for p in pts[1:]:
        if p > out[-1]:
            out.append(p)
    return out


def Ured(s, x, M):
    """Adaptive high-precision U_x(s) on [s,M] with an mpmath error estimate.
    Returns (value, quad_error, worst_k_residual, u_tail_enclosure)."""
    worst = [mpf(0)]

    def integrand(u):
        c, rr = Cred(u, x)
        w = (u - s) ** 2 * exp(5 * u)
        if w * rr > worst[0]:
            worst[0] = w * rr
        return w * c

    v, err = quad(integrand, breakpoints(s, M), error=True)
    return v, err, worst[0] * (M - s), utail_enclosure(s, M)


def report(tag, v, err, kres, ut):
    tot = err + kres + ut
    decided = abs(v) > tot
    sign = "POS" if v > 0 else ("NEG" if v < 0 else "ZERO")
    lab = f"sign={sign} [NONRIG, gate-passed]" if decided else "[QUAD-LIMITED, no sign claim]"
    print(f"    {tag} val={f12(v):>18} quaderr={f12(err):>12} "
          f"kres={f12(kres):>12} utail={f12(ut):>12}  {lab}")
    sys.stdout.flush()
    return decided, v


def main():
    print("=" * 104)
    print("C3 BATCH 9 — numerics ADDENDUM: convergence gate + positive control")
    print(f"mpmath dps = {mp.dps}")
    print("Tiers: RIGOROUS = closed-form enclosure | NONRIG = adaptive quad, gated |"
          " EXPLORATORY = neither")
    print("=" * 104)
    sys.stdout.flush()

    print("\n" + "=" * 104)
    print("(C1) RE-AUDIT of the c3b9_num.py B2 table, with the Simpson error now GATED")
    print("=" * 104)
    undecided = []
    for xv in [0, 1, 10, 14.134725, 21.022, 60, 88, 200]:
        x = mpf(xv)
        u1 = log(20 * (abs(x) + 1) ** 2 / (2 * pi)) / 2     # = C3B9.certHeight x
        M = log(max(6 * abs(x), mpf(220)) / (2 * pi)) / 2
        if M < u1:
            M = u1 + mpf('0.5')
        print(f"\n--- x = {f12(x)}  certHeight = {f12(u1)}  M = {f12(M)} ---")
        sys.stdout.flush()
        for frac in [mpf(0), mpf('0.37'), mpf(1)]:
            s = u1 * frac
            v, err, kres, ut = Ured(s, x, M)
            ok, _ = report(f"s={f12(s):>14}", v, err, kres, ut)
            if not ok:
                undecided.append((xv, f12(s)))
            elif v < 0:
                print(f"        *** COUNTEREXAMPLE to U_x(s) >= 0 ***")

    print("\n" + "=" * 104)
    print("(C2) POSITIVE CONTROL on C3B9.ramp_window_le_tailT_window:  W1(s,w) <= W2(s,w)")
    print("     W1 = int_{(s,w]} (u-s)^2/2 C du      W2 = U(s) - U(w)")
    print("=" * 104)
    violations = 0
    for xv in [0, 1, 14.134725, 21.022, 60]:
        x = mpf(xv)
        u1 = log(20 * (abs(x) + 1) ** 2 / (2 * pi)) / 2
        M = log(max(6 * abs(x), mpf(220)) / (2 * pi)) / 2
        if M < u1:
            M = u1 + mpf('0.5')
        w = u1 + mpf('0.05')          # clears the certified height
        s = u1 * mpf('0.4')
        # W1: quadratic ramp at base s, restricted to (s,w]
        W1 = quad(lambda u: (u - s) ** 2 * exp(5 * u) * Cred(u, x)[0],
                  breakpoints(s, w)) / 2
        Us = Ured(s, x, M)[0] / 2
        Uw = Ured(w, x, M)[0] / 2
        W2 = Us - Uw
        gap = W2 - W1
        flag = "OK" if gap >= 0 else "*** VIOLATION ***"
        if gap < 0:
            violations += 1
        print(f"  x={f12(x):>14} s={f12(s):>12} w={f12(w):>12}")
        print(f"      W1={f12(W1):>18}  W2={f12(W2):>18}  W2-W1={f12(gap):>18}  {flag}")
        sys.stdout.flush()

    print("\n" + "=" * 104)
    print("SUMMARY")
    print("=" * 104)
    print(f"  rows that FAILED the convergence gate (no sign claim made): {len(undecided)}")
    for (xv, s) in undecided:
        print(f"      x={xv} s={s}")
    print(f"  positive-control violations of W1 <= W2: {violations}")
    print("  Reminder: numerics may falsify only.  Nothing above proves anything.")


if __name__ == "__main__":
    main()
