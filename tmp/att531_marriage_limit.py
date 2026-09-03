"""att531 — THE MARRIAGE LIMIT: the closed-cell face minus its DC, as Q grows (ledger 531).

Exact finite-Q identity (compiled in FaceMarriageIdentity.lean):
    logDeriv( prod_{q in Q}(1 - q^{1-s}) * zeta )(s) + sum_{q in Q} log q
      = -(E(s) + E(1-s)) - [ logDeriv zeta(1-s) + P_Q(1-s) ],
    E(s) = 1/s + 1/(s-1) - (log pi)/2 + psi(s/2)/2,
    P_Q(w) = sum_{q in Q} log q * q^{-w}/(1 - q^{-w}) = sum_{n Q-smooth} Lambda(n) n^{-w}.
So "closed-cell face minus clock DC" = the Archimedean/ends pair MINUS the reflected Euler defect
    delta_Q(w) := logDeriv zeta(w) + P_Q(w)  at  w = 1 - s  (Re w = 1 - sigma in (1/2, 1)).
delta_Q(w) -> 0 as Q -> all primes  iff  the von Mangoldt series converges at w; for Re w in
(1/2,1) that convergence at every point is equivalent to RH.  In the measured range RH holds, so
the PRE-REGISTERED prediction is: delta_Q wanders and decays like Q^{1/2 - Re w} = Q^{sigma - 1/2}:
sigma = 0.45 -> Q^{-0.05} (factor ~0.56 over 10..10^6), sigma = 0.40 -> Q^{-0.10} (factor ~0.32).
DECISION RULE: the decade-RMS of delta_Q over the sample points decreases with Q, by a factor within
2x of the predicted one; a systematic increase is a bug or a contradiction.  Also: the finite-Q
identity is checked numerically to 1e-18 as a control of the Lean statement.

Read-only; mpmath zeta is the exact reference only.
"""

from __future__ import annotations

import math
import numpy as np
from mpmath import mp, mpf, mpc, zeta, digamma, log, pi

mp.dps = 22
I = mpc(0, 1)


def primes_upto(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return np.nonzero(sieve)[0]


def E(s):
    return 1 / s + 1 / (s - 1) - log(pi) / 2 + digamma(s / 2) / 2


def logderiv_zeta(s):
    return zeta(s, derivative=1) / zeta(s)


def P_Q_mp(Q, w):
    """Exact (mpmath) reflected Euler sum over a small set Q."""
    tot = mpc(0)
    for q in Q:
        x = mpf(q) ** (-w)
        tot += log(q) * x / (1 - x)
    return tot


def P_Q_np(primes: np.ndarray, w: complex) -> complex:
    """Double-precision reflected Euler sum over all primes in the array."""
    p = primes.astype(np.float64)
    x = np.exp(-w * np.log(p))
    return complex(np.sum(np.log(p) * x / (1 - x)))


def identity_check(Q, s):
    """LHS: logDeriv(prod(1-q^{1-s}) zeta)(s) + sum log q; RHS: -(E(s)+E(1-s)) - delta_Q(1-s)."""
    lz = logderiv_zeta(s)
    lhs = lz
    for q in Q:
        wq = mpf(q) ** (1 - s)
        lhs += log(q) * wq / (1 - wq)          # logDeriv (1 - q^{1-s})
        lhs += log(q)                          # + DC
    rhs = -(E(s) + E(1 - s)) - (logderiv_zeta(1 - s) + P_Q_mp(Q, 1 - s))
    return abs(lhs - rhs)


def main():
    out = []
    P = out.append
    P("att531 — marriage limit (mp.dps=%d)" % mp.dps)
    P("")
    P("Control: the finite-Q marriage identity, |LHS - RHS|:")
    for Q in [(2,), (2, 3), (2, 3, 5, 7), (2, 3, 5, 7, 11, 13)]:
        for s in (mpc("0.45", "14.0"), mpc("0.40", "33.0")):
            P("    Q=%-22s s=%s  err=%.2e" % (str(Q), mp.nstr(s, 5), float(identity_check(Q, s))))
    P("")
    primes = primes_upto(1_000_000)
    cuts = [10, 100, 1_000, 10_000, 100_000, 1_000_000]
    ts = [14.0, 17.5, 25.0, 33.0, 40.0, 50.0]
    for sigma in (0.45, 0.40):
        P("=" * 90)
        P("sigma = %.2f   (w = 1 - s, Re w = %.2f);  delta_Q(w) = logDeriv zeta(w) + P_Q(w)" % (sigma, 1 - sigma))
        P("   predicted decay exponent of |delta_Q|: Q^{%+.2f}" % (sigma - 0.5))
        table = {}
        table_end = {}
        for t in ts:
            s = mpc(sigma, t)
            w = 1 - s
            lz = complex(logderiv_zeta(w))
            wc = complex(w)
            row, row_end = [], []
            for c in cuts:
                pr = primes[primes <= c]
                d = lz + P_Q_np(pr, wc)
                # the END term of the truncated explicit formula at the reflected point:
                # sum_{n<=Q} Lambda(n) n^{-w} = Q^{1-w}/(1-w) - zeta'/zeta(w) - sum_rho Q^{rho-w}/(rho-w) + ...
                end = (c ** (1 - wc)) / (1 - wc)
                row.append(d)
                row_end.append(d - end)
            table[t] = row
            table_end[t] = row_end
        P("   RAW delta_Q (first pre-registration, which omitted the end term Q^{1-w}/(1-w)):")
        P("   t      " + "".join("  Q<=%-9d" % c for c in cuts))
        for t in ts:
            P("   %5.1f  " % t + "".join("  %+6.3f%+6.3fi" % (d.real, d.imag) for d in table[t]))
        P("   END-CORRECTED delta'_Q = delta_Q - Q^{1-w}/(1-w)  (the pole at s=0/w=1 read at the cutoff):")
        P("   t      " + "".join("  Q<=%-9d" % c for c in cuts))
        for t in ts:
            P("   %5.1f  " % t + "".join("  %+6.3f%+6.3fi" % (d.real, d.imag) for d in table_end[t]))
        for label, tab in (("raw", table), ("end-corrected", table_end)):
            rms = []
            for j, c in enumerate(cuts):
                r = math.sqrt(sum(abs(tab[t][j]) ** 2 for t in ts) / len(ts))
                rms.append(r)
            P("   decade RMS (%s): " % label + "  ".join("Q<=%d: %.4f" % (c, r) for c, r in zip(cuts, rms)))
            xs = np.log10(np.array(cuts, dtype=float))
            ys = np.log10(np.array(rms))
            slope = np.polyfit(xs, ys, 1)[0]
            slope_hi = np.polyfit(xs[1:], ys[1:], 1)[0]
            P("      ratio RMS(10^6)/RMS(10^1) = %.3f;  fitted exponent %+.3f (from 10^2 on: %+.3f);  predicted for the end-corrected defect: %+.2f"
              % (rms[-1] / rms[0], slope, slope_hi, sigma - 0.5))
        P("")
    text = "\n".join(out)
    print(text)
    with open("/Users/samuellavery/work/helix_frobenius/tmp/att531_results.txt", "w") as f:
        f.write(text + "\n")


if __name__ == "__main__":
    main()
