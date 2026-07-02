"""The 37.a weld/BSD experiment: the forced central zero and its reverb rate.

37.a (y^2 + y = x^3 - x): conductor 37, the first rank-1 curve, root number eps = -1.
The weld phase is pi, so (HingeKernel.weld_pins_half_phase, Delta = pi) the completed
Lambda(1/2+it) is pinned to the pi/2 ray — purely imaginary on the WHOLE line — and
(weld_minus_one_forces_zero) the hinge value is forced to vanish.  The hinge is then a
CROSSING, not a turning point, and its reopening rate is the BSD leading datum:

    |Lambda'(1/2)| = (sqrt(37)/2pi) * L'(1)     (Gross-Zagier: L'(1) = 0.3059997738...)

E11 (eps = +1) is the control: even hinge, turning point, Lambda(1/2) = (sqrt(11)/2pi)*L(1).

Everything fiber-side: a_p by point counting (no L-library in the loop); the pinning test
itself DETERMINES a_37 (the wrong Euler factor destroys the L-function and the ray smears).
References computed independently from the same coefficients via the exponential-integral
series L'(1) = 2 sum (a_n/n) E1(2pi n/sqrt(N)) [eps=-1] and L(1) = 2 sum (a_n/n) e^{-2pi n/sqrt(N)}
[eps=+1] (Cremona, Algorithms ch. 2.11).
"""
import math

import numpy as np
from scipy.special import exp1, loggamma

NB = 6000


def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


def ap_curve(p, A2, A4, A6):
    """a_p for y^2 + y = x^3 + A2 x^2 + A4 x + A6 via (2y+1)^2 = 4*RHS + 1."""
    if p == 2:
        cnt = sum(1 for x in range(2) for y in range(2)
                  if (y * y + y - (x ** 3 + A2 * x * x + A4 * x + A6)) % 2 == 0)
        return 2 + 1 - (cnt + 1)
    x = np.arange(p, dtype=np.int64)
    z = (4 * (x ** 3 % p) + 4 * A2 % p * (x * x % p) + 4 * A4 % p * x + (4 * A6 + 1)) % p
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(z == 0, 0, np.where(isq[z], 1, -1))
    return int(-chi.sum())


def an_bank(q, ap_fn, a_bad, nmax):
    """Multiplicative a_n from a_p (good p) + a_q = a_bad (prime conductor q)."""
    primes = sieve_primes(nmax)
    a = np.zeros(nmax + 1)
    a[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    ap = {int(p): (a_bad if p == q else ap_fn(int(p))) for p in primes}
    for n in range(2, nmax + 1):
        p = int(spf[n])
        m, k = n, 0
        while m % p == 0:
            m //= p
            k += 1
        pk = n // m
        if m > 1:
            a[n] = a[m] * a[pk]
        elif k == 1:
            a[n] = ap[p]
        else:
            a[n] = ap[p] * a[pk // p] - (0 if p == q else p) * a[pk // p // p if k >= 2 else 1]
    return a


def completed_line(lam, q, ts):
    """Completed Lambda(1/2+it) from the tapered fiber + exact Gamma prefactor."""
    n = np.arange(1, len(lam) + 1, dtype=np.float64)
    u = n / len(lam)
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = lam * w * n ** (-0.5)
    ln = np.log(n)
    F = np.array([np.sum(amp * np.exp(-1j * t * ln)) for t in ts])
    pref = np.exp((1.0 + 1j * ts) * math.log(math.sqrt(q) / (2 * math.pi))
                  + loggamma(1.0 + 1j * ts))
    return pref * F


def run_curve(tag, q, A, a_bad_candidates, eps_expect, ref_kind):
    print(f"=== {tag} (conductor {q}) ===")
    best = None
    for ab in a_bad_candidates:
        a = an_bank(q, lambda p: ap_curve(p, *A), ab, NB)
        lam = a[1:] / np.sqrt(np.arange(1, NB + 1))
        ts = np.linspace(0.05, 20.0, 1200)
        Lam = completed_line(lam, q, ts)
        med = np.median(np.abs(Lam))
        mask = np.abs(Lam) > 0.5 * med
        zbar = np.mean(np.exp(2j * np.mod(np.angle(Lam[mask]), math.pi)))
        ray = (np.angle(zbar) / 2) % math.pi
        spread = 1.0 - abs(zbar)
        print(f"  a_{q} = {ab:+d}: pinned ray {ray/math.pi:.4f}pi, spread {spread:.2e}")
        if best is None or spread < best[0]:
            best = (spread, ab, a, lam, ray)
    _, ab, a, lam, ray = best
    eps = -1 if abs(ray - math.pi / 2) < math.pi / 4 else +1
    print(f"  -> a_{q} = {ab:+d} wins; ray {ray/math.pi:.4f}pi => root number eps = {eps:+d} "
          f"(expected {eps_expect:+d})")

    # hinge photograph + derivative (fine central grid)
    dt = 1e-3
    tc = np.array([-2 * dt, -dt, 0.0, dt, 2 * dt, 1.0])
    Lc = completed_line(lam, q, tc)
    L0 = Lc[2]
    dL = (Lc[3] - Lc[1]) / (2 * dt)
    scale = abs(completed_line(lam, q, np.array([1.3]))[0])
    n = np.arange(1, NB + 1, dtype=np.float64)
    x = 2 * math.pi * n / math.sqrt(q)
    if ref_kind == "deriv":
        ref = 2 * np.sum((a[1:] / n) * exp1(x))          # L'(1), eps = -1
        pred_rate = (math.sqrt(q) / (2 * math.pi)) * ref
        print(f"  hinge value |Lambda(1/2)| = {abs(L0):.3e}  (vs scale {scale:.3f}: "
              f"forced zero at {abs(L0)/scale:.1e} of scale)")
        print(f"  hinge reverb rate |Lambda'(1/2)| = {abs(dL):.6f}")
        print(f"  predicted (sqrt(q)/2pi)*L'(1):     {pred_rate:.6f}   "
              f"[L'(1) = {ref:.10f} via E1 series; Gross-Zagier 0.3059997738]")
        print(f"  agreement: {abs(dL)/pred_rate:.6f}")
    else:
        ref = 2 * np.sum((a[1:] / n) * np.exp(-x))        # L(1), eps = +1
        pred_val = (math.sqrt(q) / (2 * math.pi)) * ref
        print(f"  hinge value |Lambda(1/2)| = {abs(L0):.6f}   predicted (sqrt(q)/2pi)*L(1) = "
              f"{pred_val:.6f}   [L(1) = {ref:.10f}; LMFDB 0.2538418609]")
        print(f"  agreement: {abs(L0)/pred_val:.6f}")
        print(f"  hinge slope |dLambda/dt(0)| = {abs(dL):.3e}  (turning point: expect ~0; "
              f"vs 37.a's {0.2963:.4f})")
    print()


if __name__ == "__main__":
    # 37.a1: y^2 + y = x^3 - x  ->  A2 = 0, A4 = -1, A6 = 0
    run_curve("37.a rank 1", 37, (0, -1, 0), [+1, -1], -1, "deriv")
    # 11.a1 control: y^2 + y = x^3 - x^2 - 10x - 20
    run_curve("11.a rank 0 (control)", 11, (-1, -10, -20), [+1, -1], +1, "value")
