"""att530 — THE FACE MARRIAGE INSTRUMENT (HP_SKELETON [HP-LEAF]; ledger 530).

Sam, 2026-09-02: "go" on building the multiplicative-face operator and measuring its
readout against the completed channel, window by window, with the seat mass split.

THE COMPILED OBJECTS THIS INSTRUMENT READS
  symClock a l z = e^{izl/2} - a e^{-izl/2};  spectralCoord s = -i(s - 1/2), i.e. s = 1/2 + iz.
  symClock_logDeriv_face_form:  logDeriv_z(symClock a l) z = (i l/2)(1 + a e^{-izl})/(1 - a e^{-izl}).
  unitaryClocks_poisson_barycenter_eulerFace (Im z < 0, right of the line, 0 <= r < 1):
      circleAverage_a [ P_r(a) * logDeriv_z(symClock a l) z ] = logDeriv_z(symClock r l) z.
  unitaryClocks_poisson_barycenter_antiEulerFace (Im z > 0, left of the line, 0 < r < 1):
      circleAverage_a [ P_r(a) * logDeriv_z(symClock a l) z ] = logDeriv_z(symClock (1/r) l) z.
  With r = p^{-1/2}, l = log p:  face r  gives  e^{izl/2}(1 - p^{-s})   (the Euler factor's denominator),
                                 face 1/r gives e^{izl/2}(1 - p^{1-s})  (the CONDUCTION factor of the ordered readout).
  So ONE direct-integral operator over the compiled Poisson measure of unitary tick operators
  D_theta = diag((theta + 2 pi k)/l) reads the Euler face on the right and the conduction face on the left.
  zeta_logDeriv_eq_etaLim:  zeta'/zeta = (etaLim)'/(etaLim) - (1 - 2^{1-s})'/(1 - 2^{1-s})  on the channel.
  Generalised here to a conduction set Q:  (prod_{q in Q}(1 - q^{1-s})) zeta(s) = sum_n c_Q(n) n^{-s},
  a closed-cell bank of period prod Q (the cell sums to zero), convergent on Re s > 0.
  seatMass s = Re(logDeriv xi s)/(Re s - 1/2);  channel_mass_iff_online: seatMass >= 0 on the
  channel (left of the line, |t| > 634.5) iff every zero is on the line.
  BankDoorClassLaw.bank_logDeriv_re_le: for unimodular faces and Re s < 1/2,
      Re logDeriv_s(clock) <= -clockFloor(l, sigma),  clockFloor = (l/2) tanh(l(1/2 - sigma)/2).

WHAT IS MEASURED (pre-registered)
  (I1) positive controls of the two compiled barycenter identities at complex z (both sides).
  (I2) the door-law bound on the LEFT barycenter face (anti-Euler / conduction clock), which is
       compiled only for unimodular faces; PREDICTION: it holds for the barycenter (an average of
       bounded things is bounded), i.e. Re logDeriv_s(1 - q^{1-s} clock) <= -clockFloor(log q, sigma).
  (I3) the seat-mass split on the channel:  logDeriv zeta = A_Q + M_Q  with
       M_Q := - sum_{q in Q} logDeriv_s(1 - q^{1-s})       (multiplicative face: the barycenter operator, DC removed)
       A_Q := logDeriv_s( prod_{q in Q}(1 - q^{1-s}) zeta )  (additive face: the closed-cell ordered bank)
       seatMass = [Re E + Re M_Q + Re A_Q]/(sigma - 1/2),  E = 1/s + 1/(s-1) - (log pi)/2 + psi(s/2)/2.
       PREDICTION: Re M_Q >= sum_q (log q/2 + clockFloor_q) > 0, so the multiplicative face contributes
       NEGATIVE seat mass, monotone decreasing as Q grows; the additive face carries the poles of the
       zeros and the compensating positive mass, monotone increasing in Q; total = seatMass > 0 on the
       verified range.  DECISION RULE: confirmed if at every window the two signs are as stated and
       both magnitudes grow with Q; refuted if the multiplicative face's seat-mass share is positive at
       any window or fails to grow.
  (I4) the closed-cell partial sums of the ordered bank at one point, as a control that the additive
       face is a convergent bank (cell of period prod Q closes exactly).

Read-only.  L-values (mpmath zeta) enter only as the exact reference for the split.
"""

from __future__ import annotations

import sys
from mpmath import mp, mpf, mpc, zeta, digamma, log, pi, exp, cos, quad, tanh, fabs, re, im, sqrt

mp.dps = 25

ZEROS = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513,
         32.935061587739190, 37.586178158825671, 40.918719012147495, 43.327073280914999,
         48.005150881167160, 49.773832477672302, 52.970321477714461, 56.446247697063395,
         59.347044002602353]

I = mpc(0, 1)


# ------------------------------------------------------------------ compiled objects, numerically

def sym_logderiv_z(a, ell, z):
    """logDeriv in z of symClock a ell (face form, ClockPoissonBarycenter.symClock_logDeriv_face_form)."""
    w = a * exp(-I * z * ell)
    return (I * ell / 2) * (1 + w) / (1 - w)


def poisson_kernel(r, theta):
    """Mathlib poissonKernel 0 (r:ℂ) (e^{iθ}) = (1 - r²)/|e^{iθ} - r|²; circle average = 1."""
    return (1 - r ** 2) / (1 - 2 * r * cos(theta) + r ** 2)


def barycenter(r, ell, z):
    """circleAverage over unimodular faces a = e^{iθ} of P_r(θ)·logDeriv_z(symClock a ell) z."""
    f = lambda th: poisson_kernel(r, th) * sym_logderiv_z(exp(I * th), ell, z)
    return quad(f, [0, pi / 2, pi, 3 * pi / 2, 2 * pi]) / (2 * pi)


def s_of_z(z):
    return mpf(1) / 2 + I * z


def z_of_s(s):
    return -I * (s - mpf(1) / 2)


def logderiv_s_from_z(Lz):
    """d/ds = (dz/ds) d/dz = -i d/dz."""
    return -I * Lz


def clock_floor(ell, sigma):
    return (ell / 2) * tanh(ell * (mpf(1) / 2 - sigma) / 2)


def logderiv_conduction(q, s):
    """logDeriv_s (1 - q^{1-s}) = (log q) q^{1-s} / (1 - q^{1-s})."""
    w = mpf(q) ** (1 - s)
    return log(q) * w / (1 - w)


def logderiv_zeta(s):
    return zeta(s, derivative=1) / zeta(s)


def ends_gamma(s):
    return 1 / s + 1 / (s - 1) - log(pi) / 2 + digamma(s / 2) / 2


def logderiv_xi(s):
    return ends_gamma(s) + logderiv_zeta(s)


def seat_mass(s):
    return re(logderiv_xi(s)) / (re(s) - mpf(1) / 2)


# ------------------------------------------------------------------ I1: barycenter controls

def control_barycenter():
    out = []
    for p in (2, 3, 7):
        ell = log(p)
        r = mpf(p) ** (-mpf(1) / 2)
        for z in (mpc(3.7, -0.4), mpc(14.1, -0.15)):       # right of the line: Euler face r
            lhs = barycenter(r, ell, z)
            rhs = sym_logderiv_z(r, ell, z)
            out.append(("right", p, z, fabs(lhs - rhs)))
        for z in (mpc(3.7, 0.4), mpc(14.1, 0.15)):         # left of the line: anti-Euler face 1/r
            lhs = barycenter(r, ell, z)
            rhs = sym_logderiv_z(1 / r, ell, z)
            out.append(("left", p, z, fabs(lhs - rhs)))
    return out


# ------------------------------------------------------------------ I2 + I3: the seat-mass split

Q_SETS = [(), (2,), (2, 3), (2, 3, 5), (2, 3, 5, 7)]


def split_at(s, Q):
    """Return (E, M_Q, A_Q, logDeriv zeta) at s for conduction set Q."""
    E = ends_gamma(s)
    Lz = logderiv_zeta(s)
    M = -sum((logderiv_conduction(q, s) for q in Q), mpc(0))
    A = Lz - M
    return E, M, A, Lz


def door_check(sigma, ts, Q):
    """Max over the grid of Re logDeriv_s(anti-clock_q) + clockFloor_q (should be <= 0).
    anti-clock_q log-derivative in s = log q / 2 + logDeriv_s(1 - q^{1-s})."""
    worst = -mpf(10) ** 9
    for t in ts:
        s = mpc(sigma, t)
        for q in Q:
            ell = log(q)
            val = re(ell / 2 + logderiv_conduction(q, s)) + clock_floor(ell, sigma)
            worst = max(worst, val)
    return worst


def window_means(sigma, ts, Q):
    """Window means (between consecutive zeros) of the seat-mass parts for conduction set Q."""
    rows = []
    for a, b in zip(ZEROS[:-1], ZEROS[1:]):
        pts = [t for t in ts if a + 0.15 < t < b - 0.15]
        if not pts:
            continue
        acc = {"seat": mpf(0), "E": mpf(0), "M": mpf(0), "A": mpf(0)}
        for t in pts:
            s = mpc(sigma, t)
            E, M, A, Lz = split_at(s, Q)
            d = re(s) - mpf(1) / 2
            acc["seat"] += re(E + Lz) / d
            acc["E"] += re(E) / d
            acc["M"] += re(M) / d
            acc["A"] += re(A) / d
        n = len(pts)
        rows.append((a, b, n, acc["seat"] / n, acc["E"] / n, acc["M"] / n, acc["A"] / n))
    return rows


# ------------------------------------------------------------------ I4: closed-cell partial sums

def ordered_bank_partial(Q, s, N):
    """Partial sums of sum_n c_Q(n) n^{-s}, c_Q = coefficients of prod_{q in Q}(1 - q^{1-s}) zeta(s):
    c_Q(n) = sum_{d | n, d | P} mu(d) d  with P = prod Q  (i.e. prod over q|n of (1 - q))."""
    total = mpc(0)
    vals = []
    for n in range(1, N + 1):
        c = 1
        for q in Q:
            if n % q == 0:
                c *= (1 - q)
        total += c * mpf(n) ** (-s)
        vals.append(total)
    return vals


def cell_control(Q, s, N):
    exact = zeta(s)
    for q in Q:
        exact *= (1 - mpf(q) ** (1 - s))
    P = 1
    for q in Q:
        P *= q
    vals = ordered_bank_partial(Q, s, N)
    # read at complete cells only (n a multiple of the period P)
    cells = [vals[k * P - 1] for k in range(1, N // P + 1)]
    errs = [fabs(v - exact) for v in cells]
    return exact, errs[len(errs) // 4], errs[len(errs) // 2], errs[-1]


# ------------------------------------------------------------------ main

def main():
    lines = []
    P = lines.append
    P("att530 — face marriage instrument (mp.dps=%d)" % mp.dps)
    P("")
    P("I1  barycenter identities (compiled 520), |lhs - rhs|:")
    for side, p, z, err in control_barycenter():
        P("    %-5s p=%d z=%s  err=%.3e" % (side, p, mp.nstr(z, 6), float(err)))
    P("")
    ts = [mpf(8) + mpf(k) * mpf("0.05") for k in range(int((60 - 8) / 0.05) + 1)]
    for sigma in (mpf("0.45"), mpf("0.40")):
        P("=" * 96)
        P("sigma = %s   (channel, left of the line; RH region so seatMass > 0 expected)" % mp.nstr(sigma, 3))
        P("I2  door-law check on the LEFT barycenter face (anti-Euler clock), max of Re logDeriv_s + clockFloor over grid:")
        for Q in Q_SETS[1:]:
            w = door_check(sigma, ts, Q)
            P("    Q=%-14s max = %+.6f   (%s)" % (str(Q), float(w), "OK <= 0" if w <= 0 else "VIOLATION"))
        P("I3  seat-mass split, window means between consecutive zeros:  seat = E + M_Q + A_Q  (each /(sigma-1/2))")
        for Q in Q_SETS:
            P("  -- Q = %s" % (str(Q) if Q else "()"))
            P("     window            n    seat        E          M_Q(mult)   A_Q(add)")
            for a, b, n, seat, E, M, A in window_means(sigma, ts, Q):
                P("     [%6.2f,%6.2f] %4d  %+9.4f  %+9.4f  %+10.4f  %+10.4f" % (a, b, n, float(seat), float(E), float(M), float(A)))
        P("")
    P("I4  closed-cell ordered bank, partial sums at complete cells vs exact (s = 0.45 + 14.0 i):")
    s0 = mpc("0.45", "14.0")
    for Q in Q_SETS[1:]:
        exact, e1, e2, e3 = cell_control(Q, s0, 21000)
        P("    Q=%-14s exact=%s   |err| at N/4, N/2, N: %.2e %.2e %.2e" % (str(Q), mp.nstr(exact, 8), float(e1), float(e2), float(e3)))
    text = "\n".join(lines)
    print(text)
    with open("/Users/samuellavery/work/helix_frobenius/tmp/att530_results.txt", "w") as f:
        f.write(text + "\n")


if __name__ == "__main__":
    main()
