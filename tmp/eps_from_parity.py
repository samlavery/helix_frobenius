#!/usr/bin/env python3
"""
eps_from_parity.py -- Probe 1 of the registration program, certifier route (b):
the seed's crossing lattice (trace-formula/BE ladder).  Extends the FROZEN
instruments poisson_dual.py / rank_ladder_closure.py; modifies neither.

CONTEXT (2026-07-28): the per-rung Gamma-chart registration reduces, Poisson-free,
to ONE real condition on the weld axis (the standing wave), given gate 1.  This
probe gathers the route-(b) evidence that the SEED lattice certifies it: the
mechanism under test is "one Poisson, every rank" -- the rank enters the dual
kernel only as the Bessel ORDER ladder with the quarter-turn phase (-i)^n per
order (the mu_4 refinement of RankLadderParity's mu_2 clock), on a lattice that
never changes with rank; and the root number assembles multiplicatively over the
seed-clock covers.

PRE-REGISTERED TESTS (tiered):
  A0 [anchor, exact identity]
      int_{-1}^{1} sqrt(1-x^2) U_r(x) e^{-izx} dx = pi (-i)^r (r+1) J_{r+1}(z)/z
      for r = 0..13.  Machine zero required (pure Hankel/Gegenbauer pair).
  A1 [measured, KILL-TEST for the archimedean half]
      On the REAL dual kernel of the ladder run (theta_inf * (F + H) profile,
      p=2, k=1, elliptic, the object of rank_ladder_closure), with
      G_r(t) = W(cos t) sin((r+1)t) and a_n its cosine coefficients:
        I(r; xi) = int W(x) U_r(x) e^(-2 pi i x xi c) dx
                 = pi * sum_{n == r mod 2} a_n (-i)^n J_n(2 pi xi c).
      The dual kernel IS its exact Bessel-order-ladder resummation -- the
      per-channel exact form of the BE-bridge "edge-skeleton resummation".
      Parity law a_n = 0 for n != r mod 2 checked; quarter-turn law
      i^r * I(r;xi) in R checked.
      CONTROL: order-shift (J_{n+1} in place of J_n) must break it at every rank.
  B  [exact arithmetic + cross-check vs measured ladder]
      Channel recursion of the root numbers (k=12 seed):
        kappa(11 kappa + 1) - (kappa-1)(11(kappa-1)+1) = 11 r + 1   (r = 2kappa-1),
      so eps(Sym^r)/eps(Sym^{r-2}) = i^{-(11 r + 1)}; the assembled
      eps(Sym^r) = i^{-kappa(11 kappa + 1)} must reproduce the measured
      theta-selfduality sign ladder +,-,-,+,+,-,- (r = 1,3,...,13; sym_r_sweep2).
  D  [measured] paired-lattice reality (standing wave on the BE lattice):
      Im(dual_xi + dual_{-xi}) = 0 on the full Kloosterman-weighted terms at
      every rank -- the lattice twin of AxisPairing.pairedBank_real.

KILL CONDITIONS (any one kills route (b) as stated; published either way):
  * A1 mismatch at any rank 0..13 (resummation incomplete);
  * B recursion failing against the measured sign ladder;
  * D imaginary leakage O(1) (no standing wave on the lattice).

Run: python3 tmp/eps_from_parity.py    Out: tmp/eps_from_parity_results.txt
"""
import os
import sys
import math
import time

import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poisson_dual as PD

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "eps_from_parity_results.txt")
_f = open(OUT, "w")


def emit(s=""):
    print(s, flush=True)
    _f.write(s + "\n")
    _f.flush()


# ---------------------------------------------------------------------------
# The frozen profile W(x) = theta_inf(x) * (F + H)(x), mirroring
# poisson_dual.arch_integral (sign=-1 elliptic branch, iota=1) EXACTLY.
# ---------------------------------------------------------------------------
P_, K_ = 2, 1
SCALE = 2.0 * P_ ** (K_ / 2.0)          # 2 p^{k/2} = 2 sqrt(2)


def W_profile(x, l, f):
    th = PD.theta_inf_profile(x, -1, K_)
    if th == 0.0:
        return 0.0
    edge = abs(1.0 - x * x)
    edge = max(edge, 1e-9)
    afe_arg = l * f * f / (SCALE * math.sqrt(edge))
    Fw = float(PD.F_profile(afe_arg))
    Hw = float(PD.H_profile(afe_arg, 1)) / math.sqrt(SCALE * SCALE * edge)
    return th * (Fw + Hw)


def cval_of(l, f):
    return P_ ** (K_ / 2.0) / (2.0 * l * f * f)


# ---------------------------------------------------------------------------
# Bessel table (mpmath), cached per z.
# ---------------------------------------------------------------------------
_bessel_cache = {}


def bessel_row(z, nmax):
    key = (round(z, 12), nmax)
    if key not in _bessel_cache:
        _bessel_cache[key] = np.array(
            [float(mp.besselj(n, z)) for n in range(nmax + 1)])
    return _bessel_cache[key]


# ---------------------------------------------------------------------------
# TEST A0: the exact Chebyshev--Bessel Hankel pair (anchor).
# ---------------------------------------------------------------------------
def test_A0():
    emit("A0  [anchor] int sqrt(1-x^2) U_r e^{-izx} dx = pi (-i)^r (r+1) J_{r+1}(z)/z")
    N = 8192
    ts = np.linspace(0.0, math.pi, N + 1)
    zs = [0.7, 2.3, 7.1, 19.5]
    worst = 0.0
    for r in range(0, 14):
        G = np.sin((r + 1) * ts) * np.sin(ts)      # sin((r+1)t) sin t
        pairs = []
        for z in zs:
            lhs = np.trapezoid(G * np.exp(-1j * z * np.cos(ts)), ts)
            Jrow = bessel_row(z, r + 2)
            rhs = math.pi * (-1j) ** r * (r + 1) * Jrow[r + 1] / z
            pairs.append((lhs, rhs))
        # normalize per rank by the largest value on the z-grid, so a Bessel
        # zero of J_{r+1} at one z cannot masquerade as an identity failure
        scale = max(max(abs(l_), abs(r_)) for l_, r_ in pairs)
        err = max(abs(l_ - r_) for l_, r_ in pairs) / max(scale, 1e-300)
        worst = max(worst, err)
    ok = worst < 1e-10
    emit(f"    r=0..13, z in {zs}: worst rel err = {worst:.3e}  -> "
         f"{'PASS' if ok else 'FAIL (anchor broken!)'}")
    return ok


# ---------------------------------------------------------------------------
# TEST A1: exact Bessel-ladder resummation of the REAL dual kernel.
# ---------------------------------------------------------------------------
def test_A1(l, f, xis=(0.5, 1.0, 2.0, 4.0, 8.0), N=8192, nmax=400):
    c = cval_of(l, f)
    emit(f"A1  [measured, kill-test] real profile, (l,f)=({l},{f}), c={c:.6f}")
    ts = np.linspace(0.0, math.pi, N + 1)
    xs = np.cos(ts)
    Wv = np.array([W_profile(x, l, f) for x in xs])
    # cosine-coefficient matrix rows n=0..nmax on the theta grid
    ns = np.arange(0, nmax + 1)
    cosmat = np.cos(np.outer(ns, ts))
    all_ok = True
    ctrl_min = float("inf")
    for r in range(0, 14):
        G = Wv * np.sin((r + 1) * ts)
        # cosine coefficients a_n = (2/pi) int G cos(nt) dt  (a_0: 1/pi)
        a = (2.0 / math.pi) * np.trapezoid(cosmat * G[None, :], ts, axis=1)
        a[0] *= 0.5
        # parity law: a_n = 0 unless n == r mod 2
        offpar = np.max(np.abs(a[(ns % 2) != (r % 2)]))
        scale_a = max(np.max(np.abs(a)), 1e-300)
        # truncation index
        keep = np.abs(a) > 1e-15 * scale_a
        ncut = int(ns[keep][-1]) if keep.any() else 0
        errs, ctrls, qturns = [], [], []
        for xi in xis:
            z = 2.0 * math.pi * xi * c
            I_ref = np.trapezoid(G * np.exp(-1j * z * xs), ts)
            Jrow = bessel_row(z, ncut + 1)
            phases = (-1j) ** (ns[:ncut + 1] % 4)
            I_sum = math.pi * np.sum(a[:ncut + 1] * phases * Jrow[:ncut + 1])
            I_ctrl = math.pi * np.sum(a[:ncut + 1] * phases * Jrow[1:ncut + 2])
            errs.append(abs(I_ref - I_sum))
            ctrls.append(abs(I_ref - I_ctrl))
            qturns.append(abs(((1j) ** (r % 4) * I_ref).imag))
        m = max(max(abs(np.trapezoid(G * np.exp(-2j * math.pi * x * c * xs), ts))
                    for x in xis), 1e-300)
        rel = max(errs) / m
        # the control must break where the kernel is informative: max over xi
        relc = max(ctrls) / m
        qt = max(qturns) / m
        ok = (rel < 1e-8) and (offpar / scale_a < 1e-12) and (qt < 1e-10)
        all_ok = all_ok and ok
        ctrl_min = min(ctrl_min, relc)
        emit(f"    r={r:>2}: resum rel err {rel:.3e}  off-parity {offpar/scale_a:.3e}"
             f"  quarter-turn {qt:.3e}  ncut={ncut:>3}  "
             f"{'PASS' if ok else 'FAIL (KILL CONDITION)'}")
    emit(f"    CONTROL order-shift: min rel mismatch over ranks = {ctrl_min:.3e}"
         f"  -> {'load-bearing (breaks)' if ctrl_min > 1e-3 else 'CONTROL WEAK'}")
    return all_ok, ctrl_min > 1e-3


# ---------------------------------------------------------------------------
# TEST B: root-number channel recursion (exact) vs measured sign ladder.
# ---------------------------------------------------------------------------
def test_B():
    emit("B   [exact + cross-check] eps(Sym^r Delta) channel assembly (k=12)")
    measured = {1: +1, 3: -1, 5: -1, 7: +1, 9: +1, 11: -1, 13: -1}
    ipow = lambda e: (1j) ** (e % 4)
    ok_all = True
    prev = None
    for r in range(1, 14, 2):
        kap = (r + 1) // 2
        # exact assembly identity: sum_{m odd <= r} (11 m + 1) = kappa(11 kappa + 1)
        s = sum(11 * m + 1 for m in range(1, r + 1, 2))
        assert s == kap * (11 * kap + 1), (r, s)
        eps = ipow(-kap * (11 * kap + 1))
        eps_r = int(round(eps.real))
        match = (eps_r == measured[r]) and abs(eps.imag) < 1e-15
        line = (f"    r={r:>2}: kappa={kap}  i^-(k(11k+1)) = {eps_r:+d}  "
                f"measured {measured[r]:+d}  {'PASS' if match else 'FAIL'}")
        if prev is not None:
            step = ipow(-(11 * r + 1))
            rec = int(round((eps / prev).real))
            rec_ok = rec == int(round(step.real))
            line += (f"   recursion eps_r/eps_(r-2) = {rec:+d} vs i^-(11r+1) = "
                     f"{int(round(step.real)):+d} {'PASS' if rec_ok else 'FAIL'}")
            match = match and rec_ok
        prev = eps
        ok_all = ok_all and match
        emit(line)
    emit(f"    channel-multiplicative root-number ladder: "
         f"{'CONFIRMED' if ok_all else 'BROKEN (KILL CONDITION)'}")
    return ok_all


# ---------------------------------------------------------------------------
# TEST D: paired-lattice reality on the full Kloosterman-weighted dual terms.
# ---------------------------------------------------------------------------
def test_D():
    emit("D   [measured] standing wave on the BE lattice: Im(dual_xi + dual_-xi) = 0")
    ok_all = True
    for (l, f) in [(1, 1), (3, 2)]:
        for r in [2, 3, 4, 5, 7]:
            worst = 0.0
            for xi in [1, 2, 3]:
                vp = PD.dual_xi_term(r, xi, f, l, -1, P_, K_, nx=600)
                vm = PD.dual_xi_term(r, -xi, f, l, -1, P_, K_, nx=600)
                den = max(abs(vp) + abs(vm), 1e-300)
                worst = max(worst, abs((vp + vm).imag) / den)
            ok = worst < 1e-9
            ok_all = ok_all and ok
            emit(f"    (l,f)=({l},{f}) r={r}: max |Im(pair)|/|pair| = {worst:.3e}  "
                 f"{'PASS' if ok else 'FAIL (KILL CONDITION)'}")
    return ok_all


def main():
    t0 = time.time()
    emit("EPS-FROM-PARITY PROBE -- certifier route (b): the seed crossing lattice")
    emit("mechanism: rank moves only the Bessel order/quarter-turn; lattice fixed;")
    emit("           root number multiplicative over seed-clock covers")
    emit("=" * 86)
    a0 = test_A0()
    a1a, ctrl1 = test_A1(1, 1)
    a1b, ctrl2 = test_A1(3, 2, xis=(0.5, 1.0, 2.0, 4.0))
    b = test_B()
    d = test_D()
    emit("=" * 86)
    emit(f"A0 anchor: {'PASS' if a0 else 'FAIL'}   "
         f"A1 resummation: {'PASS' if (a1a and a1b) else 'FAIL'} "
         f"(controls break: {ctrl1 and ctrl2})   "
         f"B eps ladder: {'PASS' if b else 'FAIL'}   D pair reality: {'PASS' if d else 'FAIL'}")
    if a0 and a1a and a1b and b and d and ctrl1 and ctrl2:
        emit("VERDICT: route (b) SURVIVES the kill-test. On the real trace-formula")
        emit("  terms the dual kernel IS its exact Bessel-order-ladder resummation")
        emit("  (rank = order, quarter-turn (-i)^n per order, lattice rank-fixed);")
        emit("  the paired lattice terms are real (standing wave present termwise);")
        emit("  and the measured root-number ladder is exactly channel-multiplicative")
        emit("  over seed-clock covers.  The registration skeleton is on the lattice.")
    else:
        emit("VERDICT: kill condition hit -- route (b) as stated is DEAD or damaged;")
        emit("  see FAIL lines (published per the falsifiability register).")
    emit(f"[done] {time.time()-t0:.0f}s -- results in {OUT}")


if __name__ == "__main__":
    main()
