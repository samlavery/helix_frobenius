#!/usr/bin/env python3
"""The open measurement: rung-5 zero-containment for a Maass form.

Target: Z(Lambda(Sym3 f)) <= Z(Lambda(f x Sym4 f)) for f the first Maass cusp
form on SL(2,Z) (LMFDB 1.0.1.1.1, R = 9.5336952613..., odd, Fricke +1),
where -- unlike the Delta certification -- containment is nobody's theorem:
it is equivalent to entirety of Lambda(Sym5 f), the gateway past the
Kim--Shahidi record.  Evaluator = containment_bench2.Precise, certified on
Delta at the 1e-13 floor.

Conventions (odd form => every Sym^r channel carries sgn):
  gamma(Sym3) = prod GammaR(s + 1 + i m R), m in {3,1,-1,-3};   eps3 = +1
  gamma(Sym5) = same with m in {5,3,1,-1,-3,-5};                eps5 = -1
  gamma(pair) = gamma(Sym5) gamma(Sym3);                        epsP = -1
(sgn-pair count: eps = (-1)^{#pairs} = +1, -1, -1; epsP = eps5*eps3 checks.)

Epistemic register: Lambda_P (JPSS) and Lambda3 (Kim--Shahidi) are LICENSED
entire objects -- the primary measurement uses only these.  The Lambda5
split evaluator presumes the OPEN functional equation; its product-identity
residual is reported as a secondary diagnostic, not an instrument check.

Certificate battery (none involve Lambda5): (a) Hecke-recursion cross-check
of built a(n) against LMFDB data at every composite n <= 1000; (b) reality
structure on the line; (c) N-stability 800 vs 1000; (d) h-stability.
Coefficient certification 1e-67 (LMFDB rigor tables); floor expectation set
by N and the window, measured by the battery.
"""
import sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from containment_bench2 import Precise, dirichlet_conv_mp

mp.mp.dps = 45

HERE = os.path.dirname(os.path.abspath(__file__))


def load_data():
    meta = json.load(open(os.path.join(HERE, 'maass_1_0_1_1_1_meta.json')))['data'][0]
    sp = meta['spectral_parameter']
    R = mp.mpf(sp['data'] if isinstance(sp, dict) else sp)
    co = json.load(open(os.path.join(HERE, 'maass_1_0_1_1_1_coeffs.json')))['data'][0]
    a = [mp.mpf(0)] * 1001
    for i, c in enumerate(co['coefficients']):
        a[i + 1] = mp.mpf(c['data']) if isinstance(c, dict) else mp.mpf(c)
    errs = co['coefficient_errors']
    emax = max(mp.mpf(e['data']) if isinstance(e, dict) else mp.mpf(e) for e in errs[1:])
    return R, a, emax


def primes_upto(N):
    sieve = [True] * (N + 1)
    ps = []
    for p in range(2, N + 1):
        if sieve[p]:
            ps.append(p)
            for q in range(p * p, N + 1, p):
                sieve[q] = False
    return ps


def sym_coeffs_from_ap(r, N, a):
    """lam_{Sym^r}(n) for n <= N from Hecke a(p) via unit-circle/real Satake."""
    lam = [mp.mpf(0)] * (N + 1)
    lam[1] = mp.mpf(1)
    for p in primes_upto(N):
        ap = a[p]
        disc = mp.sqrt(mp.mpc(ap * ap - 4))
        alpha = (ap + disc) / 2
        wts = [alpha ** (r - 2 * j) for j in range(r + 1)]
        kmax = 0
        pk = p
        while pk <= N:
            kmax += 1
            pk *= p
        loc = [mp.mpc(1)] + [mp.mpc(0)] * kmax
        for w in wts:
            for k in range(1, kmax + 1):
                loc[k] = loc[k] + w * loc[k - 1]
        # multiplicative assembly
        powvals = [mp.mpf(1)]
        pk = 1
        for k in range(1, kmax + 1):
            pk *= p
            powvals.append(pk)
        newlam = lam[:]
        for k in range(1, kmax + 1):
            base = int(powvals[k])
            ck = loc[k].real  # self-dual banks are real
            for m in range(1, N // base + 1):
                if m % p != 0 and lam[m] != 0:
                    newlam[m * base] = lam[m] * ck
        lam = newlam
    return lam


def std_coeffs_from_ap(N, a):
    """Rebuild a(n) multiplicatively from a(p) -- the Hecke cross-check."""
    return sym_coeffs_from_ap(1, N, a)


def main():
    t0 = time.time()
    R, a, emax = load_data()
    print(f"# form 1.0.1.1.1  R = {mp.nstr(R, 20)}...  coeff-error <= {float(emax):.1e}")
    N = 1000

    # (a) Hecke-recursion cross-check at every n <= N
    built = std_coeffs_from_ap(N, a)
    dev = max(abs(built[n] - a[n]) for n in range(1, N + 1))
    print(f"# Hecke cross-check: max |built a(n) - data a(n)| over n<=1000 = {float(dev):.2e}")
    if dev > 1e-30:
        print("# ABORT: convention mismatch"); return

    lam3 = sym_coeffs_from_ap(3, N, a)
    lam5 = sym_coeffs_from_ap(5, N, a)
    cpair = dirichlet_conv_mp(lam5, lam3, N)
    i = mp.mpc(0, 1)
    g3 = [1 + i * m * R for m in (3, 1, -1, -3)]
    g5 = [1 + i * m * R for m in (5, 3, 1, -1, -3, -5)]
    T0, h = 70.0, 0.02
    L3 = Precise(g3, lam3, N, mp.mpf(1), h=h, T0=T0)
    Lp = Precise(g5 + g3, cpair, N, mp.mpf(-1), h=h, T0=T0)
    print(f"# tables built in {time.time()-t0:.1f}s  (N={N}, dps={mp.mp.dps}, T0={T0}, h={h})")

    # (b) reality structure: eps3=+1 => Lambda3 real on line; epsP=-1 => imaginary
    s0 = mp.mpc(0.5, 1.1)
    v3, vp = L3.value(s0), Lp.value(s0)
    print(f"# reality at t=1.1: |Im L3|/|L3| = {float(abs(v3.imag)/abs(v3)):.2e} (want ~0), "
          f"|Re Lp|/|Lp| = {float(abs(vp.real)/abs(vp)):.2e} (want ~0)")

    # (c) N-stability and (d) h-stability at a strip point
    sA = mp.mpc(0.5, 2.0)
    Lp800 = Precise(g5 + g3, cpair, 800, mp.mpf(-1), h=h, T0=T0)
    print(f"# N-stability at t=2: |Lp(1000)-Lp(800)| = {float(abs(Lp.value(sA)-Lp800.value(sA))):.3e}"
          f"   scale |Lp| = {float(abs(Lp.value(sA))):.3e}")
    Lph = Precise(g5 + g3, cpair, N, mp.mpf(-1), h=0.03, T0=T0)
    print(f"# h-stability at t=2: |Lp(h=.02)-Lp(h=.03)| = {float(abs(Lp.value(sA)-Lph.value(sA))):.3e}")

    # zeros of Lambda3 (real on the line) by sign change + bisection
    f3 = lambda t: L3.value(mp.mpc(0.5, t)).real
    roots, tprev, vprev = [], mp.mpf("0.3"), f3(mp.mpf("0.3"))
    t = mp.mpf("0.35")
    while t < 8 and len(roots) < 4:
        v = f3(t)
        if vprev * v < 0:
            aa, bb = tprev, t
            fa = f3(aa)
            for _ in range(55):
                m2 = 0.5 * (aa + bb)
                fm = f3(m2)
                if fa * fm <= 0:
                    bb = m2
                else:
                    aa, fa = m2, fm
            roots.append(0.5 * (aa + bb))
        tprev, vprev = t, v
        t += mp.mpf("0.05")
    print(f"# zeros of Lambda(Sym3 f): {[mp.nstr(r, 12) for r in roots]}")

    # THE OPEN MEASUREMENT
    print("# containment measurement (OPEN CASE -- not a theorem for Maass):")
    for r in roots:
        vz = abs(Lp.value(mp.mpc(0.5, r)))
        loc = max(abs(Lp.value(mp.mpc(0.5, r + d))) for d in (-0.5, -0.25, 0.25, 0.5))
        print(f"#   t={mp.nstr(r, 12)}: |L_pair(rho)| = {float(vz):.3e}   "
              f"local scale = {float(loc):.3e}   ratio = {float(vz/loc):.3e}")
    if len(roots) > 1:
        tc = 0.5 * (roots[0] + roots[1])
        print(f"# control t={mp.nstr(tc, 6)}: |L_pair| = {float(abs(Lp.value(mp.mpc(0.5, tc)))):.3e}")

    # secondary diagnostic: the product identity with the CANDIDATE Lambda5
    L5 = Precise(g5, lam5, N, mp.mpf(-1), h=h, T0=T0)
    print("# secondary: product residual with candidate Lambda5 (presumes the OPEN FE):")
    for t in (1.1, 2.0, 3.0):
        s = mp.mpc(0.5, t)
        aP, bP = Lp.value(s), L5.value(s) * L3.value(s)
        den = max(abs(aP), abs(bP), mp.mpf(10) ** (-40))
        print(f"#   t={t}: rel-resid = {float(abs(aP-bP)/den):.3e}")
    print(f"# total {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
