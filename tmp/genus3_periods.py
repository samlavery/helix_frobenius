#!/usr/bin/env python3
"""
genus3_periods.py -- attempt the REAL thing: numerically compute the period
matrix (Riemann matrix tau in the Siegel upper half space) of a genus-3
hyperelliptic curve, VERIFY it (tau symmetric, Im tau positive-definite -- the
Riemann relations; if these fail I got the homology wrong and the result is
garbage, stated as such), and then test the Jacobian for extra endomorphisms /
Hodge classes via integer relations among the tau entries, under the
precision-stability gate from transcendental_boundary.py.

Curve family:  y^2 = f(x),  f monic deg 8, 8 REAL branch points e_1<...<e_8
  (real branch points => clean real-axis integration).
Differentials:  omega_i = x^{i-1} dx / y ,  i=1,2,3.
Homology (canonical hyperelliptic): cuts [e1,e2],[e3,e4],[e5,e6],[e7,e8] (f<0),
  a_j around cut j (j=1,2,3);  b_j across gap (e_{2j}, e_{2j+1}) (f>0).
  A[j,i] = oint_{a_j} omega_i,   B[j,i] = oint_{b_j} omega_i,   tau = A^{-1} B.

This is a genuine attempt.  If the Riemann relations verify, the tau is real and
the Hodge test means something; if not, I report the period computation as the
honest frontier it is -- NOT a fake pass.
"""

import mpmath as mp
mp.mp.dps = 40


def period_matrix(roots):
    e = [mp.mpf(r) for r in sorted(roots)]
    assert len(e) == 8
    def negf(x):                       # -f(x) = -prod(x-e_i)  (>0 on the cuts)
        p = mp.mpf(1)
        for ei in e:
            p *= (x - ei)
        return -p
    def posf(x):                       # f(x) (>0 on the gaps)
        p = mp.mpf(1)
        for ei in e:
            p *= (x - ei)
        return p

    oa = mp.matrix(3, 3)               # oa[i,j] = period of differential i over a_j
    obg = mp.matrix(3, 3)              # obg[i,j] = period of differential i over gap j
    # consistent branch: on interval m=(e_m,e_{m+1}), sqrt(f) = i^{7-m} sqrt|f|,
    # so 1/y = i^{m-7}/sqrt|f|.  The phase i^{m-7} alternates per interval.
    ph = [mp.mpf(1), mp.mpc(0, 1), mp.mpf(-1), mp.mpc(0, -1)]
    def phase(m):
        return ph[(m - 7) % 4]
    for j in range(3):
        a_lo, a_hi = e[2*j], e[2*j+1]                 # cut  = interval m=2j   (f<0)
        b_lo, b_hi = e[2*j+1], e[2*j+2]               # gap  = interval m=2j+1 (f>0)
        for i in range(3):
            ia = mp.quad(lambda x: x**i / mp.sqrt(negf(x)), [a_lo, a_hi])
            oa[i, j] = 2 * phase(2*j) * ia
            ib = mp.quad(lambda x: x**i / mp.sqrt(posf(x)), [b_lo, b_hi])
            obg[i, j] = 2 * phase(2*j + 1) * ib
    # canonicalize b-cycles so a_i . b_j = delta_ij :  b_j = beta_j + ... + beta_g
    ob = mp.matrix(3, 3)
    for i in range(3):
        for j in range(3):
            ob[i, j] = sum(obg[i, k] for k in range(j, 3))
    tau = oa ** -1 * ob
    return tau, oa, ob


def riemann_ok(tau):
    sym = max(abs(tau[a, b] - tau[b, a]) for a in range(3) for b in range(3))
    Imt = mp.matrix(3, 3)
    for a in range(3):
        for b in range(3):
            Imt[a, b] = mp.im(tau[a, b])
    # positive-definite check via leading principal minors
    def minor(k):
        M = mp.matrix(k, k)
        for a in range(k):
            for b in range(k):
                M[a, b] = Imt[a, b]
        return mp.det(M)
    pd = all(mp.re(minor(k)) > 0 for k in (1, 2, 3))
    return sym, pd


def rational_entries(tau, maxcoeff=10**8):
    """Which real/imag parts of tau entries are rational (=> extra Hodge structure)?
    Uses PSLQ; a hit must be precision-stable to count (guards overfit)."""
    def is_rat_stable(x):
        if abs(x) < mp.mpf(10)**(-25):
            return True
        hs = []
        for P in (30, 55):
            old = mp.mp.dps; mp.mp.dps = P
            rel = mp.pslq([mp.mpf(x), mp.mpf(1)], maxcoeff=maxcoeff)
            mp.mp.dps = old
            hs.append(None if not rel else max(abs(c) for c in rel))
        return hs[0] is not None and hs[1] is not None and hs[0] == hs[1]
    hits = 0
    for a in range(3):
        for b in range(a, 3):
            for part in (mp.re(tau[a, b]), mp.im(tau[a, b])):
                if is_rat_stable(part):
                    hits += 1
    return hits


def run(name, roots, expect):
    print(f"\n--- {name}   roots={roots} ---")
    tau, A, B = period_matrix(roots)
    sym, pd = riemann_ok(tau)
    print(f"  tau symmetric to {mp.nstr(sym,3)} ;  Im(tau) positive-definite: {pd}")
    if sym > mp.mpf(10)**(-20) or not pd:
        print("  *** Riemann relations FAIL -> period matrix not trustworthy; "
              "not a valid test (honest: the homology/branch handling is the hard part).")
        return None
    print("  Riemann relations verified -> tau is a genuine Siegel point.")
    hits = rational_entries(tau)
    print(f"  precision-stable rational tau-entries (extra Hodge structure): {hits}")
    print(f"  expectation ({expect})")
    return hits


def main():
    print("=" * 70)
    print("REAL genus-3 period matrices + Hodge/endomorphism test (an attempt)")
    print("=" * 70)
    # generic curve: 8 generic real roots -> expect a GENERIC Jacobian (no extra)
    run("generic", [-3, -2, -1, -0.4, 0.7, 1.5, 2.8, 4.1], "generic: few/no stable rational entries")
    # a symmetric curve y^2 = prod(x^2 - k^2): extra automorphism x->-x -> real multiplication
    run("symmetric (x->-x)", [-4, -3, -2, -1, 1, 2, 3, 4],
        "x->-x symmetry: expect extra structure (more stable rational entries)")


if __name__ == "__main__":
    main()
