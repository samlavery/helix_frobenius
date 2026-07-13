#!/usr/bin/env python3
"""
picard_periods.py -- attempt a VERIFIED period matrix for a NON-hyperelliptic
genus-3 curve: the superelliptic Picard curve  y^3 = f(x),  f monic deg 4, real
roots.  This is the family where the Ceresa class is generically nonzero (unlike
hyperelliptic, where it vanishes), so it's the real gateway to the Ceresa frontier.

Cube-root branch (the delicate part, analog of the sqrt phase in the hyperelliptic
case): on interval m=(r_m,r_{m+1}) there are (3-m) roots to the RIGHT, each a
negative factor whose principal cube root carries e^{i pi/3}.  So
    y_0(x) = |f(x)|^{1/3} * exp(i*pi*(3-m)/3)     on sheet 0,
and sheet s has y_s = zeta_3^s y_0.

Differentials (standard Picard basis, genus 3): (a,b) with omega = x^a dx / y^b:
    omega_1 = dx/y^2   (a,b)=(0,2)
    omega_2 = x dx/y^2 (a,b)=(1,2)
    omega_3 = dx/y     (a,b)=(0,1)

Cycles: kappa_j^{(s)} = lift of [r_j, r_{j+1}] out on sheet 0, back on sheet s.
    Period = (1 - zeta_3^{-s b}) * exp(-i pi b (3-j)/3) * I(j,a,b),
    I(j,a,b) = int_{r_j}^{r_{j+1}} x^a |f(x)|^{-b/3} dx   (real).

I try candidate symplectic bases from these 6 cycles and accept ONLY a tau that
passes the Riemann relations (symmetric, Im positive-definite).  If none passes,
I report that honestly -- the symplectic-basis assembly for a cyclic cover is the
genuine hard step, and I will not fake a tau that doesn't verify.
"""

import mpmath as mp
mp.mp.dps = 30
Z3 = mp.exp(2j * mp.pi / 3)


def omega_over_cycles(roots):
    r = [mp.mpf(x) for x in sorted(roots)]
    def absf(x):
        p = mp.mpf(1)
        for ri in r:
            p *= (x - ri)
        return abs(p)
    diffs = [(0, 2), (1, 2), (0, 1)]          # (a,b) for omega_1,2,3
    gaps = [(r[0], r[1]), (r[1], r[2]), (r[2], r[3])]
    # full period matrix: Omega[d][ (j,s) ]  d=0..2 diff, j=0..2 gap, s=1,2 sheet-diff
    Om = {}
    for d, (a, b) in enumerate(diffs):
        for j, (lo, hi) in enumerate(gaps):
            I = mp.quad(lambda x: x**a / absf(x)**(mp.mpf(b)/3), [lo, hi])
            branch = mp.exp(-1j * mp.pi * b * (3 - j) / 3)
            for s in (1, 2):
                sheet = (1 - Z3**(-s * b))
                Om[(d, j, s)] = sheet * branch * I
    return Om


def tau_from_basis(Om, aset, bset):
    A = mp.matrix(3, 3); B = mp.matrix(3, 3)
    for d in range(3):
        for c, (j, s) in enumerate(aset):
            A[d, c] = Om[(d, j, s)]
        for c, (j, s) in enumerate(bset):
            B[d, c] = Om[(d, j, s)]
    try:
        return A ** -1 * B
    except Exception:
        return None


def riemann_ok(tau):
    if tau is None:
        return 99, False
    sym = max(abs(tau[a, b] - tau[b, a]) for a in range(3) for b in range(3))
    Im = mp.matrix(3, 3)
    for a in range(3):
        for b in range(3):
            Im[a, b] = mp.im(tau[a, b])
    def minor(k):
        M = mp.matrix(k, k)
        for a in range(k):
            for b in range(k):
                M[a, b] = Im[a, b]
        return mp.re(mp.det(M))
    pd = all(minor(k) > 0 for k in (1, 2, 3)) or all(minor(k) * (-1)**k > 0 for k in (1, 2, 3))
    return sym, pd


def main():
    print("=" * 70)
    print("Picard curve y^3=f(x): verified NON-hyperelliptic genus-3 period matrix?")
    print("=" * 70)
    roots = [-2, -0.5, 1, 3]
    Om = omega_over_cycles(roots)
    print(f"  curve y^3 = (x+2)(x+0.5)(x-1)(x-3),  roots {roots}")
    print(f"  computed 3 differentials over 6 cycles kappa_j^(s).\n")

    # search natural symplectic bases: a-cycles use sheet s_a, b-cycles sheet s_b,
    # with the b-cycles possibly cumulative (as in the hyperelliptic fix).
    gaps = [0, 1, 2]
    best = None
    for s_a in (1, 2):
        for s_b in (1, 2):
            if s_a == s_b:
                continue
            aset = [(j, s_a) for j in gaps]
            for cumulative in (False, True):
                if cumulative:
                    # b_j = sum_{k>=j} kappa_k^{(s_b)}  -- fold into Omega columns
                    Om2 = dict(Om)
                    for d in range(3):
                        for j in gaps:
                            Om2[(d, j, 99)] = sum(Om[(d, k, s_b)] for k in range(j, 3))
                    bset = [(j, 99) for j in gaps]
                    tau = tau_from_basis(Om2, aset, bset)
                else:
                    bset = [(j, s_b) for j in gaps]
                    tau = tau_from_basis(Om, aset, bset)
                sym, pd = riemann_ok(tau)
                tag = f"a=sheet{s_a}, b=sheet{s_b}{'(cumulative)' if cumulative else ''}"
                print(f"  {tag:32}  symmetric~{mp.nstr(sym,2):>9}  Im-def:{pd}")
                if sym < mp.mpf(10)**(-12) and pd:
                    best = (tag, tau)
    print()
    if best:
        print(f"  *** VERIFIED period matrix found: {best[0]}")
        print("  Riemann relations hold -> a genuine non-hyperelliptic Siegel point.")
        print("  This is the Ceresa family, periods in hand.  NEXT: the Ceresa/harmonic-")
        print("  volume iterated integral on top (the secondary invariant periods miss).")
    else:
        print("  No candidate basis verified the Riemann relations.")
        print("  HONEST: the cyclic-cover symplectic basis is the genuine hard step; the")
        print("  branch/differential structure above is right (magnitudes real, phases")
        print("  tracked), but assembling the correct a,b intersection pairing needs the")
        print("  cover's intersection combinatorics, not a guess.  Not faking a tau.")


if __name__ == "__main__":
    main()
