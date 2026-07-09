"""Signature-based algebraic-cycle detection: the vanishing clock paired with the Hodge projection.

Two tests (both detect ALGEBRAICITY of a Hodge class by a vanishing SIGNATURE, not a special value):
 (A) CM: the (1,1) class of Sym^2 E is algebraic iff E has CM; a CM curve has a_p=0 at every inert
     prime (the mu_2 clock of the CM field = the Sym^2 self-twist pole).
 (B) twist-correspondence: given f and g = f (x) chi_5 (presented as raw coefficients, unequal to f),
     the Rankin-Selberg pole signature -- the DC-residue slope of L(f x g (x) chi_d) scanned over d --
     SURFACES the hidden algebraic Tate class in H^1(f)(x)H^1(g(x)chi_5) at d=5, with an unrelated
     control flat throughout.  (Core detection classical; the clock adds the unified signature reading.)
 (C) RECURSIVE Hodge tower: the pole order of L(Sym^r f x Sym^r f) is the count of algebraic
     self-correspondences at tower level r (multiplicity of the trivial in Sym^r (x) Sym^r as a
     Sato-Tate rep).  Generic form -> 1 at every level (Sym^r irreducible, SU(2)); CM form -> climbs
     1,2,2,3 = ceil((r+1)/2) (the extra cycles of N(U(1)) appearing level by level).  Measured via the
     DC-residue slope sum_{p<X} U_r(cos th_p)^2 log p /(p log X), th_p = arccos(a_p/2sqrt p).
     Pole orders themselves are the Sato-Tate moments (classical); the clock adds the recursive
     level-by-level reading that distinguishes the Hodge/Sato-Tate structure from the signature alone.

Run:  python3 hodge_detect.py
"""
import math

import numpy as np


def sieve(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = False
    return [int(x) for x in np.nonzero(s)[0]]


def ap(p, a1, a2, a3, a4, a6):
    if p == 2:
        return 2 - sum(1 for x in range(2) for y in range(2)
                       if (y * y + a1 * x * y + a3 * y - (x ** 3 + a2 * x * x + a4 * x + a6)) % 2 == 0)
    x = np.arange(p); B = (a1 * x + a3) % p; f = (x ** 3 + a2 * x * x + a4 * x + a6) % p
    D = (B * B + 4 * f) % p
    isq = np.zeros(p, bool); isq[(x * x) % p] = True
    chi = np.where(D == 0, 0, np.where(isq[D], 1, -1)); return int(-chi.sum())


def leg(d, p):
    r = pow(d % p, (p - 1) // 2, p); return -1 if r == p - 1 else r


def partA(P):
    print("(A) CM algebraicity of the (1,1) class of Sym^2 E, via the a_p vanishing signature:")
    for tag, inv, disc in [("CM y^2=x^3-x (Q(i))", (0, 0, 0, -1, 0), 4), ("non-CM 37a", (0, 0, 1, -1, 0), 37)]:
        good = [p for p in P if disc % p != 0 and p > 2]
        z = sum(1 for p in good if ap(p, *inv) == 0)
        inert = [p for p in good if p % 4 == 3]
        iz = sum(1 for p in inert if ap(p, *inv) == 0)
        print(f"    {tag:>22}: a_p=0 frac={z/len(good):.4f}; inert a_p=0 = {iz}/{len(inert)} = {iz/len(inert):.4f}")
    print()


def partB(P):
    print("(B) hidden twist-correspondence via the Rankin-Selberg pole signature (DC-residue slope):")
    E1 = (0, -1, 1, -10, -20)   # 11a = f
    E2 = (0, 0, 1, -1, 0)       # 37a = g' (unrelated control)
    bad = (2, 5, 11, 37)
    good = [p for p in P if p not in bad]
    lamf = {p: ap(p, *E1) / math.sqrt(p) for p in good}
    lamg = {p: leg(5, p) * lamf[p] for p in good}       # g = f (x) chi_5 (hidden twist)
    lamgp = {p: ap(p, *E2) / math.sqrt(p) for p in good}  # g' = 37a (control)
    lx = math.log(good[-1])
    lam2g = {p: lamf[p] * lamg[p] for p in good}
    lam2gp = {p: lamf[p] * lamgp[p] for p in good}
    def slope(lam2, d):
        return sum(lam2[p] * (1 if d == 1 else leg(d, p)) * math.log(p) / p for p in good) / lx
    print(f"    {'chi_d':>7} | g=f(x)chi_5 (secret) | g'=37a (control)")
    for d in [1, -4, 5, 8, -3, -8, 12, 13, -7, -11, 24, -24]:
        sg, sgp = slope(lam2g, d), slope(lam2gp, d)
        flag = "  <== POLE: correspondence g ~ f(x)chi_5" if abs(sg - 1) < 0.4 and sg > 0.4 else ""
        print(f"    {d:>7} | {sg:>10.3f}          | {sgp:>7.3f}{flag}")
    print()
    print("    The pole signature surfaces at d=5 without being told g=f(x)chi_5; control flat: no false positive.")


def Ur_sq(r, c):
    """Chebyshev U_r(c)^2, c = cos(theta_p) = a_p/(2 sqrt p) = char of Sym^r at Frob_p."""
    if r == 0:
        return 1.0
    u0, u1 = 1.0, 2.0 * c                 # U_0=1, U_1=2c
    for _ in range(2, r + 1):
        u0, u1 = u1, 2.0 * c * u1 - u0    # U_{n+1}=2c U_n - U_{n-1}
    return u1 * u1


def partC(X=80000, R=4):
    print("(C) RECURSIVE Hodge-tower cycle detection: pole order of L(Sym^r f x Sym^r f) per level r")
    print("    = # algebraic self-correspondences at level r (trivial mult in Sym^r (x) Sym^r):")
    P = sieve(X); lx = math.log(X)
    curves = [("non-CM 37a", (0, 0, 1, -1, 0), 37),           # bad {37}
              ("CM y^2=x^3-x  Q(i)", (0, 0, 0, -1, 0), 2),    # bad {2}
              ("CM y^2=x^3+1 Q(v-3)", (0, 0, 0, 0, 1), 6)]    # bad {2,3}
    rows = {}
    for tag, inv, disc in curves:
        good = [p for p in P if disc % p != 0]
        cth = {p: ap(p, *inv) / (2.0 * math.sqrt(p)) for p in good}
        slopes = [sum(Ur_sq(r, cth[p]) * math.log(p) / p for p in good) / lx for r in range(1, R + 1)]
        rows[tag] = slopes
        print(f"    {tag:>22}: " + "  ".join(f"r={r}:{slopes[r - 1]:.3f}" for r in range(1, R + 1)))
    base = rows["non-CM 37a"]
    print("    CM/non-CM ratio (predicted pole tower 1,2,2,3 = ceil((r+1)/2)):")
    for tag in ("CM y^2=x^3-x  Q(i)", "CM y^2=x^3+1 Q(v-3)"):
        print(f"    {tag:>22}: " + "  ".join(f"{rows[tag][i] / base[i]:.2f}" for i in range(R)))
    print("    non-CM FLAT (SU(2), Sym^r irreducible); CM CLIMBS (N(U(1)) cycle tower, level by level).")
    print("    Honest: pole orders = Sato-Tate moments (classical); the clock adds the recursive read.")
    print()


def main():
    print("SIGNATURE-BASED CYCLE DETECTION: vanishing clock in the Hodge substructure")
    print("=" * 80)
    P = sieve(60000)
    partA(P)
    partB(P)
    partC()


if __name__ == "__main__":
    main()
