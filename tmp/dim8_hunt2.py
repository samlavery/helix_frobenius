"""Dim-8 re-roll hunt: the GENERAL 4-parameter family (never scanned before —
the first hunt only searched the F3 slice alpha = -3 delta^2).

  C' : u^3 + alpha x^2 u + (x y + beta y + gamma x + a) = 0   over E0
  v_B = -5, v_A = -4, K = 2; O-polygon (0,-5),(1,-4),(3,0): slopes 1, 2 => O
  unramified, ind_O = 0.  Genus 5 <=> ONE conjugate-pair double zero among the 12
  finite branch points (I = 2)  <=>  N(x) = Res_y(E0, disc) has a repeated
  irreducible-quadratic factor.

  DESIGN LAW (the flex post-mortem): the pair must sit at NON-TORSION quadratic
  points — no auxiliary 3-divisible divisors — so no second magic function, no
  correspondence leak (the flex eightfold died of tangency-at-3-torsion: B1 had
  div = 3[T'] - 3[O], spawning a second mu_3 cover whose elliptic curve invaded
  the Prym; rails saw E0's own factor).  Here g2(0) != 0 excludes torsion x.

  Numeric-first: N(x) via the 2x2-quadratic resultant closed form, np.roots,
  min-root-gap scan over a; refine; rational-reconstruct; sympy exact verify.
"""
import itertools
import math
from fractions import Fraction

import numpy as np
import sympy as sp

P = np.polynomial.polynomial


def Ncoeffs(al, be, ga, a):
    """Ascending coefficients of N(x) = Res_y(G, D), degree 12."""
    L = np.array([be, 1.0])
    M = np.array([a, ga])
    dA = -27.0 * P.polymul(L, L)
    dB = -54.0 * P.polymul(L, M)
    dC = -27.0 * P.polymul(M, M)
    dC = np.pad(dC, (0, 7 - len(dC)))
    dC[6] += -4.0 * al ** 3
    x3dA = np.pad(dA, (3, 0))
    t1 = P.polyadd(dC, x3dA)
    u1 = P.polysub(dB, P.polymul(np.array([1.0, 2.0]), dA))
    u2 = P.polyadd(P.polymul(np.array([1.0, 2.0]), dC), np.pad(dB, (3, 0)))
    return P.polysub(P.polymul(t1, t1), P.polymul(u1, u2))


def mingap(al, be, ga, a):
    c = Ncoeffs(al, be, ga, a)
    if abs(c[-1]) < 1e-9:
        return 1e9
    r = np.roots(c[::-1])
    n = len(r)
    g = 1e9
    for i in range(n):
        for j in range(i + 1, n):
            d = abs(r[i] - r[j])
            if d < g:
                g = d
    return g


xs, As = sp.symbols('x a')


def exact_verify(al, be, ga, a):
    alq, beq, gaq, aq = map(sp.Rational, (al, be, ga, a))
    L = xs + beq
    M = gaq * xs + aq
    dA = -27 * L ** 2
    dB = -54 * L * M
    dC = -4 * alq ** 3 * xs ** 6 - 27 * M ** 2
    t1 = dC + xs ** 3 * dA
    u1 = dB - (2 * xs + 1) * dA
    u2 = (2 * xs + 1) * dC + xs ** 3 * dB
    N = sp.Poly(sp.expand(t1 * t1 - u1 * u2), xs)
    g2 = sp.gcd(N, sp.Poly(N.diff(xs), xs))
    if g2.degree() != 2:
        return False, f"gcd deg {g2.degree()}"
    facs = g2.factor_list()[1]
    if len(facs) != 1 or sp.Poly(facs[0][0], xs).degree() != 2:
        return False, "g2 reducible (rational double impossible: E0 rank 0 clash)"
    if g2.eval(0) == 0:
        return False, "pair at torsion x = 0 (magic-function risk)"
    quo, rem = sp.div(N, g2 ** 2, xs)
    if rem != sp.Poly(0, xs) and not rem.is_zero:
        return False, "g2^2 does not divide N"
    quo = sp.Poly(quo, xs)
    if quo.degree() != 8 or sp.gcd(quo, g2).degree() != 0 or \
            sp.gcd(quo, quo.diff(xs)).degree() != 0:
        return False, "cofactor not squarefree deg-8 coprime"
    if sp.gcd(g2, sp.Poly(4 * xs ** 3 + (2 * xs + 1) ** 2, xs)).degree() != 0:
        return False, "pair over 2-torsion x (not x-etale)"
    if aq == 0 or aq == beq:
        return False, "T/T' fiber degenerate"
    return True, f"g2 = {g2.as_expr()}"


def cuberoot_count(v, p):
    if v % p == 0:
        return 1
    if p % 3 != 1:
        return 1
    return 3 if pow(v, (p - 1) // 3, p) == 1 else 0


def battery(al, be, ga, a, primes=(7, 13, 31, 37, 43, 61, 67, 73, 79, 11, 23, 29, 41)):
    lines, allok, inert_zero = [], True, True
    for p in sorted(primes):
        if p in (2, 3, 19):
            continue
        vals = []
        bad = False
        for v in (al, be, ga, a):
            f = Fraction(v)
            if f.denominator % p == 0:
                bad = True
                break
            vals.append(f.numerator * pow(f.denominator, -1, p) % p)
        if bad or vals[0] % p == 0:
            continue
        alp, bep, gap_, ap = vals
        E0 = [(X, Y) for X in range(p) for Y in range(p)
              if (Y * Y + 2 * X * Y + Y - X * X * X) % p == 0]
        nE0 = len(E0) + 1
        sum_nt = nCp = nC = 0
        for (X, Y) in E0:
            Av = alp * X * X % p
            Bv = (X * Y + bep * Y + gap_ * X + ap) % p
            nu = sum(1 for u in range(p) if (u * u * u + Av * u + Bv) % p == 0)
            nt = cuberoot_count(1, p) if (X, Y) == (0, 0) else cuberoot_count(Y, p)
            sum_nt += nt
            nCp += nu
            nC += nu * nt
        nuO = 1 + (2 if pow((-alp) % p, (p - 1) // 2, p) == 1 else 0)
        ntO = cuberoot_count(-1 % p, p)
        sum_nt += ntO
        nCp += nuO
        nC += nuO * ntO
        s1 = nCp - nC
        rt = math.isqrt(p) + 1
        ch = {"A": sum_nt == nE0, "B": abs(nCp - (p + 1)) <= 10 * rt,
              "C": abs(nC - (p + 1)) <= 26 * rt, "D": abs(s1) <= 16 * rt}
        ok = all(ch.values())
        allok = allok and ok
        kind = "split" if p % 3 == 1 else "inert"
        if p % 3 == 2 and s1 != 0:
            inert_zero = False
        flag = "PASS" if ok else "FAIL " + str([k for k, v in ch.items() if not v])
        lines.append(f"   p={p:>3} ({kind}): #C'={nCp:>4} #C={nC:>5} s1={s1:>4} {flag}")
    return allok, inert_zero, lines


if __name__ == "__main__":
    hits = []
    tried = set()
    print("scanning (alpha, beta, gamma) grid, a in [-40, 40]...")
    for al, be, ga in itertools.product(range(-6, 7), range(-4, 5), range(-6, 7)):
        if al == 0:
            continue
        agrid = np.arange(-40, 40.01, 0.25)
        gaps = np.array([mingap(al, be, ga, av) for av in agrid])
        for i in np.where(gaps < 0.12)[0]:
            lo, hi = agrid[max(i - 1, 0)], agrid[min(i + 1, len(agrid) - 1)]
            for _ in range(70):
                m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
                if mingap(al, be, ga, m1) < mingap(al, be, ga, m2):
                    hi = m2
                else:
                    lo = m1
            astar = (lo + hi) / 2
            if mingap(al, be, ga, astar) > 1e-5:
                continue
            for den in range(1, 33):
                fr = Fraction(round(astar * den), den)
                if abs(float(fr) - astar) < 1e-6 and (al, be, ga, fr) not in tried:
                    tried.add((al, be, ga, fr))
                    ok, msg = exact_verify(al, be, ga, fr)
                    if ok:
                        print(f"*** CANDIDATE al={al} be={be} ga={ga} a={fr}: {msg}")
                        hits.append((al, be, ga, fr))
                    break
    print(f"\nverified candidates: {len(hits)}")
    for (al, be, ga, fr) in hits[:4]:
        print(f"\nC' : u^3 + {al}x^2 u + (xy + {be}y + {ga}x + {fr}) = 0  "
              f"-> genus 5, Prym dim 8, sig (4,4), m = 4, trap 70/81")
        allok, iz, lines = battery(al, be, ga, fr)
        for ln in lines:
            print(ln)
        print("   battery:", "ALL PASS" if allok else "FAILURES",
              "| inert s1 all zero:", iz, "(K-structure prescreen)")
