"""Dim-8 hunt: tune a genus-5 degree-3 cover of E0 (etale-Z/3 Prym => dim-8 Weil).

Index formula (proven, 4-specimen verified): g' = 3K - I + 1, K = pole renormalization,
I = index of Z[u] in the maximal order.  Genus 5 <=> I = 3K - 4 >= 2: the disc MUST carry
non-branch double zeros.  E0 has rank 0 ({O, T, T'}, all x = 0) => a rational finite double
zero is impossible => hunt a CONJUGATE QUADRATIC PAIR: config (K, I) = (2, 0_O + 2_pair).

Family F3 (disc factors rationally):
  E0 : y^2 + 2xy + y = x^3,   G = y^2 + (2x+1)y - x^3
  C' : u^3 - 3 d^2 x^2 u + B = 0,   B = (x + beta) y + gamma x + a
  A = -3 d^2 x^2  =>  disc = -4A^3 - 27B^2 = 27 (2 d^3 x^3 - B)(2 d^3 x^3 + B)
  v_O(A) = -4, v_O(B) = -5 => K = 2; O-polygon (0,-5),(1,-4),(3,0): slopes 1,2 integral
  => O unramified, v_O(disc) = -12 => ind_O = 0.
  Generic member: 12 simple branch points => g' = 7 (dim 12).
  TUNED: F+ = 2 d^3 x^3 + B acquires a conjugate-pair double zero on E0
  <=> disc_x(N+) = 0, N+ = Res_y(G, F+) = Q^2 - (2x+1)(x+b)Q - x^3(x+b)^2,
      Q = 2 d^3 x^3 + gamma x + a   (F+ linear in y: (x+b) y* = -Q)
  => I = 2, Sigma = 12 - 4 = 8, g' = 5, Prym dim 8, signature (4,4).
  Trap at dim 8: W4^2 = C(8,4)/3^m = 70/3^m, 70 coprime to 3 => fires for ALL m >= 1.

Per-hit exact verification:
  V1 gcd(N+, N+') = irreducible quadratic g2(x); g2(0) != 0; (x+b) not | g2
  V2 cofactor N+/g2^2 = quadratic, squarefree, coprime to g2
  V3 N- squarefree; gcd(N+, N-) = 1
  V4 genuine tangency: g2 | numerator of J(x) = [F+_x G_y - F+_y G_x] at y = y*(x)
  V5 x-etale at the pair: gcd(g2, 4x^3 + (2x+1)^2) = 1   (G_y != 0 there)
  V6 no triple root: A vanishes only at x = 0 and g2(0) != 0  (=> index pair is SPLIT:
     tame e=2 would force odd local disc valuation -- double zero is unramified)
  V7 T/T' fibers separable: a != 0, a != beta
Then a k=1 point-count battery (checks A-D, Weil bounds for g' = 5, g_C = 13, Prym 8).
"""
import sys
import math
from fractions import Fraction

import sympy as sp

x, y, aa = sp.symbols('x y a')

G = y**2 + (2*x + 1)*y - x**3
GX = sp.diff(G, x)
GY = sp.diff(G, y)
ETALE_POLY = 4*x**3 + (2*x + 1)**2          # Res_y(G, G_y) up to constant


def nplus(d, beta, gamma, a=aa):
    Q = 2*d**3*x**3 + gamma*x + a
    return sp.expand(Q**2 - (2*x + 1)*(x + beta)*Q - x**3*(x + beta)**2)


def nminus(d, beta, gamma, a):
    Qm = 2*d**3*x**3 - gamma*x - a
    return sp.expand(Qm**2 + (2*x + 1)*(x + beta)*Qm - x**3*(x + beta)**2)


def rational_roots_in_a(poly_in_a):
    p = sp.Poly(poly_in_a, aa)
    if p.degree() < 1:
        return []
    roots = []
    for fac, _mult in p.factor_list()[1]:
        if sp.Poly(fac, aa).degree() == 1:
            c1, c0 = sp.Poly(fac, aa).all_coeffs()
            roots.append(sp.Rational(-c0, c1))
    return sorted(set(roots))


def verify(d, beta, gamma, a0):
    """Exact verification battery. Returns (ok, report_lines)."""
    rep = []
    Np = sp.Poly(nplus(d, beta, gamma, a0), x)
    Nm = sp.Poly(nminus(d, beta, gamma, a0), x)
    if a0 == 0 or a0 == beta:
        return False, ["V7 FAIL: a in {0, beta}"]
    g2 = sp.gcd(Np, sp.Poly(Np.diff(x), x))
    if sp.Poly(g2, x).degree() != 2:
        return False, [f"V1 FAIL: gcd degree {sp.Poly(g2, x).degree()} != 2"]
    if len(sp.Poly(g2, x).factor_list()[1]) != 1 or \
            any(sp.Poly(f, x).degree() != 2 for f, _ in sp.Poly(g2, x).factor_list()[1]):
        return False, ["V1 FAIL: g2 reducible (rational double => E0 rank-0 clash or split pair)"]
    if g2.eval(0) == 0:
        return False, ["V1 FAIL: g2(0) = 0"]
    if g2.eval(-beta) == 0:
        return False, ["V1 FAIL: x = -beta root (spurious fiber mechanism)"]
    rep.append(f"V1 PASS: g2 = {g2.as_expr()} irreducible quadratic")
    cof = sp.div(Np, g2**2, x)
    if cof[1] != sp.Poly(0, x):
        return False, ["V2 FAIL: g2^2 does not divide N+"]
    c4 = cof[0]
    if c4.degree() != 2 or sp.gcd(c4, g2).degree() != 0 or \
            sp.gcd(c4, c4.diff(x)).degree() != 0:
        return False, ["V2 FAIL: cofactor not squarefree-quadratic-coprime"]
    rep.append(f"V2 PASS: cofactor {c4.as_expr()} squarefree, coprime")
    if sp.gcd(Nm, Nm.diff(x)).degree() != 0 or sp.gcd(Np, Nm).degree() != 0:
        return False, ["V3 FAIL: N- not squarefree or shares roots with N+"]
    rep.append("V3 PASS: N- squarefree, coprime to N+")
    # V4 genuine tangency: J at y = y*(x) = -Q/(x+beta)
    Q = 2*d**3*x**3 + gamma*x + a0
    ystar = -Q/(x + beta)
    Fp = 2*d**3*x**3 + (x + beta)*y + gamma*x + a0
    J = sp.diff(Fp, x)*GY - sp.diff(Fp, y)*GX
    Jnum = sp.Poly(sp.numer(sp.together(J.subs(y, ystar))), x)
    if sp.rem(Jnum, g2, x) != sp.Poly(0, x):
        return False, ["V4 FAIL: not a genuine tangency (J does not vanish on the pair)"]
    rep.append("V4 PASS: genuine tangency (J = 0 on the pair)")
    if sp.gcd(g2, sp.Poly(ETALE_POLY, x)).degree() != 0:
        return False, ["V5 FAIL: pair sits over a 2-torsion x (x not etale)"]
    rep.append("V5 PASS: x etale at the pair")
    rep.append("V6 PASS: no triple root (A = 0 only at x = 0, g2(0) != 0) => pair is SPLIT")
    rep.append("V7 PASS: T/T' fibers separable")
    return True, rep


# ---------------- k=1 battery (pure modular arithmetic) ----------------

def modfrac(fr, p):
    fr = Fraction(fr)
    if fr.denominator % p == 0:
        return None
    return fr.numerator * pow(fr.denominator, -1, p) % p


def cuberoot_count(v, p):
    if v % p == 0:
        return 1
    if p % 3 != 1:
        return 1
    return 3 if pow(v, (p - 1)//3, p) == 1 else 0


def battery(d, beta, gamma, a0, primes=(7, 13, 31, 37, 43, 61, 67, 73)):
    lines = []
    allok = True
    for p in primes:
        if p in (2, 3, 19):
            continue
        vals = [modfrac(v, p) for v in (d, beta, gamma, a0)]
        if any(v is None for v in vals):
            lines.append(f"p={p}: skipped (denominator)")
            continue
        dp, bp, gp, ap = vals
        A2 = (-3*dp*dp) % p                         # coefficient of x^2 in A
        E0 = [(X, Y) for X in range(p) for Y in range(p)
              if (Y*Y + 2*X*Y + Y - X*X*X) % p == 0]
        nE0 = len(E0) + 1
        sum_nt = 0
        nCp = nC = 0
        for (X, Y) in E0:
            Bv = ((X + bp)*Y + gp*X + ap) % p
            Av = A2*X*X % p
            nu = sum(1 for u in range(p) if (u*u*u + Av*u + Bv) % p == 0)
            nt = cuberoot_count(1, p) if (X, Y) == (0, 0) else cuberoot_count(Y, p)
            sum_nt += nt
            nCp += nu
            nC += nu*nt
        # O unramified: slope-1 branch (1 pt) + slope-2 pair (w^2 = 3 d^2 c_x^2):
        nuO = 1 + (2 if pow(3, (p - 1)//2, p) == 1 else 0)
        ntO = cuberoot_count(-1 % p, p)
        sum_nt += ntO
        nCp += nuO
        nC += nuO*ntO
        s1 = nCp - nC
        rt = math.isqrt(p) + 1
        ch = {"A": sum_nt == nE0,
              "B": abs(nCp - (p + 1)) <= 10*rt,      # g' = 5
              "C": abs(nC - (p + 1)) <= 26*rt,       # g_C = 13
              "D": abs(s1) <= 16*rt}                 # Prym dim 8
        ok = all(ch.values())
        allok = allok and ok
        flag = "PASS" if ok else "FAIL " + str([k for k, v in ch.items() if not v])
        kind = "split" if p % 3 == 1 else "inert"
        lines.append(f"p={p:>3} ({kind}): #E0={nE0:>4} #C'={nCp:>4} #C={nC:>5} "
                     f"s1={s1:>5}  {flag}")
    return allok, lines


# ---------------- Part A: F2 route sanity (expected EMPTY, E0 rank 0) -------------

def f2_scan():
    hits = []
    for n in range(1, 13):
        for m in range(-40, 41):
            if m == 0 or math.gcd(m, n) != 1:
                continue
            N = n**6 - 12*m*m*n**4 + 36*m**4*n*n - 108*m**6
            if N >= 0 and math.isqrt(N)**2 == N:
                hits.append(Fraction(m, n))
    return hits


# ---------------- Part B/C: the hunt ----------------

def hunt(d, beta, gammas, seen, max_hits=6):
    found = []
    for gnum in gammas:
        gamma = sp.Rational(gnum)
        Np = nplus(d, beta, gamma)
        D = sp.discriminant(sp.Poly(Np, x))
        for a0 in rational_roots_in_a(D):
            key = (d, beta, gamma, a0)
            if key in seen:
                continue
            seen.add(key)
            ok, rep = verify(d, beta, gamma, a0)
            tag = "CANDIDATE" if ok else "rejected"
            print(f"[d={d} beta={beta} gamma={gamma} a={a0}] {tag}")
            for r in rep:
                print("   ", r)
            sys.stdout.flush()
            if ok:
                found.append(key)
                if len(found) >= max_hits:
                    return found
    return found


if __name__ == "__main__":
    print("PART A: F2 rational-double route scan (expect empty, E0 rank 0)")
    h = f2_scan()
    print("   F2 hits:", h if h else "NONE (route dead, as predicted)")
    sys.stdout.flush()

    seen = set()
    hits = []
    passes = [
        (1, 0, list(range(-50, 51))),
        (1, 0, [sp.Rational(k, 2) for k in range(-59, 60, 2)]),
        (2, 0, list(range(-30, 31))),
        (3, 0, list(range(-20, 21))),
        (1, 1, list(range(-30, 31))),
        (1, -1, list(range(-30, 31))),
        (1, 2, list(range(-20, 21))),
        (1, -2, list(range(-20, 21))),
    ]
    for (d, beta, gammas) in passes:
        print(f"\nPART B: hunting d={d}, beta={beta}, {len(gammas)} gamma values")
        sys.stdout.flush()
        hits += hunt(sp.Integer(d), sp.Integer(beta), gammas, seen,
                     max_hits=6 - len(hits))
        if len(hits) >= 6:
            break

    print("\n" + "="*60)
    print(f"VERIFIED CANDIDATES: {len(hits)}")
    for (d, beta, gamma, a0) in hits:
        print(f"\n*** C' : u^3 - 3*{d}^2*x^2*u + ((x+{beta})*y + {gamma}*x + {a0}) = 0")
        print("    genus 5 by index formula; running k=1 battery:")
        ok, lines = battery(d, beta, gamma, a0)
        for ln in lines:
            print("   ", ln)
        print("    BATTERY:", "ALL PASS" if ok else "FAILURES")
        print("    next: sage k<=6 tower, FE-completed deg-10 numerator, purity "
              "=> genus-5 certificate; then k<=8 at p=7 for the deg-16 Prym char poly "
              "(simplicity certificate).")
