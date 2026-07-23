"""Weil sixfold candidate: first counts (prime fields, pure Python, no Sage).

TARGET (weil-sixfold-hunt dossier): simple Weil-type abelian SIXFOLD, signature (3,3),
K = Q(sqrt-3), as Prym(C/C') of the etale Z/3 cover of a GENUS-4 base:

  E0 : y^2 + 2xy + y = x^3          (Schoen's curve, conductor 19; T=(0,0), div(y)=3[T]-3[O])
  C' : u^3 + x*u + c = 0  over E0   (NON-GALOIS degree-3 cover, genus 4 -- NO involution:
                                     the decomposability trap of the bielliptic route is
                                     never built)
  C  : t^3 = y  pulled back         (ETALE: T-fiber u^3=-c separable; O-fiber 3 branches by
                                     Newton polygon; so ord(y) on C' divisible by 3 everywhere)

Prym dim = g(C)-g(C') = 10-4 = 6, sigma eigenvalue mult 3 each => (3,3). Weil type over
Q(zeta3). ALL COUNTS EXACT (fiber product over E0):
  #C'(F_q) = sum_P n_u(P),   #C(F_q) = sum_P n_u(P)*n_t(P),   s_k(Prym) = #C - #C'.

SPECIAL PLACES (mirroring tmp/schoen_explicit.py's validated conventions):
  n_t at affine P with y!=0 : #{t : t^3 = y}
  n_t over T (y ord-3 zero) : #{t : t^3 = 1/a3} = #cuberoots(1)   (a3 = 1)
  n_t over O (y ord-3 pole) : #{t : t^3 = -1}
  n_u at affine P           : #{u : u^3 + x*u + c = 0}
  n_u over O                : 1 + #{s : s^2 = -1}   (branches u ~ -c/x rational; u^2 ~ -x,
                              leading of x at O is +1, so pair rational iff -1 is a QR)

CROSS-CHECKS (all must pass; any failure = special-place handling bug, iterate):
  (A) sum_P n_t(P) == #E0(F_p)             (E'' = {t^3=y} is 3-isogenous to E0)
  (B) |#C' - (p+1)| <= 8*sqrt(p)           (Weil, genus 4 -- Weil RH for curves, THEOREM)
  (C) |#C  - (p+1)| <= 20*sqrt(p)          (Weil, genus 10)
  (D) |s_1(Prym)|   <= 12*sqrt(p)          (12 Frobenius eigenvalues)
  (E) disc(x) = -4x^3-27c^2 has 3 distinct roots, none at x=0 (branch simplicity, c!=0)

No RH/GRH anywhere: exact finite arithmetic + Weil's theorem for curves as ceiling.
NEXT (after k=1 validates): GF(p^k) for k<=6 -> Newton -> degree-12 L-poly -> weil_rails
bearings (collective lane / freeze r / order law) + no-orphan occupancy.
"""
import math

C_PARAM = 1  # the one rational parameter; c=1 first


def cuberoot_count(a, p):
    """#{t in F_p : t^3 = a}."""
    if a % p == 0:
        return 1
    if p % 3 != 1:
        return 1  # cubing is a bijection
    return 3 if pow(a, (p - 1) // 3, p) == 1 else 0


def sqrt_count(a, p):
    """#{s in F_p : s^2 = a}."""
    if a % p == 0:
        return 1
    return 2 if pow(a, (p - 1) // 2, p) == 1 else 0


def cubic_root_count(x0, c, p):
    """#{u in F_p : u^3 + x0*u + c = 0} by direct scan (p small) -- exact."""
    n = 0
    for u in range(p):
        if (u * u * u + x0 * u + c) % p == 0:
            n += 1
    return n


def run(p, c=C_PARAM):
    assert p not in (2, 3, 19) and c % p != 0
    # (E) branch simplicity: disc(x) = -4x^3 - 27c^2 squarefree in x, no root at x=0
    roots = [x for x in range(p) if (-4 * x * x * x - 27 * c * c) % p == 0]
    ok_E = 0 not in roots  # simplicity generic; multiplicity check via gcd with derivative
    droots = [x for x in roots if (-12 * x * x) % p == 0]
    ok_E = ok_E and not droots

    # enumerate E0(F_p) affine
    E0 = []
    for x in range(p):
        for y in range(p):
            if (y * y + 2 * x * y + y - x * x * x) % p == 0:
                E0.append((x, y))
    nE0 = len(E0) + 1  # + O

    # counts
    sum_nt = 0
    nCp = 0  # #C'
    nC = 0   # #C
    for (x0, y0) in E0:
        nu = cubic_root_count(x0, c, p)
        if (x0, y0) == (0, 0):          # T : y has ord-3 zero, leading 1/a3 = 1
            nt = cuberoot_count(1, p)
        else:
            nt = cuberoot_count(y0, p)
        sum_nt += nt
        nCp += nu
        nC += nu * nt
    # O
    nuO = 1 + sqrt_count(-1 % p, p)
    ntO = cuberoot_count(-1 % p, p)
    sum_nt += ntO
    nCp += nuO
    nC += nuO * ntO

    s1 = nC - nCp
    rt = math.isqrt(p) + 1
    checks = {
        "A_sum_nt=E0": sum_nt == nE0,
        "B_Cp_Weil": abs(nCp - (p + 1)) <= 8 * rt,
        "C_C_Weil": abs(nC - (p + 1)) <= 20 * rt,
        "D_s1_bound": abs(s1) <= 12 * rt,
        "E_branch_simple": ok_E,
    }
    return nE0, nCp, nC, s1, checks


if __name__ == "__main__":
    print(f"c = {C_PARAM}")
    print(f"{'p':>5} {'#E0':>6} {'#Cprime':>8} {'#C':>7} {'s1':>6}  checks")
    allok = True
    for p in [7, 11, 13, 23, 29, 31, 37, 41, 43, 53, 61, 67, 73, 79]:
        nE0, nCp, nC, s1, ch = run(p)
        ok = all(ch.values())
        allok = allok and ok
        flag = "PASS" if ok else "FAIL " + str([k for k, v in ch.items() if not v])
        print(f"{p:>5} {nE0:>6} {nCp:>8} {nC:>7} {s1:>6}  {flag}")
    print("ALL PASS" if allok else "FAILURES -- iterate special places")
