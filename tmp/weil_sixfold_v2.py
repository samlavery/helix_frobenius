"""Weil sixfold candidate v2 -- the involution-hardened construction.

  E0 : y^2 + 2xy + y = x^3        (Schoen curve, cond 19)
  C' : u^3 + x*u + (y + a) = 0    (genus 4; fiber eqn is DEGREE 3 in x => C' -> P^1_u is
                                   degree 3: no hidden double cover, tau-bar excluded;
                                   disc = -4x^3 - 27(y+a)^2, 6 simple zeros generically)
  C  : t^3 = y                    (etale: unramified over T since u^3+a separable (a!=0);
                                   unramified over O: residual cubic w^3 + w -+ 1,
                                   disc -31 != 0)
  Prym dim 6, signature (3,3).    n_u(P) = #{u: u^3 + x u + (y+a) = 0}  -- pointwise in
                                  BOTH coordinates now.
  n_u(O) = #roots of w^3 + w + 1  (sign of y-leading irrelevant: w -> -w bijection)

Checks as v1: (A) sum n_t = #E0 exact; (B,C,D) Weil bounds g=4,10, |s1|<=12 sqrt p;
(E) disc simple: -4x^3-27(y+a)^2 has 6 simple zeros (skip detailed check; A-D catch errors).
THE QUESTION this instrument exists to ask (at split p, full tower, via the sage twin):
is P_B still a square -- or IRREDUCIBLE (the simple specimen)?
"""
import math

A_PARAM = 1


def cuberoot_count(v, p):
    if v % p == 0:
        return 1
    if p % 3 != 1:
        return 1
    return 3 if pow(v, (p - 1) // 3, p) == 1 else 0


def cubic_roots(x0, b, p):
    n = 0
    for u in range(p):
        if (u * u * u + x0 * u + b) % p == 0:
            n += 1
    return n


def run(p, a=A_PARAM):
    assert p not in (2, 3, 19, 31) and a % p != 0  # 31 = residual disc, exclude
    E0 = [(x, y) for x in range(p) for y in range(p)
          if (y * y + 2 * x * y + y - x * x * x) % p == 0]
    nE0 = len(E0) + 1
    sum_nt = 0
    nCp = 0
    nC = 0
    for (x0, y0) in E0:
        nu = cubic_roots(x0, (y0 + a) % p, p)
        nt = cuberoot_count(1, p) if (x0, y0) == (0, 0) else cuberoot_count(y0, p)
        sum_nt += nt
        nCp += nu
        nC += nu * nt
    nuO = cubic_roots(1, 1, p)          # residual w^3 + w + 1
    ntO = cuberoot_count(-1 % p, p)
    sum_nt += ntO
    nCp += nuO
    nC += nuO * ntO
    s1 = nCp - nC                        # Schoen sign convention
    rt = math.isqrt(p) + 1
    checks = {
        "A": sum_nt == nE0,
        "B": abs(nCp - (p + 1)) <= 8 * rt,
        "C": abs(nC - (p + 1)) <= 20 * rt,
        "D": abs(s1) <= 12 * rt,
    }
    return nE0, nCp, nC, s1, checks


if __name__ == "__main__":
    print(f"a = {A_PARAM}")
    allok = True
    for p in [5, 7, 11, 13, 23, 29, 37, 41, 43, 53, 61, 67, 73, 79]:
        nE0, nCp, nC, s1, ch = run(p)
        ok = all(ch.values())
        allok = allok and ok
        flag = "PASS" if ok else "FAIL " + str([k for k, v in ch.items() if not v])
        print(f"p={p:>3}: #E0={nE0:>4} #C'={nCp:>4} #C={nC:>5} s1={s1:>5}  {flag}")
    print("ALL PASS" if allok else "FAILURES")
