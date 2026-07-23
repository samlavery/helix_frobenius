"""Weil tenfold candidate -- etale-Z/3 Prym over a genus-6 base (dim-10 track).

  E0 : y^2 + 2xy + y = x^3           (Schoen curve, cond 19, T=(0,0), div(y)=3[T]-3[O])
  C' : u^3 + x*u + (y + x^2 + a) = 0
       genus 6 by the index formula g' = 3K - I + 1:
       v_O(A) = -2, v_O(B) = -4  =>  K = k_O = 2;
       O-polygon (0,-4),(1,-2),(3,0): single slope-4/3 segment => e = 3 at O (tame, d = 2),
       v_O(disc) = -8  =>  ind_O = (-8 + 12 - 2)/2 = 1;
       8 simple finite branch points  =>  Sigma = 8 + 2 = 10  =>  g' = 6.
  C  : t^3 = y                        (etale automatically: div(y) = 3([T]-[O]))
  Prym dim 10, signature (5,5).

  Special fibers: T, T' (x = 0): cubic u^3 + a, separable (a != 0) -- unramified.
  O: TOTALLY RAMIFIED (e = 3, f = 1) => exactly ONE rational point over O at every q;
  n_t there: tau^3 = (unit)^3 => gcd(3, p-1) points (leading coeff is a perfect cube).

  Checks: (A) sum n_t over E0-points = #E0 exact (E0-level t-table validation, v2 verbatim);
  (B) |#C' - (p+1)| <= 12 sqrt(p)  [g' = 6];  (C) |#C - (p+1)| <= 32 sqrt(p)  [g_C = 16];
  (D) |s1| <= 20 sqrt(p)           [Prym dim 10].   s1 = #C' - #C (Schoen sign convention).
  Expectation: s1 = 0 at inert primes (p = 2 mod 3) -- the Weil-type signature.
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
    assert p not in (2, 3, 19) and a % p != 0
    E0 = [(x, y) for x in range(p) for y in range(p)
          if (y * y + 2 * x * y + y - x * x * x) % p == 0]
    nE0 = len(E0) + 1
    sum_nt = 0
    nCp = 0
    nC = 0
    for (x0, y0) in E0:
        nu = cubic_roots(x0, (y0 + x0 * x0 + a) % p, p)
        nt = cuberoot_count(1, p) if (x0, y0) == (0, 0) else cuberoot_count(y0, p)
        sum_nt += nt
        nCp += nu
        nC += nu * nt
    # O: one point on C' (totally ramified), t-fiber tau^3 = cube => gcd(3, p-1) points
    ntO_E0 = cuberoot_count(-1 % p, p)          # E0-level O term for check A only
    sum_nt += ntO_E0
    nCp += 1
    nC += 3 if p % 3 == 1 else 1
    s1 = nCp - nC
    rt = math.isqrt(p) + 1
    checks = {
        "A": sum_nt == nE0,
        "B": abs(nCp - (p + 1)) <= 12 * rt,
        "C": abs(nC - (p + 1)) <= 32 * rt,
        "D": abs(s1) <= 20 * rt,
    }
    return nE0, nCp, nC, s1, checks


if __name__ == "__main__":
    print(f"tenfold k=1 battery, a = {A_PARAM}")
    allok = True
    inert_zero = True
    for p in [5, 7, 11, 13, 23, 29, 31, 37, 41, 43, 53, 61, 67, 73, 79]:
        nE0, nCp, nC, s1, ch = run(p)
        ok = all(ch.values())
        allok = allok and ok
        if p % 3 == 2 and s1 != 0:
            inert_zero = False
        flag = "PASS" if ok else "FAIL " + str([k for k, v in ch.items() if not v])
        print(f"p={p:>3} ({'split' if p % 3 == 1 else 'inert'}): #E0={nE0:>4} "
              f"#C'={nCp:>4} #C={nC:>5} s1={s1:>5}  {flag}")
    print("ALL PASS" if allok else "FAILURES")
    print("inert s1 all zero:", inert_zero, "(Weil-type signature expectation)")
