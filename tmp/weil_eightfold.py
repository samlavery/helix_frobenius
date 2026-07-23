"""Weil EIGHTFOLD candidate -- the flex construction (dim-8 track).

  E0 : y^2 + 2xy + y = x^3        (Schoen curve; T' = (0,-1) is 3-TORSION => a FLEX:
                                   its tangent line y + 2x + 1 has TRIPLE contact)
  psi = 1 + x,  A = -3 psi^2,  B = 2 psi^3 + B1,  B1 = y + 2x + 1  (the flex line)
  C' : u^3 - 3(1+x)^2 u + (2(1+x)^3 + y + 2x + 1) = 0
  disc = -27 * B1 * (4 psi^3 + B1)          (cancellation family: factors for ANY psi)

  Genus 5 by the index formula g' = 3K - I + 1:
    v_O(A) = -4, v_O(B) = -6  =>  K = 2
    O (shift u = psi + w => w^3 + 3 psi w^2 + B1): polygon (0,-3),(2,-2),(3,0):
      slope-1/2 pair (e = 2, d = 1) + slope-2 branch; v_O(disc) = -9 => ind_O = 1
    T' (the flex): v_{T'}(B1) = 3 (triple contact), fiber (u-1)^2(u+2):
      polygon (0,3),(2,0),(3,0): slope -3/2 pair => e = 2, d = 1; v(disc) = 3 => ind = 1
    finite: 6 simple zeros of 4 psi^3 + B1  (d = 6)
    Sigma = 1 + 1 + 6 = 8;  I = 2  =>  g' = 3*2 - 2 + 1 = 5.   Prym dim 8, sig (4,4).
  Trap: W4^2 = C(8,4)/3^m = 70/3^m, 70 coprime to 3 => fires for ALL m >= 1.

  Point counts: O carries TWO rational points of C' at every q (e=2 place with f=1,
  plus the unramified slope-2 branch); each has y-leading = -(cube) => n_t = gcd(3,q-1).
  T-fiber: u^3 - 3u + 3, disc = -135 => exclude p = 5.  T' handled by the affine loop.

  Checks: (A) sum n_t over E0 = #E0; (B) |#C' - (p+1)| <= 10 sqrt(p) [g'=5];
  (C) |#C - (p+1)| <= 26 sqrt(p) [g_C = 13]; (D) |s1| <= 16 sqrt(p) [Prym dim 8].
"""
import math


def cuberoot_count(v, p):
    if v % p == 0:
        return 1
    if p % 3 != 1:
        return 1
    return 3 if pow(v, (p - 1) // 3, p) == 1 else 0


def run(p):
    assert p not in (2, 3, 5, 19)
    E0 = [(x, y) for x in range(p) for y in range(p)
          if (y * y + 2 * x * y + y - x * x * x) % p == 0]
    nE0 = len(E0) + 1
    sum_nt = 0
    nCp = 0
    nC = 0
    for (x0, y0) in E0:
        A = (-3 * (1 + x0) * (1 + x0)) % p
        B = (2 * (1 + x0) ** 3 + y0 + 2 * x0 + 1) % p
        nu = sum(1 for u in range(p) if (u * u * u + A * u + B) % p == 0)
        nt = cuberoot_count(1, p) if (x0, y0) == (0, 0) else cuberoot_count(y0, p)
        sum_nt += nt
        nCp += nu
        nC += nu * nt
    # O: e=2 place (1 rational point) + unramified slope-2 branch (1 point)
    one_third = 3 if p % 3 == 1 else 1
    ntO = cuberoot_count(-1 % p, p)
    sum_nt += ntO
    nCp += 2
    nC += 2 * one_third
    s1 = nCp - nC
    rt = math.isqrt(p) + 1
    checks = {
        "A": sum_nt == nE0,
        "B": abs(nCp - (p + 1)) <= 10 * rt,
        "C": abs(nC - (p + 1)) <= 26 * rt,
        "D": abs(s1) <= 16 * rt,
    }
    return nE0, nCp, nC, s1, checks


if __name__ == "__main__":
    print("eightfold (flex construction) k=1 battery")
    allok = True
    inert_zero = True
    for p in [7, 11, 13, 23, 29, 31, 37, 41, 43, 53, 61, 67, 73, 79]:
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
