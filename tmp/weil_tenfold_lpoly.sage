# Tenfold base C' : u^3 + x*u + (y + x^2 + a) = 0 over E0 : y^2 + 2xy + y = x^3.
# Genus-6 CERTIFICATE: count #C'(F_{p^k}) for k = 1..6, Newton -> elementary symmetric
# -> FE-complete to an assumed-degree-12 numerator -> purity |root|^2 * p = 1 for all
# 12 roots.  Purity pass <=> the numerator really has degree 12 <=> g(C') = 6 EXACTLY
# (a wrong genus assumption breaks the functional-equation completion and purity).
# Also records #C(F_{p^k}) and Prym s_k = #C' - #C for the eventual deg-20 analysis.

A_PARAM = 1


def counts(p, k, a=A_PARAM):
    q = p ^ k
    F = GF(q, 'g')
    R = PolynomialRing(F, 'U')
    U = R.gen()
    one_third = 3 if q % 3 == 1 else 1
    third = (q - 1) // 3 if q % 3 == 1 else 0
    nE0 = 1          # O
    nCp = 0
    nC = 0
    aF = F(a)
    for x0 in F:
        b = 2 * x0 + 1
        D = b * b + 4 * x0 ^ 3
        if D == 0:
            ys = [-b / 2]
        elif D.is_square():
            s = D.sqrt()
            ys = [(-b + s) / 2, (-b - s) / 2]
        else:
            ys = []
        for y0 in ys:
            nE0 += 1
            f = U ^ 3 + x0 * U + (y0 + x0 ^ 2 + aF)
            nu = len(f.roots(multiplicities=False))
            if y0 == 0:
                nt = one_third                    # T: leading coeff of y is a cube
            elif q % 3 == 1:
                nt = 3 if y0 ^ third == 1 else 0
            else:
                nt = 1
            nCp += nu
            nC += nu * nt
    nCp += 1                                      # O: totally ramified, one point
    nC += one_third                               # tau^3 = (unit)^3
    return nE0, nCp, nC


def fe_lpoly(p, Ns, g):
    # Ns[k-1] = #C'(F_{p^k}), k = 1..g; numerator P(T) = prod (1 - a_i T), deg 2g.
    t = [p ^ (k) + 1 - Ns[k - 1] for k in range(1, g + 1)]   # power sums s_k
    e = [1] + [0] * g
    for k in range(1, g + 1):
        acc = 0
        for i in range(1, k + 1):
            acc += (-1) ^ (i - 1) * e[k - i] * t[i - 1]
        e[k] = acc / k
    # coefficients of P: c_j = (-1)^j e_j for j <= g; FE: c_{2g-j} = p^{g-j} c_j
    c = [0] * (2 * g + 1)
    for j in range(g + 1):
        c[j] = (-1) ^ j * e[j]
    for j in range(g):
        c[2 * g - j] = p ^ (g - j) * c[j]
    S = PolynomialRing(QQ, 'T')
    T = S.gen()
    P = sum(QQ(c[j]) * T ^ j for j in range(2 * g + 1))
    return P


for p in [7, 13]:
    print("=" * 60)
    print(f"p = {p}")
    Ns, Ms = [], []
    for k in range(1, 7):
        nE0, nCp, nC = counts(p, k)
        Ns.append(nCp)
        Ms.append(nC)
        print(f"k={k} q={p^k}: #E0={nE0} #C'={nCp} #C={nC}  s_{k}={nCp - nC}")
        sys.stdout.flush()
    P = fe_lpoly(p, Ns, 6)
    print("P_C'(T) deg", P.degree(), ":", P)
    rts = P.change_ring(CDF).roots(multiplicities=False)
    purity = sorted(set(round(abs(r) ^ 2 * p, 3) for r in rts))
    print("|root|^2 * p (all must be 1.000):", purity)
    ok = all(abs(abs(r) ^ 2 * p - 1) < 1e-6 for r in rts)
    print("GENUS 6 CERTIFICATE:", "PASS" if ok else "FAIL")
    print("factor over ZZ:", factor(P))
