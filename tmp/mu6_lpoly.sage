# mu_6 tower: full k<=6 tower at p=7 with SIX-BIN DFT -> three rail systems.
#   E = 20a1: y^2 = x^3 + x^2 + 4x + 4;  P6 = (4,10) order 6;  h = f3^2 (x - x(3P6))
#   C' : u^3 + x*u + (y + 1) = 0   (v2 design: fiber LINEAR in (x,y) => u-map degree 3
#        PRIME => no intermediate covers, the v1/flex disease excluded BY DESIGN)
#   C  : t^6 = h∘pi  (etale, connected).  g' = 4, g_C = 19.
# Pieces: B6 = (V_chi + V_chi^5)/  [dim 6, K = Q(sqrt-3) Weil, glue | 6: NON-SPLIT
# candidate], B3 = (V_chi^2 + V_chi^4) [dim 6, mu_3 control], B2 = V_chi^3 [dim 3].
# kappa(P) = h(P)^((q-1)/6) is the descent homomorphism; special points by
# kappa(R+S) = kappa(R)kappa(S).  zeta_6 = 3 mod 7 (3^2 - 3 + 1 = 7): consistent
# across k since 3 in F_7 c F_{7^k}.
# DFT: S_m(k) = q^k + 1 - #C_m -> T_j = (1/6) sum_m zeta6^{-mj} S_m in Q(zeta_3)
# (zeta6 = -w^2).  Newton -> rail polys f_1, f_2, f_3 (deg 6 each).
# Pieces: P_B6 = f_1 * conj(f_1), P_B3 = f_2 * conj(f_2), P_B2 = f_3 (self-conj).
# Verdicts: purity each rail; freezes e_6/p^3 per rail; simplicity of each piece.

E = EllipticCurve('20a1')
P6 = E(4, 10)
assert P6.order() == 6
a1, a2, a3, a4, a6 = E.a_invariants()
xP, yP = P6.xy()
P2, P3 = 2 * P6, 3 * P6
x2, y2 = P2.xy()
x3, y3 = P3.xy()
lam1 = (3 * xP ^ 2 + 2 * a2 * xP + a4 - a1 * yP) / (2 * yP + a1 * xP + a3)
lam2 = (y2 - yP) / (x2 - xP)

K = CyclotomicField(3, 'w')
w = K.gen()
z6 = -w ^ 2                      # primitive 6th root in K
A_PARAM = 1
p = 7
Z6INT = 3                        # 3 is a primitive 6th root of unity mod 7


def h_eval(F, X, Y):
    l1 = Y - F(yP) - F(lam1) * (X - F(xP))
    v2 = X - F(x2)
    l2 = Y - F(y2) - F(lam2) * (X - F(x2))
    v3 = X - F(x3)
    num = l1 * l2
    den = v2 * v3
    if den == 0 or num == 0:
        return None
    return (num / den) ^ 2 * (X - F(x3))


def twisted_counts(k):
    q = p ^ k
    F = GF(q, 'g')
    Ep = E.change_ring(F)
    R = PolynomialRing(F, 'U')
    U = R.gen()
    z = F(Z6INT)
    zpow = [z ^ i for i in range(6)]
    e6 = (q - 1) // 6

    def kap(pt):
        if pt.is_zero():
            return 0
        v = h_eval(F, pt[0], pt[1])
        if v is None:
            return None
        return zpow.index(v ^ e6)

    # kappa at the divisor support: leading-coefficient regularization at P6
    # (well-defined mod 6th powers).  Hand derivation: tangent second-order coeff
    # y''/2 = 1/5, chord leading 1, v2(P6) = 4, v3(P6) = 5 => c3 = 1/100,
    # c6 = (x(P6) - x3) * c3^2 = 5/10000 = 1/2000.  Extend by the homomorphism.
    C6_LEAD = QQ(1) / 2000
    c6 = F(C6_LEAD.numerator()) / F(C6_LEAD.denominator())
    mP6 = zpow.index(c6 ^ e6)
    P6b = Ep(P6)
    special = {}
    for j in range(1, 6):
        S = j * P6b
        if S.is_zero():
            continue
        special[(S[0], S[1])] = (j * mP6) % 6
        # cross-validate the homomorphism extension against generic pairs when
        # the field has non-torsion points (k >= 2)
        m2 = None
        for _ in range(200):
            Rp = Ep.random_point()
            mR, mRS = kap(Rp), kap(Rp + S)
            if mR is not None and mRS is not None:
                m2 = (mRS - mR) % 6
                break
        if m2 is not None and m2 != (j * mP6) % 6:
            print(f"  WARNING k={k}: hom-extension bin {(j * mP6) % 6} != "
                  f"pair-calibrated {m2} at {j}*P6 -- convention broken")

    nCp = 0
    Cm = [0] * 6
    for pt in Ep:
        if pt.is_zero():
            continue
        X, Y = pt[0], pt[1]
        f = U ^ 3 + X * U + (Y + A_PARAM)
        nu = len(f.roots(multiplicities=False))
        m = kap(pt)
        if m is None:
            m = special.get((X, Y))
        nCp += nu
        Cm[m] += 6 * nu
    nuO = len((U ^ 3 + U + 1).roots(multiplicities=False))
    nCp += nuO
    Cm[0] += 6 * nuO             # kappa(O) = 1: all six t-branches in bin 0
    return nCp, Cm


def newton_charpoly(T1, d):
    e = [K(1)] + [K(0)] * d
    for kk in range(1, d + 1):
        acc = K(0)
        for i in range(1, kk + 1):
            acc += (-1) ^ (i - 1) * e[kk - i] * T1[i - 1]
        e[kk] = acc / kk
    S = PolynomialRing(K, 'T')
    T = S.gen()
    return sum((-1) ^ j * e[j] * T ^ (d - j) for j in range(d + 1)), e


print("MU6 TOWER  p = 7, k = 1..6  (three rails)")
T = {1: [], 2: [], 3: []}
convOK = True
for k in range(1, 7):
    nCp, Cm = twisted_counts(k)
    q = p ^ k
    S = [q + 1 - Cm[m] for m in range(6)]
    okSum = (sum(Cm) == 6 * nCp)
    t0 = sum(S) / 6
    convOK = convOK and okSum and (t0 == q + 1 - nCp)
    for j in (1, 2, 3):
        tj = sum(z6 ^ (-m * j) * S[m] for m in range(6)) / 6
        T[j].append(tj)
    print(f"k={k}: #C'={nCp} C_m={Cm} sum={'OK' if okSum else 'FAIL'} "
          f"T0={t0} (C': {q + 1 - nCp})")
    sys.stdout.flush()
print("conventions:", "PASS" if convOK else "FAIL")

SQ = PolynomialRing(QQ, 'T')
units = {K(1): "+1", K(-1): "-1", w: "+w", -w: "-w", w ^ 2: "+w^2", -w ^ 2: "-w^2"}
pieces = {}
for j, name, dim in [(1, "B6 (chi-primitive, NON-SPLIT candidate)", 6),
                     (2, "B3 (mu_3 control)", 6),
                     (3, "B2 (Z/2-Prym)", 6)]:
    f, e = newton_charpoly(T[j], 6)
    integral = all(c.is_integral() for c in f.coefficients())
    fbar = f.map_coefficients(lambda c: c.conjugate())
    rts = [CDF(rr[0]) for rr in f.change_ring(CDF).roots()]
    pure = all(abs(abs(r0) ^ 2 / p - 1) < 1e-6 for r0 in rts)
    print("=" * 64)
    print(f"rail j={j}: {name}")
    print("f =", f)
    print("integral:", "PASS" if integral else "FAIL", "| purity:",
          "PASS" if pure else "FAIL")
    e6c = e[6]
    r = e6c / p ^ 3
    if r in units:
        print(f"*** FREEZE: r = e_6/p^3 = {units[K(r)]}")
    else:
        rn = CDF(K(r).complex_embedding())
        print(f"no mu_6 freeze: |r| = {abs(rn):.6f}, arg/(pi/3) = "
              f"{rn.arg() / (pi / 3).n():.4f}")
    if j == 3:
        selfc = (f == fbar)
        print("self-conjugate (rational):", "PASS" if selfc else "FAIL")
        PB = SQ([QQ(c) for c in f.list()]) if selfc else None
    else:
        PB = SQ([QQ(c) for c in (f * fbar).list()])
    if PB is not None:
        fac = PB.factor()
        irr = len(list(fac)) == 1 and fac[0][1] == 1
        print(f"P_piece deg {PB.degree()}: factor = {fac}")
        print("SIMPLE:", "YES (irreducible at split p=7)" if irr else "no/inspect")
    pieces[j] = PB
    sys.stdout.flush()
