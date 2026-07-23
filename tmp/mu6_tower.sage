# THE HARMONIC TURN: the mu_6 tower -- three rails in one object, 2-AND-3 glue.
#
#   E   : elliptic curve with rational Z/6 torsion (P6 of exact order 6)
#   h   : div(h) = 6[P6] - 6[O];  h = f3^2 * (x - x(3P6)),  f3 = Miller chain
#         (l_{P,P}/v_{2P}) * (l_{2P,P}/v_{3P});  the finite DOUBLE-ENDED 6-helix.
#   C'  : u^3 + x*u + (y + a) = 0 over E   (v2 design; genus-4 Newton analysis is
#         E-independent: only the Weierstrass pole semigroup enters; O-residual
#         cubic w^3 + w + 1 also E-independent -- exclude p = 31)
#   C   : t^6 = h∘pi  -- etale ALWAYS (divisor 6-divisible), connected (h is neither
#         a square nor a cube: 3P6 != O != 2P6)
#   g_C = 6(g'-1) + g' = 19.  H^1(C) = H^1(C') + V_chi + V_chi^5 + V_chi^2 + V_chi^4
#         + V_chi^3:  pieces B6 (dim 6, K = Q(sqrt-3) Weil, glue | 6 => NON-SPLIT
#         CANDIDATE: 2-adic glue parity is the verdict), B3 (dim 6, mu_3 control),
#         B2 (dim 3, Z/2-Prym).
#   Binning: the sextic character kappa(P) = h(P)^((q-1)/6) IS the phi-hat descent
#   homomorphism E(F_q) -> mu_6; special fibers (h = 0/0 numerically at kP6) resolve
#   by kappa(P + Q) = kappa(P)kappa(Q) -- no leading-coefficient surgery.
#   Check A: sum_P n_t = #E''(F_q) = #E(F_q)  (E'' = E/<P6> is 6-isogenous).
#
# Stage A: pick the base curve, build h, calibrate kappa.  Stage B: k=1 battery.

A_PARAM = 1


def pick_curve():
    for label in ['20a1', '20a2', '20a3', '14a1', '14a2', '36a1']:
        E = EllipticCurve(label)
        T = E.torsion_subgroup()
        if T.order() % 6 == 0:
            for t in T:
                if t.order() == 6:
                    return label, E, E(t)
    raise RuntimeError("no Z/6 curve found")


label, E, P6 = pick_curve()
a1, a2, a3, a4, a6 = E.a_invariants()
P2, P3 = 2 * P6, 3 * P6
print(f"base curve {label}: {E.ainvs()}  bad primes {E.conductor().factor()}")
print(f"P6 = {P6.xy()}  order {P6.order()};  2P6 = {P2.xy()};  3P6 = {P3.xy()}")

# Miller lines over Q (rational coefficients; reduce mod p at use time)
xP, yP = P6.xy()
lam1 = (3 * xP ^ 2 + 2 * a2 * xP + a4 - a1 * yP) / (2 * yP + a1 * xP + a3)
x2, y2 = P2.xy()
lam2 = (y2 - yP) / (x2 - xP)
x3, y3 = P3.xy()
print(f"tangent slope at P6: {lam1};  chord(2P6,P6) slope: {lam2}")


def h_eval(F, X, Y):
    """h = [l_PP/v_2P * l_2PP/v_3P]^2 * (x - x3) over field F; None if 0/0."""
    l1 = Y - F(yP) - F(lam1) * (X - F(xP))
    v2 = X - F(x2)
    l2 = Y - F(y2) - F(lam2) * (X - F(x2))
    v3 = X - F(x3)
    num = l1 * l2
    den = v2 * v3
    if den == 0 or num == 0:
        return None                      # special point: resolve via kappa-homomorphism
    return (num / den) ^ 2 * (X - F(x3))


def kappa_table(p):
    """kappa on E(F_p) -> index in mu_6 (split p) or mu_2 (inert p); returns dict
    point -> m plus the calibrated kappa(P6bar) via the homomorphism trick."""
    F = GF(p)
    Ep = E.change_ring(F)
    d = 6 if p % 6 == 1 else 2
    e6 = (p - 1) // d
    # multiplicative generator for discrete-log binning
    g = F.multiplicative_generator()
    zeta = g ^ ((p - 1) // d)
    zpow = [zeta ^ i for i in range(d)]

    def kap(pt):
        if pt.is_zero():
            return 0
        v = h_eval(F, pt[0], pt[1])
        if v is None:
            return None
        return zpow.index(v ^ e6)

    # calibrate kappa at the <=5 special points kP6bar via kappa(R + S) = k(R)k(S)
    P6b = Ep(P6)
    special = {}
    for k in range(1, 6):
        S = k * P6b
        if S.is_zero():
            continue
        m = kap(S)
        if m is None:
            for _ in range(200):
                R = Ep.random_point()
                mR, mRS = kap(R), kap(R + S)
                if mR is not None and mRS is not None:
                    m = (mRS - mR) % d
                    break
        special[(S[0], S[1])] = m
    return Ep, d, kap, special


def battery(p):
    assert p not in (2, 3, 31) and E.conductor() % p != 0
    Ep, d, kap, special = kappa_table(p)
    nE = Ep.count_points()
    F = GF(p)
    pts = [pt for pt in Ep if not pt.is_zero()]
    R = PolynomialRing(F, 'U')
    U = R.gen()
    sum_nt = 0
    nCp = nC = 0
    bins = [0] * d
    for pt in pts:
        X, Y = pt[0], pt[1]
        f = U ^ 3 + X * U + (Y + A_PARAM)
        nu = len(f.roots(multiplicities=False))
        m = kap(pt)
        if m is None:
            m = special.get((X, Y))
        nt = d * (1 if m == 0 else 0) * (6 // d) if False else (6 if (d == 6 and m == 0)
             else (2 if (d == 2 and m == 0) else 0))
        sum_nt += nt
        nCp += nu
        nC += nu * nt
        if m is not None:
            bins[m] += nu
    # O: n_u = roots of w^3 + w + 1 (E-independent residual); kappa(O) = 1
    nuO = len((U ^ 3 + U + 1).roots(multiplicities=False))
    ntO = 6 if d == 6 else 2
    sum_nt += ntO
    nCp += nuO
    nC += nuO * ntO
    bins[0] += nuO
    s1 = nCp - nC
    rt = isqrt(p) + 1
    ch = {"A": sum_nt == nE,
          "B": abs(nCp - (p + 1)) <= 8 * rt,       # g' = 4
          "C": abs(nC - (p + 1)) <= 38 * rt,       # g_C = 19
          "D": abs(s1) <= 30 * rt}                 # total Prym dim 15
    return nE, nCp, nC, s1, bins, ch, d


print("\nStage B: k=1 battery (mu_6 tower, three rails)")
allok = True
for p in [7, 11, 13, 17, 19, 23, 29, 37, 41, 43, 47, 53, 61, 67, 73, 79]:
    if E.conductor() % p == 0 or p == 31:
        continue
    nE, nCp, nC, s1, bins, ch, d = battery(p)
    ok = all(ch.values())
    allok = allok and ok
    kind = "split" if p % 6 == 1 else "inert"
    flag = "PASS" if ok else "FAIL " + str([k for k, v in ch.items() if not v])
    print(f"p={p:>3} ({kind}): #E={nE:>4} #C'={nCp:>4} #C={nC:>5} s1={s1:>5} "
          f"bins={bins}  {flag}")
    sys.stdout.flush()
print("ALL PASS" if allok else "FAILURES")
