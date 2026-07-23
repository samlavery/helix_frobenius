# Rail-native reading for the Prym specimens (weil_rails philosophy on OUR objects).
#
# sigma-twisted point counts: for C : t^3 = y over C', at split p (zeta_3 in F_p),
# a point of C over P in C'(F_q) with y != 0 satisfies t^{q-1} = chi(y) := y^{(q-1)/3},
# so all 3 t's over P lie in the single twisted class m with chi(y) = zeta^m.
#   #C_m(F_{q^k}) = sum over C'-points, binned by chi(y)   (T-points: t = 0 in every bin;
#   O-branches: y-leading = -(cube) => bin 0)
# DFT over m (exact, in Q(zeta_3)) splits H^1(C) = H^1(C') + V_omega + V_omegabar:
#   S_m(k) := q^k + 1 - #C_m(q^k) = sum_j zeta^{mj} T_j(k),  T_j(k) = Tr(Frob^k | V_{omega^j})
# Newton on T_1(1..2d) gives the RAIL CHAR POLY f_omega in Z[zeta_3][T] (integrality =
# convention check; f * fbar = P_B = cross-check against the stored tower L-polys).
# THE FREEZE SCALAR (full-support (1,..,1) lane): r = det(Frob | V_omega)/p^{d/1...}:
#   r = e_d / p^{d/2 * 1}  with |r| = 1;  r in mu_6  <=>  FREEZE (Z[zeta_3] units = mu_6:
#   exact integer test e_d in mu_6 * p^{d/2});  the unit = the ORDER LAW reading.
# Method law: report rail phases on the pi/3 (mu_6) harmonic scale, never unit-1.
#
# Specimen here: the SIXFOLD B_{a=1}: C' : u^3 + x*u + (y+1) = 0, rail dim d = 6,
# r = e_6 / p^3.  (Eightfold version follows once its tower lands.)

P_B_KNOWN = {
    7: [1, 2, 12, 32, 93, 184, 753, 1288, 4557, 10976, 28812, 33614, 117649],
    13: [1, 7, 58, 285, 1533, 6046, 25393, 78598, 259077, 626145, 1656538,
         2599051, 4826809],
}  # ascending coefficients, from the stored v2 tower logs

K = CyclotomicField(3, 'w')
w = K.gen()


def zeta_int(p):
    for z in range(2, p):
        if (z * z + z + 1) % p == 0:
            return z
    raise ValueError


def twisted_counts(p, k):
    q = p ^ k
    assert q % 3 == 1
    F = GF(q, 'g')
    R = PolynomialRing(F, 'U')
    U = R.gen()
    z = F(zeta_int(p))
    zpow = [F(1), z, z * z]
    e3 = (q - 1) // 3
    nCp = 0
    Cm = [0, 0, 0]
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
            f = U ^ 3 + x0 * U + (y0 + 1)
            nu = len(f.roots(multiplicities=False))
            nCp += nu
            if y0 == 0:
                Cm[0] += 3 * nu          # SMOOTH model: 3 points over T (tau in mu_3,
                                         # each Frob-fixed, sigma permutes) -> bin 0
            else:
                c = y0 ^ e3
                m = zpow.index(c)
                Cm[m] += 3 * nu
    # O-branches: residual cubic w^3 + w + 1; y-leading = -1, chi(-1) = 1 => bin 0
    nuO = len((U ^ 3 + U + 1).roots(multiplicities=False))
    nCp += nuO
    Cm[0] += 3 * nuO
    return nCp, Cm


def newton_charpoly(T1, d):
    # T1[k-1] = power sums over K; return monic f(T) = T^d - e1 T^{d-1} + ...
    e = [K(1)] + [K(0)] * d
    for k in range(1, d + 1):
        acc = K(0)
        for i in range(1, k + 1):
            acc += (-1) ^ (i - 1) * e[k - i] * T1[i - 1]
        e[k] = acc / k
    S = PolynomialRing(K, 'T')
    T = S.gen()
    return sum((-1) ^ j * e[j] * T ^ (d - j) for j in range(d + 1)), e


for p in [7, 13]:
    print("=" * 64)
    print(f"SIXFOLD RAILS  p = {p}")
    T1 = []
    T0chk = []
    for k in range(1, 7):
        nCp, Cm = twisted_counts(p, k)
        q = p ^ k
        S = [q + 1 - Cm[m] for m in range(3)]
        okSum = (sum(Cm) == 3 * nCp)
        t0 = (S[0] + S[1] + S[2]) / 3
        t1 = (S[0] + w ^ (-1) * S[1] + w ^ (-2) * S[2]) / 3
        T0chk.append((t0, q + 1 - nCp))
        T1.append(t1)
        print(f"k={k}: #C'={nCp} C_m={Cm} sumcheck={'OK' if okSum else 'FAIL'} "
              f"T0={t0} (C' gives {q + 1 - nCp})")
        sys.stdout.flush()
    conv_ok = all(a == b for (a, b) in T0chk)
    print("T0 == C'-trace at all k:", "PASS" if conv_ok else "FAIL (convention!)")
    f, e = newton_charpoly(T1, 6)
    integral = all(c.is_integral() for c in f.coefficients())
    print("rail char poly f_omega(T) =", f)
    print("coefficients integral in Z[zeta_3]:", "PASS" if integral else "FAIL")
    fbar = f.map_coefficients(lambda c: c.conjugate())
    prod = f * fbar
    SQ = PolynomialRing(QQ, 'T')
    prodQ = SQ([QQ(c) for c in prod.list()])
    known = SQ(P_B_KNOWN[p])
    # stored P_B(T) = prod(1 - a_i T) has ascending coeffs; f*fbar = prod(T - a_i):
    # compare with the reversed/monicized version
    knownrev = SQ(list(reversed(P_B_KNOWN[p])))
    match = (prodQ == knownrev)
    print("f * fbar == stored P_B (reciprocal form):", "PASS" if match else "FAIL")
    e6 = e[6]
    r = e6 / p ^ 3
    print("det(Frob | V_omega) = e_6 =", e6)
    units = {K(1): "+1", K(-1): "-1", w: "+w", -w: "-w", w ^ 2: "+w^2", -w ^ 2: "-w^2"}
    if r in units:
        print(f"*** FREEZE: r = e_6/p^3 = {units[K(r)]}  (mu_6 unit; ORDER LAW reading)")
    else:
        rn = CDF(K(r).complex_embedding())
        print(f"no mu_6 freeze at H^1-det level: r = {r}, |r| = {abs(rn):.6f}, "
              f"arg/(pi/3) = {rn.arg() / (pi / 3).n():.4f}")
    # rail phase spectrum on the mu_6 scale (method law: pi/3 cells, never unit-1)
    rts = [CDF(rr[0]) for rr in f.change_ring(CDF).roots()]
    phases = sorted(((r0.arg()) / (pi / 3).n()) for r0 in rts)
    print("rail phases in units of pi/3:", [f"{ph:.3f}" for ph in phases])
    purity = [abs(abs(r0) ^ 2 / p - 1) < 1e-6 for r0 in rts]
    print("rail purity:", "PASS" if all(purity) else "FAIL")
    sys.stdout.flush()
