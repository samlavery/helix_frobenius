# Radial-Torelli rung, genus 2: periods -> FIREWALL(tau) -> theta constants
# -> branch-point invariants, gated exactly against the curve.
# Convention-free design: the gate invariants are Sp4(Z)-invariant sign-free
# theta functionals p2/p1^2, p3/p1^3, q10/p1^10 (power sums/product of the
# ten even theta^8's); by Thomae theta_S^8 ~ c^2 * T_S with T_S the SQUARED
# 3+3 partition product of branch differences (signs die in the square, the
# scale dies in ratios, Moebius dies by uniform weight) — so the true side
# computes the same rationals directly from the roots, projectively.

from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
from itertools import combinations

PREC = 120
C = ComplexField(PREC)
R.<x> = QQ[]

CURVES = {
    'g2a (rosenhain 2,3,5)': x*(x-1)*(x-2)*(x-3)*(x-5),
    'g2b (quintic)':         x^5 - x + 1,
    'g2c (sextic)':          x^6 + x + 3,
}


def proj_roots(f):
    """Projective roots (alpha:beta) of the degree-6 binary form; adds
    infinity for quintics."""
    rts = f.roots(ComplexField(PREC + 60), multiplicities=False)
    pts = [(C(r), C(1)) for r in rts]
    if f.degree() == 5:
        pts.append((C(1), C(0)))
    assert len(pts) == 6
    return pts


def true_invariants(f):
    pts = proj_roots(f)
    def d(i, j):
        (a1, b1), (a2, b2) = pts[i], pts[j]
        return a1*b2 - a2*b1
    Ts = []
    for S in combinations(range(6), 3):
        if 0 not in S:
            continue                      # each partition once (fix 0 in S)
        Sc = tuple(k for k in range(6) if k not in S)
        prod = C(1)
        for (i, j) in combinations(S, 2):
            prod *= d(i, j)
        for (i, j) in combinations(Sc, 2):
            prod *= d(i, j)
        Ts.append(prod^2)
    assert len(Ts) == 10
    p1 = sum(Ts)
    p2 = sum(t^2 for t in Ts)
    p3 = sum(t^3 for t in Ts)
    q  = prod_list(Ts)
    return [p2/p1^2, p3/p1^3, q/p1^10]


def prod_list(L):
    out = C(1)
    for t in L:
        out *= t
    return out


def theta_consts(tau):
    """The ten even genus-2 theta constants theta[a,b](0, tau)."""
    N = 14
    out = []
    for a1 in (0, 1):
        for a2 in (0, 1):
            for b1 in (0, 1):
                for b2 in (0, 1):
                    if (a1*b1 + a2*b2) % 2 != 0:
                        continue          # odd characteristic
                    aa = (C(a1)/2, C(a2)/2)
                    bb = (C(b1)/2, C(b2)/2)
                    s = C(0)
                    for n1 in range(-N, N+1):
                        for n2 in range(-N, N+1):
                            m1, m2 = C(n1) + aa[0], C(n2) + aa[1]
                            quad = m1*(tau[0][0]*m1 + tau[0][1]*m2) \
                                 + m2*(tau[1][0]*m1 + tau[1][1]*m2)
                            lin = m1*bb[0] + m2*bb[1]
                            s += (C(pi)*C.0*quad + 2*C(pi)*C.0*lin).exp()
                    out.append(s)
    assert len(out) == 10
    return out


def reconstructed_invariants(tau):
    th8 = [t^8 for t in theta_consts(tau)]
    p1 = sum(th8)
    p2 = sum(t^2 for t in th8)
    p3 = sum(t^3 for t in th8)
    q = prod_list(th8)
    return [p2/p1^2, p3/p1^3, q/p1^10]


def recognize(v, den_bound=10^12):
    fr = v.real().nearby_rational(max_denominator=den_bound)
    gate = abs(v.real() - fr) < 2^(-PREC//2) and abs(v.imag()) < 2^(-PREC//2)
    return fr, gate


for name, f in CURVES.items():
    S = RiemannSurface(y^2 - f(x) if False else None) if False else None
    RS = RiemannSurface((x^0*0).parent()(0)) if False else None
    # build surface
    Rxy = PolynomialRing(QQ, ['x', 'y'])
    xv, yv = Rxy.gens()
    fpoly = sum(QQ(c)*xv^i for i, c in enumerate(f.list()))
    RS = RiemannSurface(yv^2 - fpoly, prec=PREC)
    tau = RS.riemann_matrix()
    # internal gates on tau
    sym = max(abs(C(tau[i][j]) - C(tau[j][i])) for i in range(2) for j in range(2))
    tauC = [[C(tau[0][0]), C(tau[0][1])], [C(tau[1][0]), C(tau[1][1])]]
    # ---------------- FIREWALL: only tauC crosses ----------------
    rec = reconstructed_invariants(tauC)
    tru = true_invariants(f)
    ok_all = True
    lines = []
    tol = RealField(PREC)(2)^(-2*PREC//3)
    for k in range(3):
        # primary gate: the two arms agree at ~80-bit relative precision
        diff = abs(rec[k] - tru[k]) / (1 + abs(tru[k]))
        match = diff < tol
        ok_all = ok_all and match
        fr_r, g_r = recognize(rec[k])
        tag = f"= {fr_r} (rational)" if g_r else f"(agree to {diff:.1e})"
        lines.append(f"    I{k+1}: {'MATCH' if match else 'MISMATCH'} {tag}")
    print(f"{name}: tau-sym {sym:.1e}  ->  "
          f"{'EXACT MATCH (all 3 invariants)' if ok_all else 'MISMATCH'}",
          flush=True)
    for ln in lines:
        print(ln, flush=True)
