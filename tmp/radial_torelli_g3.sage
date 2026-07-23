# Radial-Torelli rung, genus 3 — both faces.
# HYPERELLIPTIC: tau -> 36 even thetas -> detect the hyperelliptic
#   vanishing (exactly one theta ~ 0) + Thomae gate: power-sum/product
#   ratios of the 35 nonzero theta^8's == same ratios of squared 4+4
#   partition-products of the 8 branch points (convention-free, as g2).
# QUARTIC (non-hyperelliptic, the Schoen-gate target): all-36-nonzero
#   certificate + the fingerprint is an ISOMORPHISM INVARIANT: two models
#   of the same quartic agree; a different quartic separates.
from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
from itertools import combinations

PREC = 100
C = ComplexField(PREC)
Rx.<x> = QQ[]
Rxy = PolynomialRing(QQ, ['x', 'y'])
xv, yv = Rxy.gens()


def riemann_tau(fxy):
    RS = RiemannSurface(fxy, prec=PREC)
    tau = RS.riemann_matrix()
    tc = [[C(tau[i][j]) for j in range(3)] for i in range(3)]
    sym = max(abs(tc[i][j] - tc[j][i]) for i in range(3) for j in range(3))
    assert sym < C(2)^(-PREC//2), f"tau not symmetric: {sym}"
    return tc


def theta_consts_g3(tau, N=7):
    """The 36 even genus-3 theta constants."""
    out = []
    I = C.0
    PI = C(pi)
    for a in cartesian_product([(0,1)]*3):
        for b in cartesian_product([(0,1)]*3):
            if (a[0]*b[0] + a[1]*b[1] + a[2]*b[2]) % 2 != 0:
                continue
            s = C(0)
            for n1 in range(-N, N+1):
                for n2 in range(-N, N+1):
                    for n3 in range(-N, N+1):
                        m = [C(n1)+C(a[0])/2, C(n2)+C(a[1])/2, C(n3)+C(a[2])/2]
                        quad = sum(m[i]*tau[i][j]*m[j] for i in range(3)
                                   for j in range(3))
                        lin = sum(m[i]*C(b[i])/2 for i in range(3))
                        s += (PI*I*quad + 2*PI*I*lin).exp()
            out.append(s)
    assert len(out) == 36
    return out


def fingerprint(th8):
    p1 = sum(th8)
    p2 = sum(t^2 for t in th8)
    p3 = sum(t^3 for t in th8)
    return [p2/p1^2, p3/p1^3]


def prodl(L):
    out = C(1)
    for t in L:
        out *= t
    return out


def thomae_true_g3(f):
    """True-side ratios from squared 4+4 partition products of the 8
    projective branch points of y^2 = f(x)."""
    rts = f.roots(ComplexField(PREC+60), multiplicities=False)
    pts = [(C(r), C(1)) for r in rts]
    if f.degree() == 7:
        pts.append((C(1), C(0)))
    assert len(pts) == 8
    def d(i, j):
        (a1, b1), (a2, b2) = pts[i], pts[j]
        return a1*b2 - a2*b1
    Ts = []
    for S in combinations(range(8), 4):
        if 0 not in S:
            continue
        Sc = tuple(k for k in range(8) if k not in S)
        pr = C(1)
        for (i, j) in combinations(S, 2):
            pr *= d(i, j)
        for (i, j) in combinations(Sc, 2):
            pr *= d(i, j)
        Ts.append(pr^2)
    assert len(Ts) == 35
    p1 = sum(Ts)
    p2 = sum(t^2 for t in Ts)
    p3 = sum(t^3 for t in Ts)
    return [p2/p1^2, p3/p1^3, prodl(Ts)/p1^35]


tol = C(2).real()^(-PREC//3)

print("== HYPERELLIPTIC FACE ==", flush=True)
for name, f in [('h3a: y2 = x^7 - x + 1', x^7 - x + 1),
                ('h3b: y2 = x^8 + 3x + 3', x^8 + 3*x + 3)]:
    fxy = yv^2 - sum(QQ(c)*xv^i for i, c in enumerate(f.list()))
    tau = riemann_tau(fxy)
    th = theta_consts_g3(tau)
    mags = sorted(abs(t) for t in th)
    vanish_ratio = mags[0]/mags[1]
    hyper_detected = vanish_ratio < C(10).real()^(-15)
    th_sorted = sorted(th, key=lambda t: abs(t))
    th8nz = [t^8 for t in th_sorted[1:]]          # drop the vanishing one
    p1 = sum(th8nz)
    rec = [sum(t^2 for t in th8nz)/p1^2, sum(t^3 for t in th8nz)/p1^3,
           prodl(th8nz)/p1^35]
    tru = thomae_true_g3(f)
    diffs = [abs(rec[k]-tru[k])/(1+abs(tru[k])) for k in range(3)]
    ok = all(dd < tol for dd in diffs)
    print(f"{name}: hyperelliptic-vanishing detected: {hyper_detected} "
          f"(ratio {vanish_ratio:.1e});  Thomae gate: "
          f"{'EXACT MATCH' if ok else 'MISMATCH'} "
          f"(agreements {[f'{float(dd):.0e}' for dd in diffs]})", flush=True)

print("== QUARTIC FACE (Schoen-gate target) ==", flush=True)
# q3a: x^4 + y^4 + 1 + x (smooth), model B = same curve, x -> x+y, y -> x-y
q3aA = xv^4 + yv^4 + 1 + xv
q3aB = (xv+yv)^4 + (xv-yv)^4 + 1 + (xv+yv)
q3b = xv^4 + yv^4 + 1                              # Fermat quartic
FPS = {}
for name, f in [('q3a modelA', q3aA), ('q3a modelB', q3aB),
                ('q3b Fermat', q3b)]:
    tau = riemann_tau(f)
    th = theta_consts_g3(tau)
    mags = sorted(abs(t) for t in th)
    nonhyper = mags[0]/mags[-1] > C(10).real()^(-10)
    fp = fingerprint([t^8 for t in th])
    FPS[name] = fp
    print(f"{name}: all-36-nonzero (non-hyperelliptic certificate): "
          f"{nonhyper} (min/max {mags[0]/mags[-1]:.1e})", flush=True)

same = max(abs(FPS['q3a modelA'][k] - FPS['q3a modelB'][k]) for k in range(2))
diff = max(abs(FPS['q3a modelA'][k] - FPS['q3b Fermat'][k]) for k in range(2))
print(f"ISOMORPHISM INVARIANCE: modelA vs modelB agree to {same:.1e} "
      f"({'PASS' if same < tol else 'FAIL'})", flush=True)
print(f"SEPARATION: q3a vs Fermat differ by {diff:.1e} "
      f"({'PASS' if diff > C(10).real()^(-5) else 'FAIL'})", flush=True)
