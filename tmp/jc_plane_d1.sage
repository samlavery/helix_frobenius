# hunt-spec 2026-07-26 — plane-JC side quest, round 1 (degree-1 slices).
# Normal form (gauge-fixed): l1 = u*x + v*y;  l2 = A(u,v)x + B(u,v)y with
# A,B affine-linear; target F = (linear combo of c0,c1,c2), where
# c0=u*A, c1=u*B+v*A, c2=v*B are the coeffs of l1*l2.
# Question: which parameter choices make det J_F constant, and are any
# non-injective?  ORACLE: Wang's theorem (deg<=2 JC true, all n) predicts
# every solution injective.  Purpose here = mechanism mapping (Moh: plane
# JC true to deg 100, so low degree cannot hold a counterexample).
P = PolynomialRing(QQ, ['a0','a1','a2','b0','b1','b2','m1','m2','m3','n1','n2','n3'])
a0,a1,a2,b0,b1,b2,m1,m2,m3,n1,n2,n3 = P.gens()
R = PolynomialRing(P, ['u','v'])
u, v = R.gens()
A = a0 + a1*u + a2*v
B = b0 + b1*u + b2*v
c0, c1, c2 = u*A, u*B + v*A, v*B
F1 = m1*c0 + m2*c1 + m3*c2
F2 = n1*c0 + n2*c1 + n3*c2
J = F1.derivative(u)*F2.derivative(v) - F1.derivative(v)*F2.derivative(u)
mono = J.monomials()
const = J.constant_coefficient()
noncst = [J.monomial_coefficient(m) for m in mono if m != R(1)]
print(f"det J: {len(mono)} monomials, {len(noncst)} nonconstant coeff equations")
Q = PolynomialRing(QQ, P.variable_names() + ('z',))
inj = {str(g): Q(str(g)) for g in P.gens()}
eqs = [Q(str(e)) for e in noncst] + [Q(str(const)) * Q('z') - 1]
I = Q.ideal(eqs)
dim = I.dimension()
print(f"det-const variety (const!=0): dimension = {dim} (in 13 vars incl Rabinowitsch)")
# sample a solution: slice with generic hyperplanes until 0-dim, take a point
import itertools
Jsat = I
slice_vars = ['a0','a1','a2','b0','b1','b2','m1','m2','m3','n1','n2','n3']
vals = {'a0': 1, 'a1': 0, 'a2': 3, 'b0': 0, 'b1': 2, 'b2': 0}
I2 = I + Q.ideal([inj[k] - QQ(vv) for k, vv in vals.items()])
print(f"after pinning l2 = (1+3v)x + 2u y: dim = {I2.dimension()}")
if I2.dimension() >= 0:
    # find rational point in remaining m,n vars
    G = I2.groebner_basis()
    print("sample groebner (first 4):")
    for g in list(G)[:4]: print("  ", g)
