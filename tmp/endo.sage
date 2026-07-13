from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
R.<x,y> = QQ[]

cases = {
 'generic   y^3=(x-1)(x-2)(x-3)(x-5)': y^3 - (x-1)*(x-2)*(x-3)*(x-5),
 'symmetric y^3 = x^4 - 1  (CM)':      y^3 - (x^4 - 1),
 'Klein-ish y^3 = x^4 - x  ':          y^3 - (x^4 - x),
}
print("Endomorphism algebra of the Jacobian (dim over Q = # independent Hodge classes")
print("on Jac x Jac beyond the trivial ones).  Picard curves all carry Z[zeta_3], so")
print("dim >= 2; genuine EXTRA structure (CM) shows a strictly larger algebra.\n")
for name, f in cases.items():
    S = RiemannSurface(f, prec=100)
    E = S.endomorphism_basis()
    print(f"  {name:38}  End(Jac)⊗Q dim = {len(E)}")
