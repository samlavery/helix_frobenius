from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
R.<x,y> = QQ[]
S = RiemannSurface(y^3 - (x^4 - 1), prec=80)
meths = [m for m in dir(S) if not m.startswith('__')]
want = ['homology','period','riemann','abel','jacobi','endo','cohom','differ','monodromy','tangent','cycle','intersection','paths']
print("relevant RiemannSurface methods:")
for m in meths:
    if any(w in m.lower() for w in want):
        print("   ", m)
print()
# what does homology basis look like?
try:
    print("homology_basis type:", type(S.homology_basis()))
    hb = S.homology_basis()
    print("num cycles:", len(hb), " first cycle (paths) length:", len(hb[0]) if hb else 0)
except Exception as ex:
    print("homology_basis:", ex)
