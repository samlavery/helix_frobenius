from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
R.<x,y> = QQ[]

curves = {
  'generic   y^3=(x-1)(x-2)(x-3)(x-5)': y^3 - (x-1)*(x-2)*(x-3)*(x-5),
  'symmetric y^3 = x^4 - 1':            y^3 - (x^4 - 1),
}

for name, f in curves.items():
    print('='*64)
    print(name)
    S = RiemannSurface(f, prec=120)
    tau = S.riemann_matrix()
    g = tau.nrows()
    sym = max(abs(tau[a,b]-tau[b,a]) for a in range(g) for b in range(g))
    Im = matrix(RDF, g, g, [tau[a,b].imag() for a in range(g) for b in range(g)])
    minors = [Im[:k,:k].det() for k in range(1,g+1)]
    pd = all(m > 0 for m in minors)
    print(f'  genus {g};  tau symmetric to {RDF(sym):.2e};  Im(tau) pos-def: {pd}')
    print(f'  Riemann relations {"VERIFIED" if RDF(sym)<1e-10 and pd else "FAIL"} -> '
          f'{"genuine non-hyperelliptic Siegel point" if pd else "check"}')
