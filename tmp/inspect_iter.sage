from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
import inspect
S = RiemannSurface(QQ['x,y'].0^0*0 + 0, prec=30) if False else None
from sage.schemes.riemann_surfaces import riemann_surface as rs
m = rs.RiemannSurface._integrate_differentials_iteratively
print("SIGNATURE:", inspect.signature(m))
doc = (m.__doc__ or "")
print("DOC (first 1600 chars):")
print(doc[:1600])
