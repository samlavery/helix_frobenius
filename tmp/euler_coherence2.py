"""Corrected Davenport-Heilbronn control.
Odd sequences mod 5 span a 2-dim space <u=(1,0,0,-1), v=(0,1,-1,0)>; the sine transform
acts there as a symmetric 2x2 with eigenvalues +-2.  The +2 eigenvector gives the FE.
"""
import mpmath as mp
from math import gcd
mp.mp.dps = 30

A = (4/mp.sqrt(5))*mp.sin(2*mp.pi/5)
B = (4/mp.sqrt(5))*mp.sin(4*mp.pi/5)
lam = mp.sqrt(A**2+B**2)
XI = (lam - A)/B
print(f"eigenvalue = {mp.nstr(lam,12)} (expect 2);  xi = {mp.nstr(XI,15)}")
print(f"  minimal poly check: xi satisfies B*xi^2 + 2A*xi - B = 0 ?  "
      f"{float(B*XI**2 + 2*A*XI - B):.2e}")

A_DH = [1, XI, -XI, -1, 0]          # a_1..a_5, odd mod 5, a_5 = 0
def dh(s): return mp.power(5,-s)*sum(A_DH[r-1]*mp.zeta(s, mp.mpf(r)/5) for r in range(1,6))

KNOWN = mp.mpc('0.808517','85.699348')
print(f"\nVALIDATION on the literature off-line zero 0.808517+85.699348i:")
print(f"  |f| = {float(abs(dh(KNOWN))):.3e}")
z = mp.findroot(dh, KNOWN)
print(f"  refined:  s = {mp.nstr(z,14)}   |f| = {float(abs(dh(z))):.2e}   Re = {float(mp.re(z)):.6f}")
assert abs(mp.re(z)-0.5) > 0.01, "not off-line"
print("  -> genuine OFF-LINE zero of a function with a functional equation and NO Euler product.")

def parts(s, coef, q, M):
    L = q*M//gcd(q,M)
    ds = sorted({gcd(r,q) for r in range(1,q+1)})
    return ds, [abs(mp.power(L,-s)*sum(coef(r)*mp.zeta(s,mp.mpf(r)/L)
                for r in range(1,L+1) if gcd(r,q)==d)) for d in ds]

def show(tag, coef, s, q, M):
    ds, v = parts(s, coef, q, M)
    print(f"  {tag}\n     parts: " + "  ".join(f"d={d}:{float(x):.2e}" for d,x in zip(ds,v)))

dhcoef = lambda n: A_DH[(n-1)%5]
print("\n=== DH (no Euler product) at its OWN zeros ===")
show("off-line zero 0.8085+85.6993i", dhcoef, z, 6, 5)
zon = mp.findroot(dh, mp.mpc(0.5, 18.0))
print(f"  [another DH zero: {mp.nstr(zon,12)}, Re={float(mp.re(zon)):.6f}]")
show("that zero", dhcoef, zon, 6, 5)

print("\n=== EULER controls at their own zeros (same instrument, q=6) ===")
show("zeta, zero #1", lambda n: 1, mp.mpc(0.5, mp.im(mp.zetazero(1))), 6, 1)
chi5 = lambda n: {1:1,2:-1,3:-1,4:1,0:0}[n%5]
z5 = mp.findroot(lambda s: mp.power(5,-s)*sum(chi5(r)*mp.zeta(s,mp.mpf(r)/5) for r in range(1,6)),
                 mp.mpc(0.5,6.6))
show(f"L(s,chi5) zero {mp.nstr(z5,10)}", chi5, z5, 6, 5)
