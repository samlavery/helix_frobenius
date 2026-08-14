"""DIVISOR-CLASS COHERENCE as an Euler-product detector.

For a bank with an Euler product,  sum_{gcd(n,q)=d} a_n n^-s  is a MULTIPLE of the
whole L-function, so EVERY divisor class closes at a zero, simultaneously.
Without an Euler product there is no such factorisation -- the classes should NOT close.

Specimens:  zeta (Euler), L(s,chi_5) (Euler), Davenport-Heilbronn (NO Euler, zeros OFF line).
"""
import mpmath as mp
from math import gcd
mp.mp.dps = 30

# ---- Davenport-Heilbronn: a_n periodic mod 5, odd: (1, xi, -xi, -1, 0) ----
# xi fixed by the odd-DFT eigenvector condition; validate on the known off-line zero.
def dh_xi():
    s2, s4 = mp.sin(2*mp.pi/5), mp.sin(4*mp.pi/5)
    # sine-transform eigenvector, row m=1:  (2/sqrt5)[s2 + xi*s4 + xi*s4 + s2] = eig * 1
    for eig in (1, -1):
        xi = (eig*mp.sqrt(5)/2 - 2*s2) / (2*s4)
        yield xi

def dh(s, xi):
    a = [1, xi, -xi, -1, 0]
    return mp.power(5,-s)*sum(a[r-1]*mp.zeta(s, mp.mpf(r)/5) for r in range(1,6))

KNOWN = mp.mpc('0.808517', '85.699348')   # classical DH off-line zero
best=None
for xi in dh_xi():
    v = abs(dh(KNOWN, xi))
    print(f"  xi = {mp.nstr(xi,10)}   |f(0.808517+85.699348i)| = {float(v):.3e}")
    if best is None or v < best[1]: best=(xi,v)
XI = best[0]
print(f"  -> using xi = {mp.nstr(XI,12)}  (validated on the known off-line zero)\n")

def chi5(n):   # a real character mod 5 (quadratic): 1,-1,-1,1 on 1,2,3,4
    r=n%5
    return {1:1,2:-1,3:-1,4:1,0:0}[r]

Q = 30  # common modulus: lcm(5,6)=30 -> handles mod-5 coefficients and gcd(.,6)/gcd(.,30)
def classes(q): return sorted({gcd(r,q) for r in range(1,q+1)})

def part(s, coef, q, d, M=30):
    """sum over n with gcd(n,q)=d, coefficients coef(n) periodic mod M."""
    L = q*M // gcd(q,M)
    return mp.power(L,-s)*sum(coef(r)*mp.zeta(s, mp.mpf(r)/L)
                              for r in range(1,L+1) if gcd(r,q)==d)

def run(tag, coef, s, q=6, M=5):
    ds = classes(q)
    vals=[abs(part(s,coef,q,d,M)) for d in ds]
    tot = abs(sum(part(s,coef,q,d,M) for d in ds))
    print(f"  {tag}")
    print(f"     total |f(s)| = {float(tot):.2e}   parts: " +
          "  ".join(f"d={d}:{float(v):.2e}" for d,v in zip(ds,vals)))
    return max(vals)/max(tot,mp.mpf('1e-300'))

print("=== EULER SPECIMENS: parts must all close ===")
g=mp.im(mp.zetazero(1))
run("zeta, zero #1", lambda n: 1, mp.mpc(0.5,g), q=6, M=1)
run("zeta, zero #3", lambda n: 1, mp.mpc(0.5,mp.im(mp.zetazero(3))), q=6, M=1)
# a zero of L(s,chi5)
z5 = mp.findroot(lambda s: mp.power(5,-s)*sum(chi5(r)*mp.zeta(s,mp.mpf(r)/5) for r in range(1,6)),
                 mp.mpc(0.5,6.6))
print(f"  [L(s,chi5) zero found at {mp.nstr(z5,12)}]")
run("L(s,chi5), that zero", chi5, z5, q=6, M=5)

print("\n=== NON-EULER SPECIMEN: Davenport-Heilbronn ===")
run("DH at its OFF-LINE zero 0.8085+85.6993i", lambda n: [1,XI,-XI,-1,0][n%5-1] if n%5 else 0,
    KNOWN, q=6, M=5)
# find an ON-line DH zero too
zdh = mp.findroot(lambda s: dh(s,XI), mp.mpc(0.5, 85.0))
print(f"  [DH zero found near t=85: {mp.nstr(zdh,12)}]")
run("DH at that zero", lambda n: [1,XI,-XI,-1,0][n%5-1] if n%5 else 0, zdh, q=6, M=5)
