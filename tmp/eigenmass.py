"""Eigenmass: |accumulated phasor| -> 0 at the vanishing event.
Geometry: integer n at height n (pitch 1), carrier spin n*pi/3 (mu6), mass grows from 0.
Bank is COMPLEX: sum_n chi(n) * mass(n) * exp(i * n * pi/3).  Watch |.|, not Re.
"""
import mpmath as mp
mp.mp.dps = 30
PI = mp.pi
def ph(n): return mp.e**(1j*(n*PI/3))
def chi3(n):
    r=n%3;  return 1 if r==1 else (-1 if r==2 else 0)
def triv(n): return 1
def eta(n):  return 1 if n%2==1 else -1

def bank(chifn, mass, N):
    return sum(chifn(n)*mass(n)*ph(n) for n in range(1,N+1))

masses = [("unit        ", lambda n: mp.mpf(1)),
          ("linear r*n  ", lambda n: mp.mpf(n)),
          ("readout n^-½", lambda n: mp.power(n,-0.5))]
chars  = [("chi3", chi3), ("trivial", triv), ("eta", eta)]

print("=== |bank| as N runs over cell boundaries (eigenmass) ===")
for cname, cf in chars:
    print(f"\n  {cname}")
    for mname, m in masses:
        row=[]
        for N in (3,6,9,12,60,600,6000):
            row.append(f"N={N}:{float(abs(bank(cf,m,N))):.4g}")
        print(f"    {mname} " + "  ".join(row))

print("\n=== within one cell: |bank| step by step (chi3, unit mass) ===")
for N in range(1,13):
    print(f"    N={N:2d}  |bank| = {float(abs(bank(chi3,lambda n: mp.mpf(1),N))):.6f}")
