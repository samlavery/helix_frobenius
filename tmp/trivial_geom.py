import mpmath as mp
mp.mp.dps = 25
PI = mp.pi
def spin(n): return n*PI/3
def cell(w, name):
    print(f"\n  {name}")
    print("   n mod 6:", "  ".join(f"{n%6:>5d}" for n in range(1,7)))
    print("   weight :", "  ".join(f"{w(n):>+5.2f}" for n in range(1,7)))
    prod=[w(n)*float(mp.cos(spin(n))) for n in range(1,7)]
    print("   product:", "  ".join(f"{p:>+5.2f}" for p in prod), f"   SUM={sum(prod):+.3f}")
    for N in (6,60,600,6000):
        tot=sum(w(n)*mp.cos(spin(n)) for n in range(1,N+1))
        print(f"     N={N:<5d} unit-mass bank = {float(tot):+.3e}", end="")
        totm=sum(w(n)*n*mp.cos(spin(n)) for n in range(1,N+1))
        print(f"    linear-mass = {float(totm):+.6g}")

cell(lambda n: 1 if n%3==1 else (-1 if n%3==2 else 0), "chi3  (quadratic mod 3)")
cell(lambda n: 1.0,                                     "trivial chi == 1 (bare zeta bank)")
cell(lambda n: 1.0 if n%2==1 else -1.0,                 "eta / alternating (trivial char, Re>0)")
