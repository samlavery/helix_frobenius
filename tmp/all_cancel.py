"""'At a zero, ALL phasors cancel.'
Partition the bank by gcd(n,q).  Each part is  sum_{gcd(n,q)=d} n^-s  = d^-s * prod_{p|q}(...)* zeta(s)
i.e. a zeta-MULTIPLE, so EVERY part closes at a zero -- at every level of the divisor lattice.
Verify directly by summing the actual Dirichlet series (Hurwitz-assembled), for several q.
"""
import mpmath as mp
mp.mp.dps=30
from math import gcd

def part_sum(s, q, d):
    """sum over n with gcd(n,q)=d, via residue classes mod q."""
    tot = mp.mpf(0)
    for r in range(1, q+1):
        if gcd(r, q) == d:
            tot += mp.power(q, -s) * mp.zeta(s, mp.mpf(r)/q)
    return tot

for q in (6, 12, 30):
    divs = sorted({gcd(r,q) for r in range(1,q+1)})
    print(f"\n=== q={q}, divisor classes {divs} ===")
    for k in (1,3,10):
        g=mp.im(mp.zetazero(k)); s=mp.mpc(0.5,g)
        vals=[abs(part_sum(s,q,d)) for d in divs]
        print(f"  zero #{k:2d}: " + "  ".join(f"|d={d}|={float(v):.2e}" for d,v in zip(divs,vals)))
    s=mp.mpc(0.5,17.0)
    vals=[abs(part_sum(s,q,d)) for d in divs]
    print(f"  CONTROL t=17: " + "  ".join(f"|d={d}|={float(v):.4f}" for d,v in zip(divs,vals)))
    g=mp.im(mp.zetazero(1)); s=mp.mpc(0.6,g)
    vals=[abs(part_sum(s,q,d)) for d in divs]
    print(f"  CONTROL off-line s=0.6+i*g1: " + "  ".join(f"|d={d}|={float(v):.4f}" for d,v in zip(divs,vals)))
