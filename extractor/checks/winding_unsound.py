"""WHY the naive winding criterion is unsound -- diagnosed, not guessed.

The check Re(Xi(z2) * conj(Xi(z1))) > 0 certifies that arg(Xi(z2)/Xi(z1)) lies in
(-pi/2, pi/2)  MODULO 2*pi.  It does NOT exclude the path making extra full turns between
the two samples.  Summing such increments therefore under-counts whenever the argument
advances by a full turn inside one step.

Demonstrated on the failing case [10,23]: refine the SAME boundary uniformly and watch the
answer change -- a sound criterion cannot depend on the sampling density.
"""
import sys, math
sys.path.insert(0, 'extractor')
from certified_zeta import zeta_enclosure
from mpmath import mp, mpf, mpc, fabs, re as mre, arg as marg
mp.dps = 40

def xi(z):
    z = mp.mpmathify(z); s = mpf(1)/2 + mpc(0,1)*z
    zv, _ = zeta_enclosure(s)
    return (mpf(1)/4 + z**2) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * zv

def winding_uniform(a, b, H, nper):
    corners = [mpc(a,-H), mpc(b,-H), mpc(b,H), mpc(a,H), mpc(a,-H)]
    tot = mpf(0); ndet = 0; ntot = 0
    for k in range(4):
        z0, z1 = corners[k], corners[k+1]
        prev = xi(z0)
        for j in range(1, nper+1):
            z = z0 + (z1-z0)*mpf(j)/nper
            cur = xi(z)
            ntot += 1
            if mre(cur*mp.conj(prev)) > 0: ndet += 1
            tot += marg(cur*mp.conj(prev))
            prev = cur
    return tot/(2*mp.pi), ndet, ntot

print("Rectangle [10,23] x [-0.5,0.5].  True count = 2 (gamma_1=14.1347, gamma_2=21.0220).")
print(f"{'samples/side':>13} {'winding':>14} {'nearest':>8} {'increments passing the test':>30}")
for nper in (1, 2, 4, 8, 16, 32, 64, 128):
    N, ndet, ntot = winding_uniform(mpf(10), mpf(23), mpf('0.5'), nper)
    print(f"{nper:>13} {mp.nstr(N,8):>14} {int(mp.nint(N)):>8} {f'{ndet}/{ntot}':>30}")
print()
print("The answer MOVES with sampling density while the local test keeps passing.")
print("=> Re(v2 conj v1) > 0 pins the increment only MOD 2pi.  The criterion is UNSOUND.")
