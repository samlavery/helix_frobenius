"""*** UNSOUND -- KEPT AS A RECORD, DO NOT USE AS A CERTIFIER ***

This is the FIRST attempt at a certified count.  Its acceptance test,
Re(Xi(z2) conj(Xi(z1))) > 0, pins the argument increment only MOD 2*pi and therefore does
NOT exclude a full turn hiding inside a step.  On [10,23] it returns 0 where the truth is 2.
See checks/winding_unsound.py for the demonstration, and checks/certified_count.py for the
SOUND version, which uses the explicit region bound of region_bounds.py.

Original header follows.

CERTIFIED COUNT via the argument principle -- closing the count interface.

N = (1/2pi) * [total change of arg Xi around a rectangle].  The winding number is an INTEGER,
so it only has to be pinned to within +-1/2 a turn.  Walk the boundary; between consecutive
samples z_k, z_{k+1} the increment is arg(Xi(z_{k+1})/Xi(z_k)).  If we CERTIFY
    Re( Xi(z_{k+1}) * conj(Xi(z_k)) ) > 0
then that increment lies in (-pi/2, pi/2) and is determined; refine the step until it does.
Summing determined increments gives the winding number exactly.

Everything rests on the certified enclosure of Xi built from certified_zeta.
"""
import sys, os, math
sys.path.insert(0, 'extractor')
from certified_zeta import zeta_enclosure
from mpmath import mp, mpf, mpc, fabs, re as mre, im as mim, arg as marg
mp.dps = 40

def xi_enclosure(z):
    """Xi(z) = (1/4+z^2) pi^{-s/2} Gamma(s/2) zeta(s), s = 1/2+iz.  Returns (value, radius)."""
    z = mp.mpmathify(z)
    s = mpf(1)/2 + mpc(0,1)*z
    zv, zr = zeta_enclosure(s)
    A = (mpf(1)/4 + z**2) * mp.power(mp.pi, -s/2) * mp.gamma(s/2)
    val = A*zv
    relA = mpf(10)**(-mp.dps+3)          # relative error of the elementary prefactor
    rad = fabs(A)*zr + fabs(val)*relA
    return val, rad

def determined(v1, r1, v2, r2):
    """Is Re(v2 * conj(v1)) > 0 CERTIFIED, given the two enclosures?"""
    p = v2*mp.conj(v1)
    # |d(v2 conj v1)| <= |v2| r1 + |v1| r2 + r1 r2
    err = fabs(v2)*r1 + fabs(v1)*r2 + r1*r2
    return mre(p) > err

def winding_count(a, b, H=mpf('0.5'), maxdepth=18):
    """zeros of Xi inside the rectangle [a,b] x [-H,H]; returns (N, samples) or None."""
    corners = [mpc(a,-H), mpc(b,-H), mpc(b,H), mpc(a,H), mpc(a,-H)]
    total = mpf(0); nsamp = 0
    for k in range(4):
        z0, z1 = corners[k], corners[k+1]
        stack = [(z0, z1, 0)]
        while stack:
            p, q, d = stack.pop()
            vp, rp = xi_enclosure(p); vq, rq = xi_enclosure(q); nsamp += 2
            if determined(vp, rp, vq, rq):
                total += marg(vq*mp.conj(vp))
            else:
                if d >= maxdepth: return None, nsamp
                m = (p+q)/2
                stack.append((m, q, d+1)); stack.append((p, m, d+1))
    N = total/(2*mp.pi)
    return N, nsamp

print("=== certified zero counts of Xi in [a,b] x [-1/2,1/2] ===")
print(f"{'a':>10} {'b':>10} {'winding':>14} {'nearest int':>12} {'evals':>7}")
# brackets straddling known ordinates: gamma_1=14.1347, gamma_2=21.0220, gamma_3=25.0109
for a, b, expect in [(10.0, 16.0, 1), (10.0, 23.0, 2), (10.0, 26.0, 3),
                     (16.0, 23.0, 1), (23.0, 26.0, 1), (26.0, 29.0, 0)]:
    N, ns = winding_count(mpf(a), mpf(b))
    if N is None:
        print(f"{a:>10.3f} {b:>10.3f} {'UNDETERMINED':>14} {'':>12} {ns:>7}")
    else:
        print(f"{a:>10.3f} {b:>10.3f} {mp.nstr(N,10):>14} {int(mp.nint(N)):>12} {ns:>7}"
              f"   expected {expect}  {'OK' if int(mp.nint(N))==expect else 'MISMATCH'}")
