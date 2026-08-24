#!/usr/bin/env python3
"""
att257 — THE SURVIVING QUESTION: does the archimedean block dominate, uniformly,
including at a Lehmer pair?

Two soft levers on the census signature are now closed by computation
(Pontryagin saturation; rank bound vacuous since the prime block is full rank).
What remains is the QUANTITATIVE domination:

    H_n(W) = H^pole + H^arch - H^prime + H^lat,      all of the first three PSD,

and positivity has to come from arch+pole beating prime+lateral on the
minimizing direction.  Measured once before at one generic window (ratio 1.23).
The claim under test is that this is the MECHANISM, uniformly - not an artifact
of a well-conditioned window.

HOSTILE CONFIGURATION (pre-registered): the Lehmer pair near gamma = 7005.0629,
gap ~ 4e-4, where the support is near-degenerate, the Vandermonde is
ill-conditioned, and the minimizing direction is the collision direction rather
than a generic one.  My log-t argument for arch growth applies to the generic
direction and I have no reason to think it transfers.

PREDICTION (pre-registered): 0.45 that arch still dominates at the Lehmer pair.

DECISION RULE (pre-registered): REFUTES the mechanism if at the Lehmer window
the arch energy is <= 0, or is exceeded by |prime + lateral|, while the
assembled H_n is still PSD - positivity there comes from somewhere else.
SUPPORTS if arch dominates at every window including the hostile ones.

Conventions: A(z) = xi(1/2 - i z), moments taken CENTERED at the window midpoint
(a real translation of the support, which leaves Hankel inertia invariant and
keeps the dynamic range finite).  mu_0 must reproduce the zero count - that is
the built-in validation of the contour machinery.
"""
import mpmath as mp

mp.mp.dps = 30

LOGPI = mp.log(mp.pi)

def zeta_logderiv(s):
    return mp.zeta(s, derivative=1) / mp.zeta(s)

def blocks_at(s):
    """(pole, arch, prime) parts of xi'/xi at s."""
    pole = 1 / s + 1 / (s - 1)
    arch = -LOGPI / 2 + mp.digamma(s / 2) / 2
    prime = zeta_logderiv(s)
    return pole, arch, prime

def moments_window(a, b, Y=mp.mpf('1.5'), kmax=10, quadpts=None):
    """centered contour moments, split into (pole, arch, prime, lateral)."""
    c = (a + b) / 2
    mu = {name: [mp.mpc(0)] * (kmax + 1)
          for name in ('pole', 'arch', 'prime', 'lat')}

    # horizontal edges: z = x +- iY, s = 1/2 - i z
    def horiz(sign):
        def f(x):
            z = mp.mpc(x, sign * Y)
            s = mp.mpf(0.5) - 1j * z
            if mp.re(s) > mp.mpf('0.5'):
                po, ar, pr = blocks_at(s)
            else:
                # FE image: xi'/xi(s) = -xi'/xi(1-s), split on the convergent side
                po, ar, pr = blocks_at(1 - s)
                po, ar, pr = -po, -ar, -pr
            # dz = dx along the top (left-to-right for sign=-1 orientation)
            return (z - c, (-1j) * po, (-1j) * ar, (-1j) * pr)
        return f

    for sign, orient in ((-1, +1), (+1, -1)):   # bottom L->R, top R->L
        f = horiz(sign)
        for k in range(kmax + 1):
            for nm, idx in (('pole', 1), ('arch', 2), ('prime', 3)):
                val = mp.quad(lambda x: (f(x)[0] ** k) * f(x)[idx], [a, b])
                mu[nm][k] += orient * val / (2 * mp.pi * 1j)

    # lateral edges: z = a + i y and z = b + i y
    for x0, orient in ((a, -1), (b, +1)):
        def g(y, x0=x0):
            z = mp.mpc(x0, y)
            s = mp.mpf(0.5) - 1j * z
            return (z - c, (-1j) * (1 / s + 1 / (s - 1) - LOGPI / 2
                                    + mp.digamma(s / 2) / 2 + zeta_logderiv(s)))
        for k in range(kmax + 1):
            val = mp.quad(lambda y: (g(y)[0] ** k) * g(y)[1] * 1j, [-Y, Y])
            mu['lat'][k] += orient * val / (2 * mp.pi * 1j)
    return mu

def hankel(muk, n):
    return mp.matrix(n, n, lambda i, j: muk[i + j])

def report(a, b, label, nlist=(3, 4), kmax=10):
    print(f"\n=== {label}: W = ({a}, {b}) ===", flush=True)
    mu = moments_window(mp.mpf(a), mp.mpf(b), kmax=kmax)
    tot = [mu['pole'][k] + mu['arch'][k] + mu['prime'][k] + mu['lat'][k]
           for k in range(kmax + 1)]
    print(f"  mu_0 (zero count) = {mp.nstr(tot[0], 12)}")
    for n in nlist:
        H = mp.matrix(n, n, lambda i, j: mp.re(tot[i + j]))
        try:
            E, V = mp.eigsy(mp.matrix([[mp.re(H[i, j]) for j in range(n)]
                                       for i in range(n)]))
        except Exception as e:
            print(f"  n={n}: eig failed {e}")
            continue
        lam = min(E)
        idx = list(E).index(lam)
        v = [V[i, idx] for i in range(n)]
        def energy(name):
            return sum(v[i] * mp.re(mu[name][i + j]) * v[j]
                       for i in range(n) for j in range(n))
        ep, ea, epr, el = (energy('pole'), energy('arch'),
                           energy('prime'), energy('lat'))
        drain = epr + el
        ratio = (ea + ep) / abs(drain) if drain != 0 else mp.inf
        print(f"  n={n}: lam_min={mp.nstr(lam,6)}  pole={mp.nstr(ep,4)} "
              f"arch={mp.nstr(ea,4)} prime={mp.nstr(epr,4)} lat={mp.nstr(el,4)}")
        print(f"        (pole+arch)/|prime+lat| = {mp.nstr(ratio,5)}"
              f"   {'ARCH DOMINATES' if ratio > 1 else 'DOES NOT DOMINATE'}")

if __name__ == "__main__":
    report(10, 30, "control, generic (validated window)")
    report(100, 130, "generic, higher")
    report(7000, 7010, "HOSTILE: contains Lehmer pair 7005.0629")
    report(7004.5, 7005.6, "HOSTILE: tight on the Lehmer pair")
