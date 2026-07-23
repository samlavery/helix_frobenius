# Radial-Torelli pilot, genus 1: "does the radius remember the curve",
# closed end to end.  The radial arm computes the period lattice (AGM)
# from the curve; the FIREWALL hands only (w1, w2) to the Torelli arm,
# which reconstructs j via the classical modular formula and must land
# the exact rational j of the curve (continued-fraction recognition).
from mpmath import mp, mpf, mpc, agm, kleinj, sqrt, pi, im, re, polyroots, mpmathify
from fractions import Fraction

mp.dps = 50

CURVES = {
    '11a1':  [0, -1, 1, -10, -20],
    '37a1':  [0, 0, 1, -1, 0],
    '389a1': [0, 1, 1, -2, 0],
    '5077a1':[0, 0, 1, -7, 6],
}

def invariants(a):
    a1, a2, a3, a4, a6 = a
    b2 = a1*a1 + 4*a2
    b4 = 2*a4 + a1*a3
    b6 = a3*a3 + 4*a6
    c4 = b2*b2 - 24*b4
    c6 = -b2**3 + 36*b2*b4 - 216*b6
    disc = (c4**3 - c6**2) // 1728
    jnum, jden = 1728*c4**3, c4**3 - c6**2
    return c4, c6, disc, Fraction(jnum, jden)

def periods(c4, c6):
    # y^2 = 4x^3 - (c4/48)*4... use y^2 = 4x^3 - g2 x - g3 with
    # g2 = c4/12, g3 = c6/216
    g2, g3 = mpf(c4)/12, mpf(c6)/216
    rts = polyroots([mpf(4), mpf(0), -g2, -g3], extraprec=80)
    rts = sorted([mpc(r) for r in rts], key=lambda z: re(z))
    if all(abs(im(r)) < mpf(10)**-30 for r in rts):
        e3, e2, e1 = [re(r) for r in rts]
        w1 = pi / agm(sqrt(e1 - e3), sqrt(e1 - e2))
        w2 = 1j * pi / agm(sqrt(e1 - e3), sqrt(e2 - e3))
    else:
        # one real root (e1); complex pair a +- bi
        reals = [r for r in rts if abs(im(r)) < mpf(10)**-30]
        cplx = [r for r in rts if abs(im(r)) >= mpf(10)**-30]
        e1 = re(reals[0])
        a, b = re(cplx[0]), abs(im(cplx[0]))
        A = sqrt(3*e1*e1 - g2/4)          # |e1 - a +- bi| structure
        M = agm(2*sqrt(A), sqrt(2*A + 3*e1))
        w1 = 2*pi / M                      # real period
        Mi = agm(2*sqrt(A), sqrt(2*A - 3*e1))
        w2 = w1/2 + 1j*pi/Mi               # standard lattice completion
    return w1, w2

print(f"{'curve':8s} {'tau':>24s}  reconstructed j == true j?")
for name, a in CURVES.items():
    c4, c6, disc, jtrue = invariants(a)
    w1, w2 = periods(c4, c6)
    # ---------------- FIREWALL: only (w1, w2) cross ----------------
    tau = w2 / w1
    if im(tau) < 0:
        tau = -tau
    jrec = kleinj(tau) * 1728
    # rational recognition with verification gate
    jr = Fraction(mp.nstr(re(jrec), 40, strip_zeros=False))
    jrat = jr.limit_denominator(10**7)
    gate = abs(re(jrec) - mpf(jrat.numerator)/mpf(jrat.denominator))
    ok = (jrat == jtrue) and gate < mpf(10)**-25 and abs(im(jrec)) < mpf(10)**-25
    print(f"{name:8s} {complex(tau).real:+.4f}{complex(tau).imag:+.4f}i  "
          f"{'EXACT MATCH  j = ' + str(jtrue) if ok else 'MISMATCH: rec ' + str(jrat) + ' vs true ' + str(jtrue)}")
