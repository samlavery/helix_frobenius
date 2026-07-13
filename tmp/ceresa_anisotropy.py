"""Depth-3 anisotropy, measured: the Ceresa heights of bielliptic Picard curves.

The retention/anisotropy front above grade one (JordanDriftTower.lean isolates the
frontier; this instrument measures its first genuine above-grade-one instance).
Laga--Shnidman (arXiv:2312.12965) prove, for the bielliptic Picard family

    C_t :  y^3 = x^4 + 2 t x^2 + 1        (genus 3, mu_6-action),

that the Ceresa cycle kappa(C_t) is torsion in CH_1(J_t) IFF the point

    Q_t = (cbrt(t^2 - 1), t)   on   E-hat : y^2 = x^3 + 1

is torsion, and that the Beilinson--Bloch height of kappa(C_t) is proportional to
the Neron--Tate height h-hat(Q_t).  So h-hat(Q_t) is a theorem-anchored READOUT of
the depth-3 drift pairing on this family:

    h-hat(Q_t) > 0  <=>  the depth-3 pairing is non-isotropic at kappa(C_t);
    h-hat(Q_t) = 0  exactly on the L-S torsion locus (t = 0, +-3 over Q) --
                    the honest boundary, verified EXACTLY here (finite orbits).

E-hat(Q) is rank 0 with torsion Z/6 = {oo, (-1,0), (0,+-1), (2,+-3)}, so Q_t is
RATIONAL only at the torsion locus (t^2 - 1 a perfect cube means (s,t) in
E-hat(Q)); generic t needs heights over the cubic field K = Q(theta),
theta^3 = t^2 - 1.  Implemented from scratch:

  * exact K-arithmetic (Fraction triples mod theta^3 = D);
  * x-only duplication on y^2 = x^3 + 1:  x(2P) = x(x^3 - 8) / (4(x^3 + 1));
  * absolute logarithmic Weil height of x_n in K via the exact characteristic
    polynomial (Newton traces, Fraction-exact) and its Mahler measure
    (mpmath roots at high precision);
  * h-hat(Q) ~= 4^{-n} h(x_n) at n = NDOUBLE (raw term; jet_census method law:
    Richardson unstable here, raw term converges like 4^{-n}).

Anisotropy verdict: h-hat > 0 with margin for every census t off the torsion
locus; EXACT 0 on it.  Run: python3 ceresa_anisotropy.py    (~1-2 min)
"""
import sys, os, math
from fractions import Fraction as Q

import mpmath as mp

NDOUBLE = 6

TORSION_T = [Q(0), Q(3), Q(-3)]          # the Laga-Shnidman locus over Q
GENERIC_T = [Q(2), Q(4), Q(5), Q(7), Q(1, 2), Q(9)]


# ---------------------------------------------------------------- K = Q(theta)
class K3:
    """Elements a + b theta + c theta^2 of Q(theta), theta^3 = D (D in Q)."""
    __slots__ = ("a", "b", "c", "D")

    def __init__(self, D, a=Q(0), b=Q(0), c=Q(0)):
        self.D, self.a, self.b, self.c = D, Q(a), Q(b), Q(c)

    def __add__(s, o):
        return K3(s.D, s.a + o.a, s.b + o.b, s.c + o.c)

    def __sub__(s, o):
        return K3(s.D, s.a - o.a, s.b - o.b, s.c - o.c)

    def __mul__(s, o):
        D = s.D
        a = s.a * o.a + D * (s.b * o.c + s.c * o.b)
        b = s.a * o.b + s.b * o.a + D * s.c * o.c
        c = s.a * o.c + s.b * o.b + s.c * o.a
        return K3(D, a, b, c)

    def scalar(s, q):
        return K3(s.D, s.a * q, s.b * q, s.c * q)

    def is_zero(s):
        return s.a == 0 and s.b == 0 and s.c == 0

    def mult_matrix(s):
        """3x3 Fraction matrix of multiplication by s in basis 1, theta, theta^2."""
        D = s.D
        return [[s.a, D * s.c, D * s.b],
                [s.b, s.a, D * s.c],
                [s.c, s.b, s.a]]

    def inv(s):
        """Inverse via adjugate of the multiplication matrix (exact)."""
        M = s.mult_matrix()
        det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
               - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
               + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
        if det == 0:
            raise ZeroDivisionError("non-invertible element")
        cof = [[(M[(i + 1) % 3][(j + 1) % 3] * M[(i + 2) % 3][(j + 2) % 3]
                 - M[(i + 1) % 3][(j + 2) % 3] * M[(i + 2) % 3][(j + 1) % 3])
                for j in range(3)] for i in range(3)]
        # inverse column acting on e1 = (1,0,0): first column of adjugate/det
        return K3(s.D, cof[0][0] / det, cof[0][1] / det, cof[0][2] / det)


def charpoly(al):
    """Exact characteristic polynomial z^3 + c2 z^2 + c1 z + c0 of mult-by-al,
    via Newton traces (Fractions)."""
    M = al.mult_matrix()

    def matmul(A, B):
        return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)]
                for i in range(3)]

    t1 = M[0][0] + M[1][1] + M[2][2]
    M2 = matmul(M, M)
    t2 = M2[0][0] + M2[1][1] + M2[2][2]
    M3 = matmul(M2, M)
    t3 = M3[0][0] + M3[1][1] + M3[2][2]
    c2 = -t1
    c1 = (t1 * t1 - t2) / 2
    c0 = -(t1 ** 3 - 3 * t1 * t2 + 2 * t3) / 6
    return [Q(1), c2, c1, c0]


def weil_height(al, dps):
    """Absolute logarithmic Weil height of al in K, from the exact charpoly:
    h = (1/3) (log|lead| + sum log^+ |roots|) after clearing denominators."""
    cp = charpoly(al)
    den = 1
    for c in cp:
        den = den * c.denominator // math.gcd(den, c.denominator)
    ints = [int(c * den) for c in cp]
    mp.mp.dps = dps
    roots = mp.polyroots([mp.mpf(v) for v in ints], maxsteps=200, extraprec=200)
    h = mp.log(abs(ints[0]))
    for r in roots:
        h += mp.log(max(1, abs(r)))
    return float(h / 3)


def x_double(x):
    """x(2P) = x (x^3 - 8) / (4 (x^3 + 1)) on y^2 = x^3 + 1; None at infinity."""
    x3 = x * x * x
    one, eight = K3(x.D, 1), K3(x.D, 8)
    den = (x3 + one).scalar(Q(4))
    if den.is_zero():
        return None
    return x * (x3 - eight) * den.inv()


def canonical_height(t, ndouble=NDOUBLE):
    """h-hat(Q_t), Q_t = (cbrt(t^2-1), t) on y^2 = x^3 + 1, over K = Q(theta).
    Returns (estimate at ndouble, torsion?, n, previous estimate at ndouble-1)
    -- the (n-1, n) pair is the convergence certificate (raw term converges
    like 4^-n).  Torsion = orbit hit infinity or became periodic (exact)."""
    D = t * t - 1
    x = K3(D, 0, 1, 0)                      # theta itself
    seen = []
    est_prev = None
    for n in range(1, ndouble + 1):
        x = x_double(x)
        if x is None:
            return 0.0, True, n, 0.0         # hit infinity: torsion, exactly
        key = (x.a, x.b, x.c)
        if key in seen:
            return 0.0, True, n, 0.0         # periodic orbit: torsion, exactly
        seen.append(key)
        if n == ndouble - 1:
            est_prev = weil_height(x, _dps_for(x)) / (4 ** n)
    h = weil_height(x, _dps_for(x))
    return h / (4 ** ndouble), False, ndouble, est_prev


def _dps_for(x):
    """Working precision matched to the largest coefficient of x (all three
    coordinates, numerators and denominators)."""
    bits = 0
    for v in (x.a, x.b, x.c):
        bits = max(bits, abs(v.numerator).bit_length(),
                   abs(v.denominator).bit_length())
    return max(60, int(bits * 0.302) + 120)


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# CERESA ANISOTROPY -- the depth-3 drift pairing, measured on the")
    P("# Laga-Shnidman family C_t: y^3 = x^4 + 2tx^2 + 1  (arXiv:2312.12965)")
    P("# readout: h-hat(Q_t), Q_t = (cbrt(t^2-1), t) on y^2 = x^3 + 1")
    P("#" * 78)
    P()
    P("  BOUNDARY (the L-S torsion locus over Q -- Ceresa torsion, exact):")
    ok_boundary = True
    for t in TORSION_T:
        h, tors, n, _ = canonical_height(t)
        ok = tors and h == 0.0
        ok_boundary = ok_boundary and ok
        P(f"    t = {str(t):>4s}: orbit terminated exactly at doubling {n} "
          f"-> h-hat = 0 (torsion)   {'OK' if ok else 'FAIL'}")
    P()
    P("  GENERIC CENSUS (off the locus -- anisotropy requires h-hat > 0;")
    P("  convergence certificate = |estimate(n) - estimate(n-1)|):")
    ok_generic = True
    conv_ok = True
    vals = {}
    for t in GENERIC_T:
        h, tors, n, hprev = canonical_height(t)
        pos = (not tors) and h > 1e-3
        dconv = abs(h - hprev)
        conv_ok = conv_ok and dconv < 5e-3
        ok_generic = ok_generic and pos
        vals[t] = h
        P(f"    t = {str(t):>4s}: h-hat(Q_t) ~= {h:10.6f}   conv |d| = {dconv:.1e}"
          f"   {'non-isotropic' if pos else '*** ISOTROPIC/FAIL ***'}")
    P()
    P("  pairwise separations (observation, not a pass/fail axis):")

    def torsion_translate(t, tp):
        """Numeric group-law check: Q_{t'} = s Q_t + T for a sign s and a
        torsion point T of y^2 = x^3 + 1?  Height equality then follows
        EXACTLY (canonical height is torsion-translation invariant)."""
        def cbrt(v):
            return v ** (1.0 / 3) if v >= 0 else -((-v) ** (1.0 / 3))

        x1, y1 = cbrt(float(t) ** 2 - 1), float(t)
        xp, yp = cbrt(float(tp) ** 2 - 1), float(tp)
        tors = [None, (-1.0, 0.0), (0.0, 1.0), (0.0, -1.0), (2.0, 3.0),
                (2.0, -3.0)]

        def add(Pt, Qt):
            if Pt is None:
                return Qt
            if Qt is None:
                return Pt
            (a, b), (c, d) = Pt, Qt
            if abs(a - c) < 1e-12:
                if abs(b + d) < 1e-9:
                    return None
                lam = (3 * a * a) / (2 * b)
            else:
                lam = (d - b) / (c - a)
            x3 = lam * lam - a - c
            return (x3, lam * (a - x3) - b)

        for s in (1, -1):
            for T in tors:
                R = add((x1, s * y1), T)
                if R and abs(R[0] - xp) < 1e-6 and abs(abs(R[1]) - abs(yp)) < 1e-6:
                    return s, T
        return None

    ts = list(vals)
    for i in range(len(ts)):
        for j in range(i + 1, len(ts)):
            d = abs(vals[ts[i]] - vals[ts[j]]) / max(vals[ts[i]], vals[ts[j]])
            if d < 0.01:
                rel = torsion_translate(ts[i], ts[j])
                if rel is not None:
                    s, T = rel
                    P(f"    COINCIDENCE RESOLVED: t = {ts[i]} vs t = {ts[j]} "
                      f"agree to {d:.1e} because Q_t' = "
                      f"{'+' if s == 1 else '-'}Q_t + {T if T else 'O'} "
                      f"(group law, verified numerically):")
                    P(f"      a torsion-translation symmetry of the L-S family "
                      f"(t'^2-1 = c^3 (t^2-1)); height equality is EXACT at the")
                    P(f"      Q-level -- discovered by the instrument, proven by "
                      f"the group law.  Not an anisotropy issue.")
                else:
                    P(f"    NEAR-COINCIDENCE UNRESOLVED: t = {ts[i]} vs "
                      f"t = {ts[j]} agree to {d:.1e} with no torsion-translation "
                      f"explanation found -- flagged for follow-up.")
    P()
    P("VERDICT:")
    if ok_boundary and ok_generic and conv_ok:
        P("  The depth-3 drift pairing is NON-ISOTROPIC at every census point off")
        P("  the Laga-Shnidman locus -- h-hat(Q_t) > 0 with clear margin and a")
        P("  passing convergence certificate -- and EXACTLY zero on the locus")
        P("  (finite orbits, no limit taken).  By L-S Thm 1.1/1.4 this is a")
        P("  theorem-anchored measurement of Beilinson-Bloch anisotropy ABOVE")
        P("  grade one: the first such reading in the program.  The isotropy")
        P("  locus exists, is exactly where the theorem puts it, and is detected")
        P("  exactly -- anisotropy off it is measured, not assumed.")
    else:
        P("  A FAILURE -- either an isotropic non-torsion point (a Beilinson-Bloch")
        P("  counterexample candidate!) or an instrument defect.  Publish per the")
        P("  falsifiability register and investigate with high priority.")
    P()
    P("  Scope: h-hat(Q_t) is the L-S proxy; the proportionality h(kappa) ~ h-hat")
    P("  is their theorem, consumed as a citation.  Heights over the cubic field")
    P("  Q(cbrt(t^2-1)) from scratch: exact field arithmetic, exact charpoly,")
    P("  Mahler measure at matched precision; raw 4^-n term at n=6 (rel. error")
    P("  ~1e-3, ample for anisotropy).  Next: larger census + height growth vs")
    P("  the L-S Northcott statement; then non-product K3 clause-(c).")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "ceresa_anisotropy_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to ceresa_anisotropy_results.txt]")


if __name__ == "__main__":
    main()
