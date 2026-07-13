"""The recognition demo: the converse leg closed at grade one, in-house.

The terminus's hardest ingredient is the CONVERSE LEG: from a fired ledger
coordinate to a CONSTRUCTED cycle.  Grade one is the only place mathematics has
ever closed that loop -- Gross-Zagier-Kolyvagin: the fired first jet (L' != 0)
plus a CM clock alignment (a Heegner point on the modular curve) CONSTRUCTS a
rational point through the modular parametrization.  This instrument runs the
loop end-to-end with house machinery only:

  1. the fiber: a_n of 37a1 from POINT COUNTS (sha_hinge.bank_general);
  2. the clock alignment: a Heegner point tau on X_0(37) -- an imaginary
     quadratic clock (class number one, 37 split) aligned with the level-37
     modular clock: tau = (-B + sqrt(-D)) / 74, B^2 = -D mod 148;
  3. the construction: z = sum a_n/n q^n (the modular parametrization,
     evaluated -- the Abel-Jacobi image of the alignment);
  4. the landing: the trace 2 Re(z) in C/Lambda, with Lambda from our own AGM
     periods; x = wp(z) by the Weierstrass q-series;
  5. THE RECOGNITION GATE (exact): x is recognized as a rational by continued
     fractions, y is solved in Q, and the point is verified on
     y^2 + y = x^3 - x in EXACT arithmetic -- any normalization error anywhere
     upstream makes this gate fail loudly;
  6. the audit: canonical height of the constructed point vs the regulator
     (jet_census machinery): the ratio is the Heegner index squared -- an
     integer landing; and the fired jet L'(37a1,1) = 0.306 (drift instrument)
     is what Gross-Zagier says the construction realizes.

Register: the construction is the classical GZ loop run on house instruments;
nothing here is a new theorem -- it is the OPERATIONAL TEMPLATE of the
recognition problem the terminus needs at every grade, demonstrated at the one
grade where it is a theorem.  Run: python3 heegner_recognition.py   (~30 s)
"""
import sys, os, math, cmath
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
import jet_census as JC
import hodge_clock_demo as HC

N = 37
AINV = (0, 0, 1, -1, 0)          # 37a1: y^2 + y = x^3 - x
CLASS_ONE_D = [3, 4, 7, 8, 11, 19, 43, 67, 163]


def heegner_disc():
    """Smallest class-number-one D with 37 split in Q(sqrt(-D)); D = 3, 4 are
    skipped (extra roots of unity in K twist the Heegner machinery)."""
    for D in CLASS_ONE_D:
        if D in (3, 4):
            continue
        if pow((-D) % N, (N - 1) // 2, N) == 1:
            for B in range(2 * N):
                if (B * B + D) % (4 * N) == 0:
                    return D, B
    raise RuntimeError("no Heegner discriminant found")


def modular_image(tau, nmax=4000):
    """z = sum_{n} (a_n / n) e^{2 pi i n tau} -- a_n from point counts."""
    bad = {int(p): SH.a_bad(int(p), AINV) for p in SH.sieve_primes(N)
           if N % int(p) == 0}
    a = SH.bank_general(N, AINV, bad, nmax)
    q = cmath.exp(2j * math.pi * tau)
    z, qn = 0j, 1
    for n in range(1, nmax + 1):
        qn *= q
        z += a[n] / n * qn
    return z


def lattice():
    """(w1, w2) of 37a1, SELF-CERTIFIED.  sha_hinge.real_period is the BSD
    period Omega (both real components for disc > 0), and the clock demo's tau
    is the SL2-reduced modulus -- which pins the lattice shape only up to the
    generator assignment (tau vs -1/tau) and leaves the absolute scale to fix.
    So: scan {Omega, Omega/2} x {tau, 1/tau assignments} and return the basis
    passing BOTH half-period certificates wp(w1/2) = e1 and wp(w2/2) = e3."""
    import numpy as np
    inv = SH.invariants(AINV)
    roots = sorted(r.real for r in
                   np.roots([1.0, inv["b2"] / 4.0, inv["b4"] / 2.0,
                             inv["b6"] / 4.0]) if abs(r.imag) < 1e-9)
    e3, e1 = roots[0], roots[-1]
    Om = SH.real_period(AINV)
    tauE, err = HC.curve_tau(AINV)
    assert err < 1e-8, "period certificate failed"
    ratio = abs(tauE.imag)
    for s in (0.5, 1.0):
        for r in (ratio, 1.0 / ratio):
            w1 = Om * s
            w2 = 1j * r * w1
            d1 = abs(wp(complex(w1 / 2, 0.0), w1, w2).real - e1)
            d3 = abs(wp(w2 / 2, w1, w2).real - e3)
            if d1 < 1e-9 and d3 < 1e-9:
                return w1, w2
    raise RuntimeError("no lattice basis passed both half-period certificates")


def lattice_certificate(w1, w2):
    """wp(w1/2) must equal the largest real root of the completed cubic
    x^3 + (b4/2) x + b6/4 -- pins the lattice scale before any recognition."""
    import numpy as np
    inv = SH.invariants(AINV)
    roots = np.roots([1.0, inv["b2"] / 4.0, inv["b4"] / 2.0, inv["b6"] / 4.0])
    e1 = max(r.real for r in roots if abs(r.imag) < 1e-9)
    val = wp(complex(w1 / 2, 0.0), w1, w2)
    return abs(val.real - e1), e1, val


def wp(z, w1, w2, nmax=200):
    """Weierstrass wp(z; Lambda) by the standard q-series."""
    tau = w2 / w1
    q = cmath.exp(2j * math.pi * tau)
    w = cmath.exp(2j * math.pi * (z / w1))
    s = Q(1, 12) * 1.0 + w / (1 - w) ** 2
    qn = 1
    for n in range(1, nmax + 1):
        qn *= q
        for u in (w, 1 / w):
            s += qn * u / (1 - qn * u) ** 2
        s -= 2 * qn / (1 - qn) ** 2
    return (2j * math.pi / w1) ** 2 * s


def recognize_rational(v, qmax=10 ** 6, tol=1e-8):
    """Continued-fraction recognition of a real float as p/q, verified to tol."""
    from fractions import Fraction
    fr = Fraction(v).limit_denominator(qmax)
    if abs(float(fr) - v) < tol * max(1.0, abs(v)):
        return fr
    return None


def on_curve(x, y):
    a1, a2, a3, a4, a6 = AINV
    return y * y + a1 * x * y + a3 * y == x ** 3 + a2 * x * x + a4 * x + a6


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# HEEGNER RECOGNITION -- the converse leg closed at grade one, in-house")
    P("# fired jet (L' != 0) + CM clock alignment  =>  a CONSTRUCTED point")
    P("#" * 78)
    P()
    D, B = heegner_disc()
    tau = complex(-B, math.sqrt(D)) / (2 * N)
    P(f"  clock alignment: D = -{D} (class number 1, 37 split), B = {B}")
    P(f"  Heegner point tau = ({-B} + sqrt(-{D})) / {2 * N}, "
      f"Im tau = {tau.imag:.5f}, |q| = {math.exp(-2 * math.pi * tau.imag):.4f}")
    z = modular_image(tau)
    P(f"  modular image z = {z.real:+.10f} {z.imag:+.10f}i   "
      f"(a_n from point counts only)")
    w1, w2 = lattice()
    P(f"  lattice: w1 = {w1:.10f}, w2 = {w2.real:+.2e} {w2.imag:+.10f}i "
      f"(AGM; real generator = Omega / #components)")
    dev, e1, _ = lattice_certificate(w1, w2)
    P(f"  lattice certificate: wp(w1/2) vs largest cubic root e1 = {e1:.8f}: "
      f"|dev| = {dev:.1e}  {'OK' if dev < 1e-8 else 'FAIL'}")
    if dev >= 1e-8:
        P("  ABORT: lattice normalization wrong; fix before recognition.")
        return
    P()

    # the K-trace: conjugate Heegner point maps to complex conjugate, so the
    # E(Q) candidate is z + z-bar = 2 Re(z) mod Lambda (rectangular lattice);
    # both real components (u and u + w2/2) are tried -- the recognition gate
    # decides.
    found = None
    for name, u in [("2Re(z)", complex(2 * z.real, 0.0)),
                    ("2Re(z)+w2/2", complex(2 * z.real, 0.0) + w2 / 2)]:
        ur = complex(u.real % w1, u.imag)
        xw = wp(ur, w1, w2)
        if abs(xw.imag) > 1e-6:
            P(f"  candidate {name}: wp not real ({xw.imag:+.1e}) -- rejected")
            continue
        # completed-square model x^3 + (b2/4)x^2 + ... has the same x; b2 = 0
        xf = xw.real
        xr = recognize_rational(xf)
        if xr is None:
            P(f"  candidate {name}: x = {xf:.10f} not recognized -- rejected")
            continue
        # solve y in Q exactly: y^2 + y = x^3 - x
        rhs = xr ** 3 - xr
        disc = 1 + 4 * rhs
        num, den = disc.numerator, disc.denominator
        sn, sd = math.isqrt(abs(num)), math.isqrt(den)
        if num < 0 or sn * sn != num or sd * sd != den:
            P(f"  candidate {name}: x = {xr} recognized but y not rational -- "
              f"rejected")
            continue
        y = (Q(-1) + Q(sn, sd)) / 2
        if not on_curve(xr, y):
            y = (Q(-1) - Q(sn, sd)) / 2
        assert on_curve(xr, y)
        found = (name, xr, y)
        break
    P()
    if found is None:
        P("VERDICT: RECOGNITION FAILED -- a normalization upstream is wrong, or")
        P("  the trace landed on torsion invisible to this reduction.  The gate")
        P("  did its job; investigate before any claim.")
    else:
        name, xr, y = found
        P(f"  RECOGNIZED (via {name}):  P = ({xr}, {y})   -- exact, on")
        P(f"  y^2 + y = x^3 - x verified in rational arithmetic.")
        hP = JC.canonical_height_naive((xr, y), AINV)[0]
        gen = (Q(0), Q(0))
        hG = JC.canonical_height_naive(gen, AINV)[0]
        ratio = hP / hG if hG > 0 else float("inf")
        P(f"  audit: h-hat(P) = {hP:.6f};  h-hat(generator (0,0)) = {hG:.6f};")
        P(f"         ratio = {ratio:.4f}  -> Heegner index m with m^2 = "
          f"{round(ratio)} (integer landing, margin {abs(ratio - round(ratio)):.1e})")
        P()
        P("VERDICT:")
        P("  The converse leg CLOSES at grade one on house instruments: point")
        P("  counts built the modular clock, the CM alignment named the Heegner")
        P("  point, the parametrization CONSTRUCTED a point, the recognition gate")
        P("  landed it in Q exactly, and its height is an integer multiple-squared")
        P("  of the regulator -- the fired jet L'(37a1,1) = 0.306 realized as an")
        P("  actual cycle (Gross-Zagier).  This is the operational template of the")
        P("  recognition problem the terminus needs at every grade: detection")
        P("  (jet fires) -> alignment (CM clock) -> construction (parametrization)")
        P("  -> recognition (exact landing).  At grade >= 2 the missing piece is")
        P("  the parametrization's analogue -- the Kudla-shaped arm.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "heegner_recognition_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to heegner_recognition_results.txt]")


if __name__ == "__main__":
    main()
