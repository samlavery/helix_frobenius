"""
helix_phasor_tool.py — reference implementation of the double-ended helix phasor tool.

Faithful Python companion to:
  • the paper  "The Double-Ended Helix: A Three-Dimensional Geometric Tool for the
    Vanishing Points of Dirichlet L-Functions"  (S. Lavery, 2026; paper/helix_phasor_model.tex)
  • the Lean 4 / Mathlib formalization (RequestProject): ClosedForm.lean, HelixLogFreeFTA.lean,
    HelixCollapseReality.lean, LFunctionPhasor.lean, GeometricProjectionHolds.lean, Faithfulness.lean

FAITHFULNESS NOTE (read this).
  • The *definitions* below are direct transcriptions of the Lean source; each carries its Lean
    identifier (file:line), and each is checked numerically in the demo.
  • The *strip extension* (accumulation onto the critical line) is computed by ABEL SUMMATION —
    summation by parts on the bounded character partial sums B_n — which is exactly the method of
    the paper (Thm 5.1/5.2 proof) and of the Lean proofs `dirichlet_strip_tendsto_LFunction` /
    `eta_strip_tendsto`.  There is NO ad-hoc taper.
  • The *vanishing-point finder* is a NUMERICAL DEMONSTRATION, not a theorem: the theorems
    (`continuous_model_zeta`, Thm 5.3) state that the fiber's limit vanishes iff ζ(½+iy)=0; the
    local-minimum detection here is only a convenience for locating those y.
  • No mpmath and no zeta routine of any kind: the fiber is computed only from its own phasor
    terms.  The only external numbers are a literal table of PUBLISHED reference zeros, used solely
    for the final |diff| comparison — they never enter the fiber, the carrier, or the finder.

This is a TOOL.  It makes no claim beyond locating the vanishing points.
"""

import cmath
import math
import numpy as np

PI = math.pi
DELTA = PI / 3.0                      # Sec 2.2: fixed integer spacing Delta = pi/3 (Geometry.Delta)


# ============================================================================
# Section 2 — the pi/3 helix carrier      (ClosedForm.lean : CriticalLinePhasor.Geometry)
# ============================================================================

def helix(p, r, k):
    """Geometry.helix (Def 2.1): gamma(k) = (r k cos 2pi k, r k sin 2pi k, p k)."""
    return (r * k * math.cos(2 * PI * k), r * k * math.sin(2 * PI * k), p * k)

def speed(p, r, k):
    """Geometry.speed (Def 2.1): ||gamma'(k)|| = sqrt(p^2 + r^2 + (2 pi r k)^2)."""
    return math.sqrt(p * p + r * r + (2 * PI * r * k) ** 2)

def arclength(p, r, k):
    """Geometry.arclengthClosed (Thm 2.3): closed-form S(k;p,r); S(k;p,0)=p k."""
    if r == 0:
        return p * k
    root = math.sqrt(p * p + r * r + 4 * PI * PI * r * r * k * k)
    return k / 2 * root + (p * p + r * r) / (4 * PI * r) * math.asinh(
        2 * PI * r * k / math.sqrt(p * p + r * r))

def k_climb(p, y):
    """Geometry.kClimb (Def 2.1): k(y) = e^y / p  (height z = e^y, radius R = (r/p) e^y)."""
    return math.exp(y) / p

def Nindex(p, r, y):
    """Geometry.Nindex (Def 2.4): N(y) = S(k(y);p,r)/Delta = (3/pi) S."""
    return arclength(p, r, k_climb(p, y)) / DELTA

def spin_angle(n):
    """Geometry.spinAngle (Def 2.4): integer angular coordinate s_n = n*(pi/3)."""
    return n * DELTA


# ============================================================================
# Section 3 — the log-free FTA winding and the bridge      (HelixLogFreeFTA.lean)
# ============================================================================

def _factorization(n):
    """Nat.factorization: prime -> exponent map of n >= 1."""
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def wind_angle(n, theta):
    """HelixLogFree.windAngle (Def 3.1): Theta(n) = sum_{p^e || n} e*theta(p) — completely additive."""
    return sum(e * theta(p) for p, e in _factorization(n).items())

def wind(n, theta):
    """HelixLogFree.wind (Def 3.1): wind(n) = exp(i Theta(n)) on the unit circle."""
    return cmath.exp(1j * wind_angle(n, theta))

def helix_pt(n, theta):
    """HelixLogFree.helixPt / norm_helixPt (Def 3.1, Thm 2.6): sqrt(n) wind(n); ||.|| = sqrt(n)."""
    return math.sqrt(n) * wind(n, theta)

def bridge_theta(gamma):
    """Faithful.wind_glog_eq_cpow (Thm 3.4): theta(p)=gamma*log p  =>  wind(n) = n^{i gamma}."""
    return lambda p: gamma * math.log(p)


# ============================================================================
# Section 4 — the phasor fiber          (LFunctionPhasor.lean : spin, phasorTerm)
# ============================================================================

def spin(y, n):
    """LFunctionPhasor.spin (Def 4.2, line 38): spin(y,n) = exp(-(y log n) i), unit modulus."""
    return cmath.exp(-(y * math.log(n)) * 1j)

def phasor(chi, n, sigma, y):
    """LFunctionPhasor.phasorTerm (line 42): chi(n) * n^{-sigma} * spin(y,n) = chi(n) n^{-s}."""
    if n == 0:
        return 0j
    return chi(n) * (n ** (-sigma)) * spin(y, n)

def finite_carrier(chi, N, s):
    """DirichletPhasorCarrier.finiteCarrier / fiber_accumulates_to_L (Def 4.4, Thm 4.5):
    raw partial sum  sum_{n<N} chi(n) n^{-s}  ->  L(s,chi)  for Re s > 1."""
    return sum(chi(n) * complex(n) ** (-s) for n in range(1, N))


# ---- Dirichlet characters: the only dial (Sec 8 — one carrier, all chi; faithful_all_L) ----

def chi_trivial(n):                  # zeta channel
    return 1.0

def chi_mod3(n):                     # real character mod 3 — the +/- (split/inert) channels
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def eta_coeff(n):                    # alternating weight (-1)^{n+1}, the zeta channel's strip regulator
    return 1.0 if (n % 2 == 1) else -1.0


# ============================================================================
# Section 5 — strip extension by ABEL SUMMATION  (the paper's & Lean's method)
#   eta_strip_tendsto (line 1098), dirichlet_strip_tendsto_LFunction (line 647),
#   continuous_model_zeta (Faithfulness.lean:256)
# ============================================================================

def _partial_char_sums(coeff, M):
    """B_n = sum_{k=1}^{n} coeff(k) — the bounded character partial sums (Abel's B_N).
    Returns array with B[n-1] = B_n for n=1..M."""
    B = np.empty(M)
    acc = 0.0
    for k in range(1, M + 1):
        acc += coeff(k)
        B[k - 1] = acc
    return B

def abel_fiber(coeff, s, M=8000):
    """Strip extension via Abel summation (summation by parts), the method of Thm 5.1/5.2 and of
    `dirichlet_strip_tendsto_LFunction` / `eta_strip_tendsto`:

        sum_{n<N} coeff(n) n^{-s}  =  sum_n B_n (n^{-s} - (n+1)^{-s})   (boundary -> 0, Re s > 0)

    With coeff = eta_coeff this -> (1 - 2^{1-s}) zeta(s); with coeff = chi (chi != 1) -> L(s,chi).
    Truncated at M terms.  No taper.
    """
    B = _partial_char_sums(coeff, M)
    n = np.arange(1, M + 1, dtype=complex)
    return complex(np.sum(B * (n ** (-s) - (n + 1) ** (-s))))


# ---- vanishing points on the critical line (NUMERICAL DEMO of continuous_model_zeta) ----

def _vanishing_sweep(coeff, ys, M=8000, sigma=0.5):
    """|abel_fiber(sigma + i y)| over an array of ordinates ys, vectorized (chunked)."""
    B = _partial_char_sums(coeff, M)
    n = np.arange(1, M + 1, dtype=float)
    amp = np.concatenate([B * n ** (-sigma), -B * (n + 1) ** (-sigma)]).astype(complex)
    logp = np.concatenate([np.log(n), np.log(n + 1)])
    out = np.empty(len(ys))
    for i in range(0, len(ys), 200):
        Mx = np.exp(-1j * np.outer(ys[i:i + 200], logp))
        out[i:i + 200] = np.abs(Mx @ amp)
    return out

def vanishing_points(coeff, y_max=52.0, samples=6000, M=8000, thresh=0.3):
    """NUMERICAL DEMONSTRATION (not a theorem).  `continuous_model_zeta` (Thm 5.3) proves the
    Abel-summed fiber's limit vanishes iff ζ(½+iy)=0 (resp. L(½+iy,χ)=0); this scans the line and
    returns the local minima of |fiber| — the located vanishing points.  The minimum-detection is a
    demo convenience for finding the y, not part of any theorem."""
    ys = np.linspace(1.0, y_max, samples)
    mags = _vanishing_sweep(coeff, ys, M)
    base = float(np.median(mags))
    return [float(ys[i]) for i in range(1, len(ys) - 1)
            if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < thresh * base]


# ============================================================================
# Section 7 — the readout projection                  (GeometricProjectionHolds.lean)
# ============================================================================

def to_circle_angle(t):
    """HarmonicProjection.toCircleAngle: Cayley map t -> 2 arctan t in (-pi, pi)."""
    return 2 * math.atan(t)

def to_line(theta):
    """HarmonicProjection.toLine: affine rescale theta -> (theta + pi)/(2 pi) in (0,1)."""
    return (theta + PI) / (2 * PI)

def projection(t):
    """HarmonicProjection.projection = toLine o toCircleAngle  (3D harmonic value -> 1D coord)."""
    return to_line(to_circle_angle(t))


# ============================================================================
# Section 10 — the Frobenius conjugate-eigenstate determinant identity
# ============================================================================

def frobenius_conjugate_det(y, n):
    """Faithful.frobenius_conjugate_det_one (Thm 10.1, Faithfulness.lean:335):
    det !![spin y n, 0; 0, conj(spin y n)] = z conj z = |z|^2 = 1, z = spin(y,n).
    (Transverse phase block; the radial sqrt(p) of the similitude is carried separately.)"""
    z = spin(y, n)
    return np.linalg.det(np.array([[z, 0], [0, np.conjugate(z)]], dtype=complex))


# ============================================================================
# Published reference values — for the final |diff| comparison ONLY.
#   Well-known published constants (imaginary parts of the nontrivial zeros): the literature's
#   ground truth, obtained independently of this tool.  They do NOT enter the fiber, carrier, or
#   finder — they replace any call to an external zeta routine (e.g. mpmath).
# ============================================================================

ZETA2 = PI * PI / 6.0                 # zeta(2), closed form

# imaginary parts of the first nontrivial zeros of zeta (published reference)
ZETA_ZEROS = [
    14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
    37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
    52.970321478, 56.446247697, 59.347044003, 60.831778525, 65.112544048,
]

# imaginary parts of the first zeros of L(s, chi_3) (published reference, approx)
CHI3_ZEROS = [8.04, 11.25, 15.70, 18.26, 20.46, 24.06, 26.58, 28.22]


# ============================================================================
# Demo
# ============================================================================

def _demo():
    line = "=" * 80
    print(line)
    print("THE DOUBLE-ENDED HELIX PHASOR TOOL — reference implementation (faithful to paper + Lean)")
    print("  builds the carrier, rides the fiber, finds the vanishing points.  (no RH claim)")
    print(line)
    p = r = 1.0

    print("\n[Sec 2] carrier: integer angle s_n = n*pi/3 is 6-periodic (Eisenstein mu_6)")
    for n in range(7):
        print(f"   n={n}:  s_n mod 2pi = {spin_angle(n) % (2 * PI):8.4f}")
    print(f"   carrier_spacing: s_(n+1)-s_n = {spin_angle(5) - spin_angle(4):.6f}  (= pi/3 = {DELTA:.6f})")
    print(f"   norm_helixPt(9) = {abs(helix_pt(9, bridge_theta(1.0))):.4f}  (= sqrt 9 = 3, emergent)")

    print("\n[Sec 3] HelixLogFree winding is a multiplicative character (wind_mul):")
    th = bridge_theta(1.0)
    for (m, n) in [(6, 35), (4, 9), (12, 25)]:
        print(f"   |wind({m}*{n}) - wind({m})wind({n})| = {abs(wind(m * n, th) - wind(m, th) * wind(n, th)):.2e}")
    print("   bridge (wind_glog_eq_cpow):  wind(n) = n^{i gamma}:")
    for n in [2, 7, 30]:
        print(f"   n={n:>2}: |wind(n) - n^(i)| = {abs(wind(n, bridge_theta(1.0)) - complex(n) ** 1j):.2e}")

    print("\n[Sec 4] raw partial sums accumulate to L on Re s>1 (fiber_accumulates_to_L):")
    g = finite_carrier(chi_trivial, 8000, 2.0)
    print(f"   sum_{{n<N}} n^-2 = {g.real:.6f}   reference zeta(2)=pi^2/6 = {ZETA2:.6f}")

    print("\n[Sec 5] strip extension by ABEL SUMMATION; vanishing points vs zeta zeros")
    print("        (continuous_model_zeta: eta-fiber -> 0  iff  zeta(1/2+iy)=0)")
    vps = vanishing_points(eta_coeff, y_max=52, samples=6000, M=8000)
    print(f"   {'k':>2} {'vanishing point':>16} {'published zero':>16} {'|diff|':>9}")
    for k, v in enumerate(vps[:12], 1):
        z = min(ZETA_ZEROS, key=lambda t: abs(t - v))
        print(f"   {k:>2} {v:>16.4f} {z:>16.4f} {abs(v - z):>9.4f}")

    print("\n[Sec 8] same carrier, chi_3 (mod 3): vanishing points = zeros of L(s, chi_3) (faithful_all_L)")
    vps3 = vanishing_points(chi_mod3, y_max=30, samples=5000, M=8000)
    print(f"   vanishing points:    {[round(v, 3) for v in vps3[:8]]}")
    print(f"   published reference: {CHI3_ZEROS}")

    print("\n[Sec 9] both_helices_conjugate: left strand = conj(right strand) (exact, every N)")
    yv = 14.0
    right = sum(eta_coeff(n) * complex(n) ** (-(0.5 + 1j * yv)) for n in range(1, 300))
    left = sum(eta_coeff(n) * complex(n) ** (-(0.5 - 1j * yv)) for n in range(1, 300))
    print(f"   |left - conj(right)| = {abs(left - np.conjugate(right)):.2e}")

    print("\n[Sec 10] frobenius_conjugate_det_one: det diag(z, conj z) = |z|^2 = 1")
    for (y, n) in [(14.13, 2), (21.02, 7), (3.0, 30)]:
        d = frobenius_conjugate_det(y, n)
        print(f"   y={y:>6.2f} n={n:>2}:  det = {d.real:.6f} {d.imag:+.1e}i")

    print("\n[Sec 7] readout projection (projection_midline):")
    print(f"   projection(0) = {projection(0):.4f}  (midpoint of [0,1]: the gauge centre)")

    print("\n" + line)
    print("Definitions faithful to the Lean source; strip by Abel summation (paper's method);")
    print("vanishing-point finder is a numerical demo of continuous_model_zeta.  No RH claim.")
    print(line)


if __name__ == "__main__":
    _demo()
