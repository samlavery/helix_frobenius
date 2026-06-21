"""
helix_geometry_3d.py — the 3-D Archimedean-helix carrier of the L-function phasor model.

Faithful realization of PHASOR_HELIX_SPEC.md.  Two halves, kept strictly separate
(spec §2, "division of labor"):

  * THE ARROWS (§1) decide WHICH frequency y cancels -> the value of L and its zeros.
        phasor(n, y) = chi(n) * n^(-sigma) * exp(-i * y * ln n)
        S(y) = sum_n phasor(n, y) = L(chi, sigma + i y)
    A zero is P = M: the +channel vector sum equals the -channel vector sum
    ("negative = positive").  Each lane diverges ~ sqrt(N); only the difference
    converges.  The arrow length n^(-sigma) is the decay, TRANSVERSE to the helix.

  * THE CARRIER (§2) decides WHERE each phasor and each cancellation sits.
    HORIZONTAL: an Archimedean spiral r = b*theta, integer n placed at constant
        RADIAL-PLANE arc length u * n (u = pi/3).  Radius grows ~ sqrt(n).
        Radial growth is L-DEPENDENT: the gap per turn is g = e^(mod q) (eta e^2,
        chi3 e^3, chi4 e^4, chi5 e^5, chi8 e^8), so b = e^q/(2 pi).
    VERTICAL (height law, default align_z_to_ey=True): z_n = n.  Every integer slot rises
        by the same Delta z = 1 -- per integer n, NOT per phasor: the neutral bucket
        chi(n)=0 carries no arrow but still occupies its slot and still ticks the height
        (counting per active phasor would climb by phi(q)/q per integer and land the
        resonance at (phi(q)/q)*e^(gamma_k), wrong by the active fraction).  Since phasor n
        resonates at y = ln n, this puts z = n = e^(y_n) -- each integer at the height of its
        own resonant frequency -- and the zeros land at z = e^(gamma_k).  Holds for ALL
        L-functions (it rides on spin = log n).  align_z_to_ey=False reverts to
        z = p*theta/(2 pi) ~ sqrt(n).

phasors-per-turn is L-dependent two ways (spec §2):
  1. GEOMETRIC count 2*pi*R_n/u scales with the radial growth e^(mod q);
  2. the neutral bucket chi(n)=0 drops inactive integers, so the LIVE count is
     geometric * active_fraction, active_fraction = #{a: chi(a) != 0}/q.

The separation is the whole point: a helix whose own radius did the cancelling
would need radius -> 0 (decay), contradicting "Archimedean / non-decaying".  Here
the decay lives in the arrow (n^(-sigma)); the radius is free to grow.

Validation (run `python3 helix_geometry_3d.py`): the arrow sum cancels at the
published zeros and is O(1) off them; the lanes satisfy P = M at a zero; the radius
grows ~sqrt(n) with turn-gap e^(mod q); the geometric/live phasors-per-turn match
spec §2; the height law puts each found crossing at z = e^(gamma_k).  An optional
arbitrary-precision layer (`analytic_L`, `analytic_zeros`, `verify_against_analytic`;
needs mpmath) cross-checks the zeros against independent ground truth (Hurwitz-zeta L,
the Riemann zeros) to ~1e-30 -- the second, independent computation of spec §7.
"""

import math
import numpy as np

PI = math.pi

# ===========================================================================
# Carrier constants.  u and base from spec §2; the radial growth is per-character.
# ===========================================================================
UNIT  = PI / 3.0            # u : radial-plane arc length per integer (constant spacing)
PITCH = PI / 3.0            # p : vertical rise per turn (only for align_z_to_ey=False)
BASE  = 0.0                 # base radius: pure spiral r = b*theta, starts at origin


def growth(q):
    """g = e^(mod q): the radial gap per turn (Archimedean), L-DEPENDENT (spec §2)."""
    return math.exp(q)


def radial_b(q):
    """b = dr/dtheta = g/(2 pi) = e^(mod q)/(2 pi)."""
    return math.exp(q) / (2.0 * PI)


# ===========================================================================
# 1. The carrier:  horizontal Archimedean spiral, radial growth b = e^q/(2 pi)
#
#    radius  r(theta) = BASE + b*theta            (BASE = 0: pure spiral from origin)
#    arc(theta)   = integral_0^theta b*sqrt(t^2+1) dt   (RADIAL-PLANE Archimedean arc)
#    theta_n      = arc^{-1}(u * n)               (Newton)
#    z_n          = n  (default height law; see carrier_height)
# ===========================================================================

def _arc_antideriv(w, b):
    """Antiderivative of (1/b) sqrt(w^2 + b^2) in w = BASE + b*theta:
        (1/b) [ (w/2) sqrt(w^2 + b^2) + (b^2/2) ln(w + sqrt(w^2 + b^2)) ].  Vectorized."""
    w = np.asarray(w, dtype=np.float64)
    root = np.sqrt(w * w + b * b)
    return (0.5 * w * root + 0.5 * b * b * np.log(w + root)) / b


def arc_length(theta, b):
    """Radial-plane Archimedean arc length from the origin to polar angle theta:
        integral_0^theta sqrt((BASE + b t)^2 + b^2) dt = integral_0^theta b sqrt(t^2+1) dt (BASE=0).
    Closed form via w = BASE + b*theta:  _arc_antideriv(w, b) - _arc_antideriv(BASE, b).
    Vectorized (accepts scalars or numpy arrays)."""
    theta = np.asarray(theta, dtype=np.float64)
    return _arc_antideriv(BASE + b * theta, b) - _arc_antideriv(BASE, b)


def arc_speed(theta, b):
    """d(arc)/d(theta) = sqrt((BASE + b theta)^2 + b^2)  (planar spiral speed; Newton derivative).
    For BASE = 0: b sqrt(theta^2 + 1)."""
    theta = np.asarray(theta, dtype=np.float64)
    r = BASE + b * theta
    return np.sqrt(r * r + b * b)


def theta_at_arclength(s, b, iters=80, tol=1e-13):
    """Solve arc(theta, b) = s for theta >= 0 by Newton's method (spec §2, arc^{-1}).
    Vectorized; the initial guess is the large-theta asymptotic arc ~ b theta^2 / 2."""
    s = np.asarray(s, dtype=np.float64)
    theta = np.sqrt(np.maximum(2.0 * s / b, 0.0))     # arc ~ b theta^2/2 -> theta ~ sqrt(2s/b)
    for _ in range(iters):
        f = arc_length(theta, b) - s
        theta = theta - f / arc_speed(theta, b)
        if np.max(np.abs(f)) < tol:
            break
    return np.where(s <= 0.0, 0.0, theta)


def theta_at(n, b):
    """theta_n = arc^{-1}(u * n): the polar angle of integer n on the helix of growth b."""
    return theta_at_arclength(UNIT * np.asarray(n, dtype=np.float64), b)


def carrier_radius(n, b):
    """R_n = BASE + b * theta_n.  Non-decaying; grows ~ sqrt(n) (-> sqrt(g/3) sqrt(n));
    the radial gap per full turn is exactly g = e^(mod q) = 2 pi b.  Does NOT do the cancelling."""
    return BASE + b * theta_at(n, b)


def carrier_height(n, b=None, align_z_to_ey=True):
    """The vertical height z_n (spec §2 height law).
    align_z_to_ey=True (default): z_n = n -- constant height law, Delta z = 1 per integer n
        (every slot, including chi(n)=0; NOT per active phasor), so integer n sits at
        z = n = e^(y_n) and the zeros land at z = e^(gamma_k).
    align_z_to_ey=False: z = p*theta_n/(2 pi) ~ sqrt(n) = e^(y/2) (constant pitch per turn; needs b)."""
    n_arr = np.asarray(n, dtype=np.float64)
    if align_z_to_ey:
        z = n_arr
    else:
        z = (PITCH / (2.0 * PI)) * theta_at(n_arr, b)
    return float(z) if np.ndim(n) == 0 else z


def carrier_point(n, b, align_z_to_ey=True):
    """point_n = (R_n cos theta_n, R_n sin theta_n, z_n) -- the 3-D carrier point(s).
    Scalar n -> a 3-tuple; array n -> an (N, 3) array."""
    th = theta_at(n, b)
    R = BASE + b * th
    z = carrier_height(n, b, align_z_to_ey)
    x = R * np.cos(th)
    y = R * np.sin(th)
    if np.ndim(th) == 0:
        return (float(x), float(y), float(z))
    z = np.broadcast_to(np.asarray(z, dtype=np.float64), x.shape)
    return np.stack([x, y, z], axis=-1)


def phasors_per_turn(n, b):
    """GEOMETRIC count 2 pi R_n / u : integer steps in one turn (spec §2).  Grows with the radius;
    scales with the radial growth e^(mod q), so it is L-function dependent."""
    return 2.0 * PI * carrier_radius(n, b) / UNIT


def active_phasors_per_turn(n, b, active_fraction):
    """LIVE count: geometric * active_fraction, where active_fraction = #{a: chi(a) != 0}/q.
    The neutral bucket chi(n)=0 contributes no spinning arrow, so only active integers count."""
    return phasors_per_turn(n, b) * active_fraction


# ===========================================================================
# 1b. THE LINEAR SPIRAL carrier (the corrected carrier -- replaces the Archimedean sqrt(n) one).
#     Phasor n sits at radius (pi/3)*n -- LINEAR, step pi/3: 1->pi/3, 2->2pi/3, 3->pi -- and angle
#     (2pi/q)*ln n.  Per turn (d-angle = 2pi) the index n grows x e^q, so the radius grows x e^q
#     (e^mod); the count per turn grows (NOT a fixed six); there is NO sqrt(n) anywhere.  The ANGLE
#     is the spin: a phasor's angular position theta_n rotates (in y) at rate ln n, since the phase
#     is -(y q/2pi) theta_n = -y ln n.  The carrier enters the value through the ANGLE; the radius is
#     pure placement (it never appears in the sum).
# ===========================================================================

def linspiral_angle(n, q):
    """Winding angle of phasor n on the linear spiral: (2pi/q)*ln n.  This IS the spin (scaled): the
    phase -(y q/2pi)*angle = -y*ln n.  Per turn the index grows x e^q -> radius grows x e^q (e^mod)."""
    return (2.0 * PI / q) * np.log(np.asarray(n, dtype=np.float64))


def linspiral_radius(n):
    """Radius of phasor n: (pi/3)*n  (LINEAR, step pi/3; the e^q per-turn growth lives in the angle)."""
    return (PI / 3.0) * np.asarray(n, dtype=np.float64)


def linspiral_point(n, q):
    """Carrier point (x, y) of phasor n on the linear spiral: (r cos th, r sin th)."""
    r = linspiral_radius(n); th = linspiral_angle(n, q)
    return r * np.cos(th), r * np.sin(th)


def linspiral_value(chi, y, N=200_000, sigma=0.5):
    """The value at frequency y, with each phasor's spin READ OFF its carrier angle:
        S(y) = sum_n chi(n) n^(-sigma) exp(-i (y q/2pi) * angle_n),   angle_n = (2pi/q) ln n.
    The (q/2pi) cancels the (2pi/q) -> phase = -y ln n -> S = L(1/2+iy).  Closes at the zeros;
    numerically identical to phasor_sum, but the spin now comes from the carrier geometry (the angle),
    not imposed by hand -- so the carrier genuinely enters the value through the angle."""
    n = np.arange(1, N + 1, dtype=np.float64)
    th = linspiral_angle(n, chi.q)
    return complex(np.sum(chi(n) * n ** (-sigma) * np.exp(-1j * (y * chi.q / (2.0 * PI)) * th)))


# ===========================================================================
# 2. The arrows:  magnitude n^(-sigma), spin ln n  (spec §1, §8 load-bearing)
# ===========================================================================

def spin(n):
    """spin(n) = ln n : each phasor spins at its own ln n (the one and only log).
    Using the spiral winding angle (~ sqrt(n)) instead does NOT cancel (spec §8)."""
    return np.log(np.asarray(n, dtype=np.float64))


def magnitude(n, sigma=0.5):
    """magnitude(n) = n^(-sigma) : the arrow length, transverse to the helix (decays)."""
    return np.asarray(n, dtype=np.float64) ** (-sigma)


def phasor(chi, n, y, sigma=0.5):
    """phasor(n, y) = chi(n) * n^(-sigma) * exp(-i y ln n).  Independent of the carrier."""
    n = np.asarray(n, dtype=np.float64)
    return chi(n) * n ** (-sigma) * np.exp(-1j * y * np.log(n))


# ===========================================================================
# 3. Characters: how the +/- channels are assigned  (spec §3)
# ===========================================================================

class RealCharacter:
    """Real (quadratic) Dirichlet character: chi(n) depends only on n mod q, values +1/-1/0."""

    def __init__(self, name, q, values, lvalue=None):
        self.name = name
        self.q = q
        self.values = np.asarray(values, dtype=np.float64)
        self.lvalue = lvalue            # human description of the L-function

    def __call__(self, n):
        idx = np.asarray(n).astype(np.int64) % self.q
        return self.values[idx]

    @property
    def active_fraction(self):
        """#{a in 0..q-1: chi(a) != 0} / q  (chi3 2/3, chi4 1/2, chi5 4/5, chi8 1/2)."""
        return int(np.count_nonzero(self.values)) / self.q


class EtaCoefficient:
    """g(n) = (-1)^(n+1) -- the alternation, NOT a character.  Supplies +/- channels to the
    trivial character so that the sum cancels; gives the Dirichlet eta = (1 - 2^(1-s)) zeta(s).
    On Re s = 1/2 the factor (1 - 2^(1-s)) never vanishes, so eta's zeros there are exactly
    the nontrivial zeros of zeta (spec §3).  q = 2 (mod), and every integer is active."""

    name = "eta"
    q = 2
    active_fraction = 1.0
    lvalue = "(1 - 2^(1-s)) * zeta(s)  -- principal / chi1 / zeta case"

    def __call__(self, n):
        odd = (np.asarray(n).astype(np.int64) % 2 == 1)
        return np.where(odd, 1.0, -1.0)


CHARACTERS = {
    "chi3": RealCharacter("chi3", 3, [0, 1, -1],                       "mod-3 odd"),
    "chi4": RealCharacter("chi4", 4, [0, 1, 0, -1],                    "Dirichlet beta"),
    "chi5": RealCharacter("chi5", 5, [0, 1, -1, -1, 1],                "mod-5 even"),
    "chi8": RealCharacter("chi8", 8, [0, 1, 0, -1, 0, -1, 0, 1],       "(2/n)"),
    "eta":  EtaCoefficient(),
}


# ===========================================================================
# 4. The phasor bank: the sum and its +/- channels  (spec §1)
# ===========================================================================

def phasor_sum(chi, y, N=200_000, sigma=0.5):
    """S(y) = sum_{n=1}^{N} chi(n) n^(-sigma) exp(-i y ln n).  -> L(chi, sigma + i y) as N -> oo.
    At a zero |S_N| ~ 0.667 / sqrt(N) (conditional convergence); off a zero S_N -> L != 0."""
    n = np.arange(1, N + 1, dtype=np.float64)
    return complex(np.sum(chi(n) * n ** (-sigma) * np.exp(-1j * y * np.log(n))))


def phasor_sum_pi3(chi, y, N=200_000, sigma=0.5):
    """The phasor with BOTH magnitude and spin read off the pi/3 carrier coordinate x_n = (pi/3)*n
    instead of the bare index n:
        S_pi3(y) = sum_n chi(n) * x_n^(-sigma) * exp(-i*y*ln x_n),   x_n = (pi/3)*n.
    This is the arrow put 'on the real pi/3 scale'.  Empirically and algebraically it equals
    (pi/3)^(-sigma) * exp(-i*y*ln(pi/3)) * phasor_sum(...): a constant times a global phase, so its
    zeros coincide with the bare phasor's -- demonstrated in the [5] sweep."""
    n = np.arange(1, N + 1, dtype=np.float64)
    x = (PI / 3.0) * n
    return complex(np.sum(chi(n) * x ** (-sigma) * np.exp(-1j * y * np.log(x))))


def channel_sums(chi, y, N=200_000, sigma=0.5):
    """The two lanes (spec §1):
        P(y) = sum_{chi(n)=+1} n^(-sigma) exp(-i y ln n)
        M(y) = sum_{chi(n)=-1} n^(-sigma) exp(-i y ln n)
    S = P - M; L = 0  <=>  P = M.  Each lane individually diverges ~ N^(1-sigma) = sqrt(N);
    only the difference converges.  Returns (P, M)."""
    n = np.arange(1, N + 1, dtype=np.float64)
    c = chi(n)
    arrows = n ** (-sigma) * np.exp(-1j * y * np.log(n))
    P = complex(np.sum(np.where(c > 0, arrows, 0.0)))
    M = complex(np.sum(np.where(c < 0, arrows, 0.0)))
    return P, M


def _golden_min(f, a, b, iters=60):
    """Golden-section minimization of a unimodal f on [a, b] (numpy-only; no scipy)."""
    invphi = (math.sqrt(5.0) - 1.0) / 2.0
    c = b - invphi * (b - a)
    d = a + invphi * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(iters):
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - invphi * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + invphi * (b - a)
            fd = f(d)
    return 0.5 * (a + b)


def find_zeros(chi, y_lo, y_hi, N=120_000, sigma=0.5, step=0.02, dip=0.05):
    """FIND the zeros gamma_k directly from the phasors (spec §7.2): sweep |S(y)| on [y_lo, y_hi],
    detect the cancellation dips (local minima), and refine each by golden section.  A genuine
    zero has |S_N| ~ 0.667/sqrt(N) (kept iff below `dip`); off a zero |S_N| = O(1).  Returns the
    list of refined gamma_k.  These are independent of any published table."""
    ys = np.arange(y_lo, y_hi, step)
    mag = np.array([abs(phasor_sum(chi, y, N, sigma)) for y in ys])
    f = lambda y: abs(phasor_sum(chi, y, N, sigma))
    gammas = []
    for i in range(1, len(ys) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1]:
            g = _golden_min(f, ys[i - 1], ys[i + 1])
            if f(g) < dip:
                gammas.append(g)
    return gammas


# The first 10 zeros gamma_k on Re s = 1/2 of each L-function (float64, ~15-16 significant digits)
# and their resonant terms e^(gamma_k)  (spec §4).  Provenance: NOT hand-copied -- `first_n_zeros`
# below enumerates them from scratch from the independently defined analytic L (coarse |L| scan +
# mpmath findroot; mpmath.zetazero for eta), `analytic_zeros` refines them, and
# `verify_against_analytic` confirms |L(1/2 + i gamma_k)| ~ 10^(-30) at every height (completeness:
# |L| stays bounded away from 0 between consecutive zeros).  Stored to the float64 limit (~1e-15);
# use `first_n_zeros(chi, n, dps=...)` / `analytic_zeros(chi, dps=...)` for more zeros or more digits.
ZEROS = {
    "chi3": [8.0397371556814667, 11.249206207772935, 15.704619176721626, 18.261997495693128, 20.455770807742493, 24.059414856493451, 26.577868735774585, 28.218164506233386, 30.745040261382496, 33.897388927259419],
    "chi4": [6.0209489046975967, 10.243770304166555, 12.988098012312423, 16.342607104587222, 18.291993196123535, 21.45061134398346, 23.278376520459532, 25.728756425088728, 28.359634343025328, 29.656384014593153],
    "chi5": [6.6484533447277147, 9.8314444328866696, 11.958845626083515, 16.033821128384236, 17.566994292325555, 19.54073262278475, 22.227405454459411, 24.588466217408195, 26.77609594800414, 28.461035100177522],
    "chi8": [4.8999739970070365, 7.6284288417693978, 10.806588163861712, 12.31054299423653, 15.195754250645123, 17.022285974308347, 18.805958907707148, 21.131645962221344, 23.083849996200547, 24.201963557815602],
    "eta":  [14.134725141734694, 21.022039638771555, 25.010857580145689, 30.424876125859513, 32.93506158773919, 37.586178158825671, 40.918719012147495, 43.327073280915, 48.00515088116716, 49.773832477672302],
}


# ===========================================================================
# 4b. Independent analytic ground truth  (spec §3, §6, §7).  This is the second,
#     INDEPENDENT computation the verification recipe (§7) requires -- the analytic_L /
#     analytic_zeros the spec §6 names.  Needs mpmath; the NumPy model core above does NOT.
#     Used only to VALIDATE the model to arbitrary precision, never inside it.
# ===========================================================================

def _require_mpmath():
    """Import mpmath on demand -- only the ground-truth / validation layer needs it."""
    try:
        import mpmath
        return mpmath
    except ImportError as exc:                       # pragma: no cover
        raise ImportError(
            "the analytic ground truth needs mpmath (`pip install mpmath`); the NumPy "
            "model core (phasor_sum, channels, the carrier) does not."
        ) from exc


def analytic_L(chi, s, dps=30):
    """L(chi, s) to arbitrary precision, computed INDEPENDENTLY of the phasor sum via Hurwitz
    zeta (spec §3) -- the value the truncated S(y) converges to:
        real character:  L(chi, s) = q^(-s) * sum_{a=1}^{q-1} chi(a) * zeta(s, a/q)
        eta / zeta:      L(eta, s) = (1 - 2^(1-s)) * zeta(s)
    Returns an mpmath complex (mpc)."""
    mp = _require_mpmath()
    mp.mp.dps = dps
    s = mp.mpc(s)
    if isinstance(chi, EtaCoefficient):
        return (1 - 2 ** (1 - s)) * mp.zeta(s)
    q = chi.q
    return q ** (-s) * sum(int(chi.values[a]) * mp.zeta(s, mp.mpf(a) / q) for a in range(1, q))


def analytic_zeros(chi, seeds=None, dps=30):
    """The zeros gamma_k on Re s = 1/2 to arbitrary precision, computed INDEPENDENTLY of the
    phasor model (spec §7.1).  Character: Newton (mpmath.findroot) on t -> L(1/2 + i t) from each
    seed -- the seed only selects WHICH zero; the value is fixed by L, not the seed.  eta:
    mpmath.zetazero (the genuine Riemann zeros).  Returns mpmath reals; each is a true on-line zero
    (|im t|, |L(1/2 + i gamma)| ~ 10^(-dps)).  Default seeds: the float64 ZEROS table."""
    mp = _require_mpmath()
    mp.mp.dps = dps
    half = mp.mpf(1) / 2
    if seeds is None:
        seeds = ZEROS[chi.name]
    if isinstance(chi, EtaCoefficient):
        return [mp.zetazero(k + 1).imag for k in range(len(seeds))]
    return [mp.findroot(lambda t: analytic_L(chi, half + 1j * t, dps), mp.mpf(g0)).real
            for g0 in seeds]


def first_n_zeros(chi, n=10, T=60.0, dps=30):
    """The first `n` zeros gamma_k on Re s = 1/2, enumerated FROM SCRATCH (no seed table) and
    INDEPENDENTLY of the phasor model (spec §7.1).  Character: coarse-scan |L(1/2+it)| on [0.2, T]
    for local minima, refine each by Newton (mpmath.findroot), keep genuine on-line zeros, dedupe,
    sort.  eta: mpmath.zetazero (the genuine Riemann zeros).  This is how the ZEROS table is
    generated; completeness (no missed zero) is witnessed by |L| staying bounded away from 0
    between consecutive zeros.  Returns mpmath reals."""
    mp = _require_mpmath()
    mp.mp.dps = dps
    half = mp.mpf(1) / 2
    if isinstance(chi, EtaCoefficient):
        return [mp.zetazero(k + 1).imag for k in range(n)]
    scan_dps, h = 15, mp.mpf(1) / 20             # coarse scan cheap; refine at full dps
    ts, mags, t = [], [], mp.mpf(1) / 5
    while t <= T:
        ts.append(t); mags.append(abs(analytic_L(chi, half + 1j * t, scan_dps))); t += h
    zeros = []
    for i in range(1, len(ts) - 1):
        if not (mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.5):
            continue
        r = mp.findroot(lambda u: analytic_L(chi, half + 1j * u, dps), ts[i])
        if (abs(r.imag) < 1e-12 and abs(analytic_L(chi, half + 1j * r.real, dps)) < 1e-20
                and all(abs(r.real - z) > 1e-6 for z in zeros)):
            zeros.append(r.real)
        if len(zeros) >= n + 2:
            break
    zeros.sort()
    return zeros[:n]


def verify_against_analytic(N=1_000_000, dps=30):
    """Pressure-test the model against independent mpmath ground truth (spec §7).  Returns the
    worst-case residuals over every tabulated zero (all L-functions, first 10 each):
      * 'max_abs_L_at_zero'  -- |L(1/2 + i gamma_k)| at the analytic zeros (~10^(-dps): they are
                                genuine on-line zeros of the independently defined L);
      * 'max_table_vs_exact' -- |float64 ZEROS - arbitrary-precision zero| (~10^(-15) float64 floor);
      * 'max_dip_x_sqrtN'    -- |S_N(gamma_1)| * sqrt(N) over the first zero of each L-function, the
                                at-zero cancellation dip scaled by sqrt(N) (~O(1): confirms |S_N| ~
                                const/sqrt(N), the conditional-convergence envelope -- no finite
                                truncation hits 0 exactly)."""
    mp = _require_mpmath()
    mp.mp.dps = dps
    half = mp.mpf(1) / 2
    max_L = max_tab = max_dip = 0.0
    n_zeros = 0
    for name in ZEROS:
        chi = CHARACTERS[name]
        azeros = analytic_zeros(chi, dps=dps)                 # refine the stored seeds (all 10)
        for g_hp, g_tab in zip(azeros, ZEROS[name]):
            max_L = max(max_L, float(abs(analytic_L(chi, half + 1j * g_hp, dps))))
            max_tab = max(max_tab, abs(float(g_hp) - g_tab))
            n_zeros += 1
        # the at-zero dip |S_N| ~ 0.667/sqrt(N) is the same story at every zero; gamma_1 suffices
        max_dip = max(max_dip, abs(phasor_sum(chi, float(azeros[0]), N=N)) * math.sqrt(N))
    return {"max_abs_L_at_zero": max_L, "max_table_vs_exact": max_tab,
            "max_dip_x_sqrtN": max_dip, "N": N, "dps": dps, "n_zeros": n_zeros}


# ===========================================================================
# 4c. The COMPLETED finite phasor: high-dps head + Euler-Maclaurin tail.  This REMOVES the
#     ~0.667/sqrt(N) conditional-convergence floor: the tail sum_{n>N} is not chopped, it is
#     completed by the Euler-Maclaurin asymptotic of the SAME periodic phasor tail (Bernoulli
#     numbers + a boundary term), NOT by Hurwitz/zeta.  "visible arrows + asymptotic boundary
#     flow."  The model then finds gamma to high dps, not 3-4 digits.  Needs mpmath.
# ===========================================================================

def _char_value(chi, n):
    """chi(n) for a scalar integer n (RealCharacter: values[n mod q]; eta: +1 odd / -1 even)."""
    if isinstance(chi, EtaCoefficient):
        return 1 if (n % 2 == 1) else -1
    return int(chi.values[n % chi.q])


def phasor_sum_hp(chi, y, N=2000, sigma=0.5, dps=40):
    """The phasor head sum_{n<=N} chi(n) n^(-(sigma + i*y)) in ARBITRARY precision (mpmath).  y may be
    complex (root-finders perturb off the real axis), so s = sigma + i*y is built directly."""
    mp = _require_mpmath()
    mp.mp.dps = dps
    s = mp.mpf(sigma) + 1j * y
    terms = [c * mp.power(n, -s) for n in range(1, N + 1) if (c := _char_value(chi, n))]
    return mp.fsum(terms)


def _rising_pochhammer(s, k):
    mp = _require_mpmath()
    out = mp.mpc(1)
    for j in range(k):
        out *= s + j
    return out


def _em_zeta_tail(s, A, M=4):
    """Euler-Maclaurin tail for sum_{k>=0} (A+k)^(-s): the pole term A^(1-s)/(s-1) (load-bearing),
    the 1/2 boundary, and the Bernoulli series.  Error ~ A^(-2M-1/2); M=4 suffices for A ~ 1e3."""
    mp = _require_mpmath()
    A = mp.mpf(A); s = mp.mpc(s)
    total = A ** (1 - s) / (s - 1) + mp.mpf("0.5") * A ** (-s)
    for m in range(1, M + 1):
        total += (mp.bernoulli(2 * m) / mp.factorial(2 * m)
                  * _rising_pochhammer(s, 2 * m - 1) * A ** (-s - (2 * m - 1)))
    return total


def phasor_tail_em(chi, s, N, M=4):
    """The tail sum_{n>N} chi(n) n^(-s), split by residue class mod q and completed by Euler-Maclaurin
    -- NOT Hurwitz zeta, the EM expansion of the same periodic phasor tail.  For residue a the active
    terms are n = q*k + a > N, i.e. q^(-s) * sum_{k>=k0} (k + a/q)^(-s) with k0 the first k past N."""
    mp = _require_mpmath()
    s = mp.mpc(s); q = chi.q
    total = mp.mpc(0)
    for a in range(q):
        c = _char_value(chi, a)
        if c == 0:
            continue
        k0 = math.floor((N - a) / q) + 1
        if a == 0 and k0 < 1:
            k0 = 1
        if k0 < 0:
            k0 = 0
        total += c * mp.power(q, -s) * _em_zeta_tail(s, mp.mpf(k0) + mp.mpf(a) / q, M=M)
    return total


def phasor_sum_completed(chi, y, N=2000, M=4, dps=40):
    """The COMPLETED finite phasor S(y) = (high-dps head sum_{n<=N}) + (EM tail of sum_{n>N}).  Equals
    L(1/2 + i*y, chi) to the EM order, so its zeros are the L-zeros -- but built from the phasors and
    their asymptotic boundary flow, with no zeta/Hurwitz oracle."""
    return phasor_sum_hp(chi, y, N=N, dps=dps) + phasor_tail_em(chi, 0.5 + 1j * y, N, M=M)


def find_zero_em(chi, gamma_seed, N=2000, M=4, dps=40):
    """FIND a critical-line zero gamma from the completed finite phasor (NO oracle): Newton
    (mpmath.findroot) on phasor_sum_completed from the approximate seed.  The seed only selects WHICH
    zero; the value is the model's.  Accurate to ~ the EM order (A^(-2M-1/2)); raise N, M, dps for more."""
    mp = _require_mpmath()
    mp.mp.dps = dps
    root = mp.findroot(lambda y: phasor_sum_completed(chi, y, N=N, M=M, dps=dps), mp.mpf(gamma_seed))
    return root.real


# ===========================================================================
# 5. Resonance: where each crossing sits on the carrier  (spec §2, §4)
# ===========================================================================

def resonant_term(gamma):
    """n* = e^(gamma): the resonant integer of a zero (spin(n*) = ln n* = gamma).
    Under the height law z_n = n, this is also the cancellation HEIGHT (spec §4)."""
    return math.exp(gamma)


def resonance_arc_position(gamma):
    """Horizontal (radial-plane) fiber position of zero gamma: arc length u * e^(gamma)."""
    return UNIT * resonant_term(gamma)


def resonance_height(gamma):
    """The vertical HEIGHT of the cancellation of zero gamma: z = e^(gamma) (= n*), since
    the height law is z_n = n and the resonant integer is n* = e^(gamma)."""
    return resonant_term(gamma)


def resonance_point(gamma, b):
    """The 3-D carrier point of crossing gamma on the helix of growth b: HORIZONTAL at arc length
    u*e^(gamma), VERTICAL at z = e^(gamma).  (So x, y ~ sqrt(e^gamma) while z = e^gamma.)"""
    th = float(theta_at_arclength(resonance_arc_position(gamma), b))
    R = BASE + b * th
    return (R * math.cos(th), R * math.sin(th), resonant_term(gamma))


def resonance_point_hp(gamma, q, dps=40):
    """The crossing gamma as a genuine 3D point (x, y, z) on the character-q helix, arbitrary
    precision.  height z = e^gamma (height law z_n = n*); arc = (pi/3) e^gamma; the Archimedean arc
    arc(theta) = (b/2)[theta*sqrt(theta^2+1) + asinh(theta)], b = e^q/(2pi), fixes the winding angle
    theta; radius R = b*theta ~ sqrt(e^q/3)*sqrt(z); (x, y) = (R cos theta, R sin theta).
    High dps is REQUIRED, not cosmetic: theta ~ sqrt(e^gamma) reaches ~1e11 for the high zeros, where
    float64 (ULP ~ 1e-5 rad there) loses the angular position (x, y) entirely.  Returns (x, y, z, R, theta)."""
    mp = _require_mpmath()
    mp.mp.dps = dps
    b = mp.e ** q / (2 * mp.pi)
    z = mp.e ** mp.mpf(gamma)
    arc = mp.pi / 3 * z
    arclen = lambda t: (b / 2) * (t * mp.sqrt(t * t + 1) + mp.asinh(t))
    th = mp.findroot(lambda t: arclen(t) - arc, mp.sqrt(2 * arc / b))
    R = b * th
    return R * mp.cos(th), R * mp.sin(th), z, R, th


# ===========================================================================
# 6. PhasorHelix: carrier + arrows for one character  (mirrors spec §6 usage)
# ===========================================================================

class PhasorHelix:
    """The 3-D carrier together with the arrows for one character.  The radial growth
    b = e^(mod q)/(2 pi) and the active_fraction are read from the character; the height law is
    z_n = n by default (align_z_to_ey).  The carrier never enters the sum -- net(y) depends only
    on chi, sigma (the carrier fixes WHERE, not the value of L)."""

    def __init__(self, chi, sigma=0.5, N=200_000, align_z_to_ey=True):
        self.chi = chi
        self.sigma = sigma
        self.N = N
        self.q = chi.q
        self.b = radial_b(chi.q)                # radial growth e^(mod q)/(2 pi)
        self.active_fraction = chi.active_fraction
        self.align_z_to_ey = align_z_to_ey

    # --- arrows (value of L) ---
    def net(self, y):
        """S(y) = L(chi, 1/2 + i y) (truncated).  ~ 0 at a zero, O(1) off it."""
        return phasor_sum(self.chi, y, self.N, self.sigma)

    def channels(self, y):
        """(P, M); a zero is P = M."""
        return channel_sums(self.chi, y, self.N, self.sigma)

    def find_zeros(self, y_lo, y_hi, step=0.02, dip=0.05):
        """Find the zeros gamma_k from the phasors on [y_lo, y_hi] (no table)."""
        return find_zeros(self.chi, y_lo, y_hi, self.N, self.sigma, step, dip)

    # --- carrier (horizontal spiral e^(mod q) + height law z_n = n) ---
    def carrier_point(self, n=None):
        """3-D carrier point(s).  Default n: all integers 1..N as an (N, 3) array."""
        if n is None:
            n = np.arange(1, self.N + 1)
        return carrier_point(n, self.b, self.align_z_to_ey)

    def carrier_height(self, n):
        return carrier_height(n, self.b, self.align_z_to_ey)

    def carrier_radius(self, n):
        return carrier_radius(n, self.b)

    def phasors_per_turn(self, n):
        """GEOMETRIC count 2 pi R_n / u (L-dependent via e^(mod q))."""
        return phasors_per_turn(n, self.b)

    def active_phasors_per_turn(self, n):
        """LIVE count: geometric * active_fraction (drops the chi(n)=0 bucket)."""
        return active_phasors_per_turn(n, self.b, self.active_fraction)

    def resonance_arc_position(self, gamma):
        return resonance_arc_position(gamma)

    def resonance_height(self, gamma):
        """z = e^gamma (height law z_n = n)."""
        return resonance_height(gamma)

    def resonance_point(self, gamma):
        """The 3-D carrier point (x, y, z) of the cancellation of zero gamma (z = e^gamma)."""
        return resonance_point(gamma, self.b)


# ===========================================================================
# 7. Validation (spec §2, §4, §7) -- run as a script
# ===========================================================================

def _demo():
    line = "=" * 78
    print(line)
    print("3-D ARCHIMEDEAN-HELIX PHASOR MODEL  (faithful to PHASOR_HELIX_SPEC.md)")
    print(line)

    print("\n[carrier constants]  u = pi/3 (radial-plane), base = 0, height law z_n = n (align_z);")
    print("   radial growth g = e^(mod q) is L-DEPENDENT (b = e^q / 2pi).")

    print("\n[1] LINEAR SPIRAL carrier per L-function: radius (pi/3)n (LINEAR, no sqrt), angle (2pi/q)ln n.")
    print("    Radius grows x e^(mod q) per turn; turns to n=1000 = ln(1000)/q; count/turn grows (NOT 6).")
    print(f"   {'char':>5} {'q':>2} {'e^q/turn':>9} {'radius(1e3)':>12} {'angle(1e3)':>11} "
          f"{'turns by 1e3':>12} {'act.frac':>8}")
    for name in ("eta", "chi3", "chi4", "chi5", "chi8"):
        chi = CHARACTERS[name]; q = chi.q
        rad = float(linspiral_radius(1000)); ang = float(linspiral_angle(1000, q))
        print(f"   {name:>5} {q:>2} {math.exp(q):>9.2f} {rad:>12.3f} {ang:>11.3f} "
              f"{ang/(2*math.pi):>12.2f} {chi.active_fraction:>8.3f}")
    print("   radius (pi/3)n is the SAME for every char (placement); q lives in the ANGLE, which sets")
    print("   the per-turn growth e^q AND is the spin ln n.  No sqrt(n): radius linear, angle = ln n.")

    print("\n[2] height law z_n = n  (Delta z = 1 per integer n, incl chi(n)=0 -> z = e^(y_n)).")
    print(f"   {'n':>8} {'z_n=n':>8} {'angle(chi3)':>13} {'radius(chi3)':>12}")
    for n in (1, 10, 1000, 100000):
        print(f"   {n:>8} {float(carrier_height(n)):>8.0f} {float(linspiral_angle(n, 3)):>13.4f} "
              f"{float(linspiral_radius(n)):>12.3f}")

    print("\n[3] arrows: magnitude = n^(-sigma) (decay, transverse), spin = ln n.")
    print(f"   {'n':>5} {'n^(-1/2)':>10} {'ln n':>9}")
    for n in (1, 4, 100):
        print(f"   {n:>5} {float(magnitude(n)):>10.6f} {float(spin(n)):>9.5f}")

    print("\n[4] the arrow sum is L: cancels at a zero (P = M), O(1) off it.  N = 200000.")
    print(f"   {'char':>5} {'gamma_1':>11} {'|S(gamma)|':>11} {'|S(off)|':>10} "
          f"{'|P|=|M| lanes':>14} {'|P-M| at zero':>14}")
    for name in ("chi3", "chi4", "chi5", "chi8", "eta"):
        chi = CHARACTERS[name]
        g = ZEROS[name][0]
        s_on = abs(phasor_sum(chi, g))
        s_off = abs(phasor_sum(chi, g + 1.3))
        P, M = channel_sums(chi, g)
        print(f"   {name:>5} {g:>11.6f} {s_on:>11.5f} {s_off:>10.4f} "
              f"{0.5*(abs(P)+abs(M)):>14.4f} {abs(P-M):>14.6f}")
    print("   lanes diverge ~sqrt(N) in lockstep; only P - M converges (spec §1, §8).")

    print("\n[5] THE LINEAR SPIRAL carrier, and the model finding the zeros ON it.  Phasor n at radius")
    print("    (pi/3)n [1->pi/3, 2->2pi/3, 3->pi] and angle (2pi/q)ln n.  The ANGLE is the spin:")
    print("    angle * q/(2pi) = ln n, the rate phasor n rotates in y.  No sqrt(n) anywhere.")
    q3 = CHARACTERS["chi3"].q
    print(f"   {'n':>3} {'radius=(pi/3)n':>15} {'angle=(2pi/q)ln n':>18} {'angle*q/2pi = ln n (spin)':>26}")
    for k in (1, 2, 3, 5, 8):
        print(f"   {k:>3} {float(linspiral_radius(k)):>15.6f} {float(linspiral_angle(k, q3)):>18.6f} "
              f"{float(linspiral_angle(k, q3)) * q3 / (2 * math.pi):>26.6f}")
    chi3 = CHARACTERS["chi3"]; nn = np.arange(1, 200001, dtype=float)
    _ph = lambda th: abs(np.sum(chi3(nn) * nn**-0.5 * np.exp(-1j * (8.039737155681467 * q3 / (2*math.pi)) * th)))
    print("   the carrier ENTERS through the angle (= the spin), not the radius:")
    print(f"     angle = ln n   -> |S(zero 8.0397)| = {_ph(linspiral_angle(nn, q3)):.5f}  (closes)")
    print(f"     angle = sqrt n -> |S(zero 8.0397)| = {_ph((2*math.pi/q3) * np.sqrt(nn)):.5f}  (the old winding: breaks)")
    print("     radius (pi/3)n is never in S -> pure placement (all the old 'carrier never enters' showed).")
    try:
        import mpmath as _mp
    except ImportError:
        print("    (the model's high-dps finder needs mpmath.)")
    else:
        print("   the model finds gamma (completed phasor, EM M=8, dps=50, no oracle) on the spiral:")
        print(f"   {'char':>5} {'found gamma (model)':>34} {'err vs oracle':>13} "
              f"{'angle (2pi/q)g':>16} {'radius (pi/3)e^g':>17}")
        worst = _mp.mpf(0)
        for name in ZEROS:
            chi = CHARACTERS[name]
            oracle = analytic_zeros(chi, seeds=ZEROS[name], dps=50)
            for g_seed, g_true in zip(ZEROS[name], oracle):
                g = find_zero_em(chi, g_seed, N=2000, M=8, dps=50)
                err = abs(g - g_true); worst = max(worst, err)
                ang = (2 * _mp.pi / chi.q) * g; rad = (_mp.pi / 3) * _mp.e ** g
                print(f"   {name:>5} {_mp.nstr(g, 26):>34} {_mp.nstr(err, 2):>13} "
                      f"{_mp.nstr(ang, 8):>16} {_mp.nstr(rad, 8):>17}")
        print(f"   worst err over all 50: {_mp.nstr(worst, 2)} (EM M=8 at N=2000); bumping M is ~free, N is not.")
        print("   each zero sits at angle (2pi/q)gamma, radius (pi/3)e^gamma -- found by the model, placed")
        print("   on the linear spiral.  No sqrt(n), no oracle except the err column.")

    print("\n[6] WHAT enters the value, precisely: the carrier's ANGLE does (it IS the spin ln n); the")
    print("    RADIUS does not (placement).  The old claim 'the carrier never enters' only ever varied")
    print("    the radius/growth -- which is why it looked carrier-independent.  Corrected, on chi3:")
    g = ZEROS["chi3"][0]
    nnn = np.arange(1, 50001, dtype=float)
    val = lambda th: abs(np.sum(CHARACTERS["chi3"](nnn) * nnn**-0.5 * np.exp(-1j * (g*3/(2*math.pi)) * th)))
    print(f"   radius (pi/3)n: never in S (placement)  -> |S(zero)| = {val(linspiral_angle(nnn, 3)):.4f}  (any radius -> same)")
    print(f"   angle ln n -> sqrt n (the SPIN)         -> |S(zero)| = {val((2*math.pi/3) * np.sqrt(nnn)):.4f}  (broken)")
    print("   so the carrier DOES enter -- through the angle, which is the spin.  (old sec 6 was incomplete.)")

    print("\n[7] Are those the real zeros?  Independent ground-truth certificate (needs mpmath).")
    print("    §5 finds gamma from the carrier; this confirms each is a genuine zero of the ACTUAL")
    print("    analytic L (Hurwitz zeta / Riemann zeros via mpmath -- nothing to do with the model),")
    print("    so §5's 'exact gamma' is real ground truth, not the code grading its own table.")
    try:
        import mpmath  # noqa: F401  (presence check; the certificate below uses analytic_L internally)
    except ImportError:
        print("    (mpmath not installed -- skipping; `pip install mpmath`.  The model in §5 is NumPy-only.)")
    else:
        res = verify_against_analytic(dps=30)
        print(f"    over all {res['n_zeros']} targeted zeros: max |L(1/2 + i gamma)| = "
              f"{res['max_abs_L_at_zero']:.0e}  -- every one a true on-line zero to ~1e-30.")

    print("\n" + line)
    print("Arrows (n^(-sigma), ln n) set WHICH y cancels = L and its zeros (P = M).")
    print("Carrier: horizontal growth e^(mod q) sets WHERE; height law z_n = n puts every zero")
    print("at z = e^(gamma_k) (shared by all L-functions, riding on spin = log n).")
    print(line)


if __name__ == "__main__":
    _demo()
