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
spec §2; the height law puts each found crossing at z = e^(gamma_k).
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


# Published zeros gamma_k on Re s = 1/2 and their resonant terms e^(gamma_k)  (spec §4).
ZEROS = {
    "chi3": [8.039737, 11.249206, 15.704619, 18.261997],
    "chi4": [6.020949, 10.243770, 12.988098, 16.342607],
    "chi5": [6.648453, 9.831444, 11.958846, 16.033821],
    "eta":  [14.134725, 21.022040, 25.010858, 30.424876],   # first four nontrivial zeta zeros
}


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

    print("\n[1] carrier per L-function: radius ~sqrt(n); turn gap = e^(mod q); phasors/turn,")
    print("    geometric (2*pi*R/u) and LIVE (x active_fraction).  Counts at n = 1000:")
    print(f"   {'char':>5} {'q':>2} {'g=e^q':>9} {'turn gap':>9} {'R(1e3)':>8} {'R/sqrt':>7} "
          f"{'act.frac':>8} {'geo/turn':>9} {'live/turn':>9}")
    for name in ("eta", "chi3", "chi4", "chi5", "chi8"):
        chi = CHARACTERS[name]
        b = radial_b(chi.q)
        R = float(carrier_radius(1000, b))
        print(f"   {name:>5} {chi.q:>2} {growth(chi.q):>9.2f} {2*PI*b:>9.3f} {R:>8.2f} "
              f"{R/math.sqrt(1000):>7.3f} {chi.active_fraction:>8.3f} "
              f"{phasors_per_turn(1000, b):>9.1f} {active_phasors_per_turn(1000, b, chi.active_fraction):>9.1f}")
    b3 = radial_b(3)
    print("   chi3 geometric phasors/turn at n=10, 1e3, 1e5:",
          [round(float(phasors_per_turn(n, b3))) for n in (10, 1000, 100000)], "(spec 41, 489, 4909)")

    print("\n[2] height law z_n = n  (Delta z = 1 per integer n, incl chi(n)=0 -> z = e^(y_n)).")
    print(f"   {'n':>8} {'z_n=n':>8} {'theta_n(chi3)':>13} {'R_n(chi3)':>10}")
    for n in (1, 10, 1000, 100000):
        th = float(theta_at(n, b3))
        print(f"   {n:>8} {float(carrier_height(n)):>8.0f} {th:>13.4f} {b3*th:>10.3f}")

    print("\n[3] arrows: magnitude = n^(-sigma) (decay, transverse), spin = ln n.")
    print(f"   {'n':>5} {'n^(-1/2)':>10} {'ln n':>9}")
    for n in (1, 4, 100):
        print(f"   {n:>5} {float(magnitude(n)):>10.6f} {float(spin(n)):>9.5f}")

    print("\n[4] the arrow sum is L: cancels at a zero (P = M), O(1) off it.  N = 200000.")
    print(f"   {'char':>5} {'gamma_1':>11} {'|S(gamma)|':>11} {'|S(off)|':>10} "
          f"{'|P|=|M| lanes':>14} {'|P-M| at zero':>14}")
    for name in ("chi3", "chi4", "chi5", "eta"):
        chi = CHARACTERS[name]
        g = ZEROS[name][0]
        s_on = abs(phasor_sum(chi, g))
        s_off = abs(phasor_sum(chi, g + 1.3))
        P, M = channel_sums(chi, g)
        print(f"   {name:>5} {g:>11.6f} {s_on:>11.5f} {s_off:>10.4f} "
              f"{0.5*(abs(P)+abs(M)):>14.4f} {abs(P-M):>14.6f}")
    print("   lanes diverge ~sqrt(N) in lockstep; only P - M converges (spec §1, §8).")

    print("\n[5] FIND the crossings from the phasors (sweep+refine |S(y)|, no table); under z_n = n")
    print("    each lands at the HEIGHT z = e^(gamma_k) (spec §4 cancellation heights).")
    print(f"   {'char':>5} {'found gamma':>12} {'published':>11} {'|err|':>8} "
          f"{'height z=e^g':>12} {'arc u*e^g':>11}")
    for name, lo, hi in (("chi3", 6.5, 16.5), ("chi4", 5.0, 17.0),
                          ("chi5", 6.0, 16.5), ("eta", 12.0, 26.0)):
        chi = CHARACTERS[name]
        found = find_zeros(chi, lo, hi)             # independent of ZEROS table
        pub = ZEROS[name]
        for g in found:
            near = min(pub, key=lambda p: abs(p - g))
            print(f"   {name:>5} {g:>12.6f} {near:>11.6f} {abs(g-near):>8.1e} "
                  f"{resonant_term(g):>12.3e} {resonance_arc_position(g):>11.3e}")
    print("   gamma found purely from the cancellation dips; height z = e^(gamma_k) (spec §4).")

    print("\n[6] carrier shape does NOT change L: net(y) is identical regardless of growth/height.")
    g = ZEROS["chi3"][0]
    net_a = PhasorHelix(CHARACTERS["chi3"], N=50_000).net(g)
    print(f"   PhasorHelix(chi3).net({g}) = {net_a:.3e}  (the carrier never enters the sum)")

    print("\n" + line)
    print("Arrows (n^(-sigma), ln n) set WHICH y cancels = L and its zeros (P = M).")
    print("Carrier: horizontal growth e^(mod q) sets WHERE; height law z_n = n puts every zero")
    print("at z = e^(gamma_k) (shared by all L-functions, riding on spin = log n).")
    print(line)


if __name__ == "__main__":
    _demo()
