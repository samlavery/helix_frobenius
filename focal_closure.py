"""focal_closure.py — exact harmonic cancellation at the zeros, demonstrated
by a growth locator that finds them unaided.

TWO CLAIMS, in order of importance.

1. EXACT HARMONIC CANCELLATION (the pi/3 structure's actual role).  At an
   on-line zero the vanishing is a finite harmonic BALANCE — "negative =
   positive" — not a value manufactured by infinite analytic continuation:

   * the mu6 six-cell closure is EXACT in the Eisenstein integers Z[zeta_6]:
     every complete eta block sums to literally 0 in integer arithmetic — no
     epsilon, no limit (`test_six_cell_closure_exact_integers`; the same fact
     as carrier_fiber's `exact_cell_marker`);
   * the pi/3 cell unit is the NONZERO normalization making the harmonic
     channel an exact scalar multiple of the L-value,
     B(Z) = (pi/3) * L(1/2 + i log Z) identically (Lean `Ucell_ne_zero`,
     `cell_normalized_scalar_exact`, `scalar_zero_iff_L_zero`; mirrored by
     carrier_fiber.analytic_channels).  At a zero the harmonic channel is
     therefore EXACTLY zero: residue-free vanishing, with no remainder term,
     no cutoff error, and no appeal to continuation for the event itself;
   * finitely, the vanishing IS lane balance: the individually large
     (divergent-in-the-limit) lane resultants coincide as complex vectors,
     P = M, while each lane stays O(1)-large (`test_lane_balance_at_zero`).

   So the pi/3 structure is NOT a claim that zeros can be found everywhere;
   it is the claim that WHAT HAPPENS at a zero is an exact harmonic
   cancellation event of the finite carrier structure.

2. THE GROWTH LOCATOR (a numerical demonstration on top of claim 1).  The
   fiber GROWS along the carrier; at head height Z the bank holds every phasor
   n <= Z.  Its balance events locate the zeros without any oracle — which
   demonstrates the cancellation is genuinely in the geometry, but the
   locator is the demo, not the thesis.  Three ingredients, each load-bearing
   (see the test suite for the A/B regressions):

  * HEAD-COUPLED READOUT.  Phasor n's angle is its carrier angle ln x_n
    (x_n = (pi/3) n, fixed at construction); the only logarithm applied at read
    time is the head's own projection y = log Z (the model's readout law
    `resonanceHeightEquiv` / `GeometricReadout`).  This is THE coupling that
    makes the fiber self-locating: an uncoupled rotation rate (or any fixed
    no-log phase law) is height-blind and locates nothing.
  * GROWTH.  Each phasor enters at zero magnitude when the head reaches it and
    grows to its complete value x_n^(-1/2) over the newest fraction of the
    fiber (self-similar C-infinity window w(n/Z), w(0)=1).  Without growth the
    closure is displaced from the true zero by ~1e-2; with it the event
    sharpens as the fiber grows (~1e-4 at Z~1e2 down to ~1e-12 at Z~1e6).
  * LANE CLOSURE.  The bank splits into finitely many lanes (residue classes
    for a Dirichlet character; coefficient signs for a cusp form).  A VANISHING
    is the focal closure of the whole bank: the lane-weighted resultant polygon
    closes,  sum_lane u_lane * R_lane = 0.   The closure measure
    c(Z) = |sum u R| / max |R|  is projective (scale- and gauge-free): in the
    ARROWS the pi/3 scale is provably inert (a constant amplitude times a
    global phase, cancelling between lanes — `test_pi3_arrow_gauge`).  Where
    pi/3 is load-bearing is one level down on each side: in the carrier
    placement that forces the area law and hence the n^(-1/2) amplitude, and
    in the exact cell normalization of claim 1 that makes the harmonic
    channel exactly (pi/3) * L.

Genuine closures have depth c(Z) ~ 1e-6..1e-12 (shallower, ~1e-3, only in
tiny banks Z <~ 200); spurious dips sit at c >~ 0.1.  The depth cut 2e-2
separates them with no per-family tuning.

HONESTY.  No L-function, no reference zero, and no external frequency sweep
appears anywhere in the locator; the published/independent reference ordinates
live in the quarantined REFERENCE section at the bottom and enter only final
|diff| validation columns.  What is claimed is representation equivalence: the
closure events of the growing 3-D bank coincide with the on-line zeros of the
1-D L-function (the per-height convergence layer of the Lean development,
`dirichlet_strip_tendsto_LFunction` etc., is what makes that an identity, not
a metaphor).  The representation pays an honest exponential price: reading
head height Z costs O(Z) phasors and zero k lives at Z = e^(gamma_k).
Completeness — that EVERY nontrivial zero is such a closure event — is
projection primacy (GRH) and is neither assumed nor claimed.

FAMILIES.  One representative per structural axis of the grand-RH scope that
is reachable by finite computation:
  eta (the zeta channel), chi3/chi4/chi5/chi8   real Dirichlet, +/- lanes
  chi5c (order 4), chi7c (order 6)              complex Dirichlet, lane polygon
  delta       Ramanujan Delta, GL(2) weight 12 level 1; tau(n) built from
              scratch via eta(q)^24 (exact limb-split FFT squarings, with
              Hecke-multiplicativity and Deligne-bound assertions)
  e11         elliptic curve 11.a, GL(2) weight 2; a_n via eta(q)^2 eta(q^11)^2
Abelian Dedekind zeta functions factor into Dirichlet L-functions and are
covered by their factors.  Untested (honestly out of reach here): Maass forms,
degree >= 3 primitives, CM/Grossencharacter cases.  L-functions with a pole
need an eta-style regulator, exactly as zeta itself does.

Run:
    python3 focal_closure.py test                    # unit suite (~30 s)
    python3 focal_closure.py demo                    # full family tables (~2-4 min)
    python3 focal_closure.py scan --family chi3 --y0 1.5 --y1 11.6
"""

from __future__ import annotations

import argparse
import math
import unittest
from dataclasses import dataclass, field

import numpy as np

PI3 = math.pi / 3.0


# ============================================================================
# Coefficient builders (everything from scratch; exactness asserted)
# ============================================================================


def eta_pentagonal(N: int) -> np.ndarray:
    """prod (1-q^n) as a dense length-N array (pentagonal number theorem)."""
    c = np.zeros(N, dtype=np.float64)
    k = 0
    while True:
        done = True
        for kk in (k, -k) if k else (0,):
            m = kk * (3 * kk - 1) // 2
            if m < N:
                c[m] += (-1) ** kk
                done = False
        if k and done:
            break
        k += 1
    return c


def eta_cubed(N: int) -> np.ndarray:
    """prod (1-q^n)^3 = sum_k (-1)^k (2k+1) q^{k(k+1)/2}   (Jacobi)."""
    c = np.zeros(N, dtype=np.float64)
    k = 0
    while True:
        m = k * (k + 1) // 2
        if m >= N:
            break
        c[m] += (-1) ** k * (2 * k + 1)
        k += 1
    return c


def fft_square_trunc(a: np.ndarray, N: int) -> np.ndarray:
    L = 1
    while L < 2 * N:
        L *= 2
    fa = np.fft.rfft(a, L)
    return np.fft.irfft(fa * fa, L)[:N]


def exact_square_trunc(a: np.ndarray, N: int, B: float = 8192.0) -> np.ndarray:
    """Exact truncated square of an integer-valued float64 array via balanced
    limb splitting.  Each cross-convolution has values <= N*(B/2)^2 (~2e13 at
    N ~ 1e6), so float64 FFT roundoff (< 0.5) is removed by rounding; because
    convolution magnitudes are local in the output index, small coefficients
    stay exact even when the array's dynamic range exceeds 2^53 (a plain FFT
    square silently destroys them — that failure mode is what this exists for).
    """
    limbs = []
    r = a.copy()
    for _ in range(10):
        if not np.any(r):
            break
        d = np.round(r / B)
        limbs.append(r - B * d)
        r = d
    L = 1
    while L < 2 * N:
        L *= 2
    Fs = [np.fft.rfft(l, L) for l in limbs]
    out = np.zeros(N, dtype=np.float64)
    for i in range(len(Fs)):
        for j in range(i, len(Fs)):
            conv = np.round(np.fft.irfft(Fs[i] * Fs[j], L)[:N])
            out += ((1.0 if i == j else 2.0) * B ** (i + j)) * conv
    return out


def delta_lambda(N: int) -> np.ndarray:
    """lambda(n) = tau(n)/n^{11/2} for n = 1..N (analytic normalization),
    tau via Delta = q * eta(q)^24 with three exact limb-split squarings."""
    P = eta_cubed(N)
    P = exact_square_trunc(P, N)      # eta^6
    P = exact_square_trunc(P, N)      # eta^12
    P = exact_square_trunc(P, N)      # eta^24
    tau = np.zeros(N + 1)
    tau[1:] = P[:N]
    for n, want in ((1, 1), (2, -24), (3, 252), (4, -1472), (5, 4830), (6, -6048)):
        assert tau[n] == want, (n, tau[n], want)
    assert tau[2] * tau[3] == tau[6] and tau[2] * tau[5] == tau[10]      # Hecke
    for p in (101, 1009, 10007, 100003):                                 # Deligne
        if p <= N:
            assert abs(tau[p] / p ** 5.5) <= 2.0, p
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1)
    lam[1:] = tau[1:] / n[1:] ** 5.5
    return lam


def e11_lambda(N: int) -> np.ndarray:
    """lambda(n) = a_n/sqrt(n) for elliptic curve 11.a:
    q * prod (1-q^n)^2 (1-q^{11n})^2  (weight-2 newform, exact small integers)."""
    P1 = eta_pentagonal(N)
    A = np.round(fft_square_trunc(P1, N))
    P11 = np.zeros(N, dtype=np.float64)
    small = eta_pentagonal(N // 11 + 2)
    idx = np.arange(len(small)) * 11
    keep = idx < N
    P11[idx[keep]] = small[keep]
    B = np.round(fft_square_trunc(P11, N))
    L = 1
    while L < 2 * N:
        L *= 2
    prod = np.round(np.fft.irfft(np.fft.rfft(A, L) * np.fft.rfft(B, L), L)[:N])
    a = np.zeros(N + 1)
    a[1:] = prod[:N]
    for n, want in ((1, 1), (2, -2), (3, -1), (4, 2), (5, 1), (7, -2), (11, 1)):
        assert a[n] == want, (n, a[n], want)
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1)
    lam[1:] = a[1:] / np.sqrt(n[1:])
    return lam


def character_values(q: int, gen: int, order: int) -> np.ndarray:
    """Dirichlet character mod q with chi(gen) a primitive order-th root of 1."""
    vals = np.zeros(q, dtype=np.complex128)
    zeta = np.exp(2j * np.pi / order)
    vals[1] = 1.0
    a, k = gen, 1
    while a != 1:
        vals[a] = zeta ** k
        a = (a * gen) % q
        k += 1
    return vals


# ============================================================================
# Families
# ============================================================================


@dataclass
class Family:
    """A grand-RH family instance: per-site coefficients plus a finite lane split.

    coeff(N)    -> complex array c[0..N] (c[n] multiplies phasor n; c[0] unused)
    lane_key(N) -> int array; sites sharing a key form one lane.  The lane
                   weight u_lane is the common unimodular factor c_n/|c_n|.
    """

    name: str
    kind: str                       # 'dirichlet' | 'cusp'
    make: object
    max_N: int = 2_000_000
    _cache: dict = field(default_factory=dict)

    def coeff(self, N: int) -> np.ndarray:
        key = N
        if key not in self._cache:
            self._cache.clear()
            self._cache[key] = self.make(N)
        return self._cache[key]


def _dirichlet_family(name, q, values):
    vals = np.asarray(values, dtype=np.complex128)

    def make(N):
        n = np.arange(0, N + 1, dtype=np.int64)
        return vals[n % q], (n % q)

    return Family(name, "dirichlet", make)


def _cusp_family(name, builder, max_N):
    def make(N):
        lam = builder(min(N, max_N) if False else N)
        return lam.astype(np.complex128), np.sign(lam).astype(np.int64)

    return Family(name, "cusp", make, max_N=max_N)


FAMILIES: dict[str, Family] = {
    "eta": _dirichlet_family("eta", 2, [-1.0, 1.0]),
    "chi3": _dirichlet_family("chi3", 3, [0, 1, -1]),
    "chi4": _dirichlet_family("chi4", 4, [0, 1, 0, -1]),
    "chi5": _dirichlet_family("chi5", 5, [0, 1, -1, -1, 1]),
    "chi8": _dirichlet_family("chi8", 8, [0, 1, 0, -1, 0, -1, 0, 1]),
    "chi5c": _dirichlet_family("chi5c", 5, character_values(5, 2, 4)),
    "chi7c": _dirichlet_family("chi7c", 7, character_values(7, 3, 6)),
    "delta": _cusp_family("delta", delta_lambda, max_N=1_300_000),
    "e11": _cusp_family("e11", e11_lambda, max_N=1_000_000),
}


# ============================================================================
# Claim 1 — exact harmonic cancellation (integer arithmetic, no epsilon)
# ============================================================================

# zeta_6^k in the basis (1, zeta) of Z[zeta_6], where zeta^2 = zeta - 1.
_ZETA6_POWERS = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))


def exact_cell_marker(block_index: int, sign_of_n) -> tuple[int, int]:
    """The signed six-cell marker of one complete mu6 block, computed EXACTLY
    in the Eisenstein integers Z[zeta_6] (integer arithmetic; a residue-free
    algebraic identity, not a numerical limit).  Returns (a, b) with the
    marker a + b*zeta_6; the harmonic cancellation of the block is the exact
    statement (a, b) == (0, 0).  Mirrors carrier_fiber's `exact_cell_marker`
    and the Lean six-cell closure layer."""
    a = b = 0
    start = 6 * (block_index - 1)
    for off in range(6):
        slot = start + off
        s = int(sign_of_n(slot + 1))
        za, zb = _ZETA6_POWERS[slot % 6]
        a += s * za
        b += s * zb
    return a, b


# ============================================================================
# Claim 2 — the growth locator
# ============================================================================


def growth_window(u: np.ndarray) -> np.ndarray:
    """Self-similar C-infinity entry window: w(0)=1 (complete), w(1)=0 (a
    phasor enters as a point when the head reaches it and grows as the head
    advances).  Any w with w(0)=1 leaves the growth limit unchanged."""
    return np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)


def lane_state(family: Family, y: float, arrow_scale: float = PI3, grown: bool = True):
    """Whole-bank lane resultants at head height Z = e^y.

    Returns (F, max_lane, lanes): F = sum_lane u_lane R_lane (the focal
    channel), the largest lane resultant modulus (the projective normalizer),
    and the list of (u_lane, R_lane) pairs — the balance exhibit: at a zero
    the lanes stay individually large while their weighted sum closes."""
    Z = math.exp(y)
    N = int(Z)
    if N < 4:
        return 0j, 0.0, []
    coeffs, keys = family.coeff(N)
    c = coeffs[1 : N + 1]
    k = keys[1 : N + 1]
    n = np.arange(1, N + 1, dtype=np.float64)
    w = growth_window(n / Z) if grown else np.ones_like(n)
    x = arrow_scale * n
    term = np.abs(c) * w * x ** (-0.5) * np.exp(-1j * y * np.log(x))
    F = 0j
    max_lane = 0.0
    lanes = []
    for lane in np.unique(k):
        sel = k == lane
        cs = c[sel]
        nz = np.abs(cs) > 0
        if not np.any(nz):
            continue
        u_lane = complex(cs[nz][0] / abs(cs[nz][0]))
        R = complex(np.sum(term[sel]))
        F += u_lane * R
        max_lane = max(max_lane, abs(R))
        lanes.append((u_lane, R))
    return F, max_lane, lanes


def closure(family: Family, y: float, arrow_scale: float = PI3, grown: bool = True) -> float:
    """Projective closure measure c(Z) = |sum u R| / max |R| at head Z = e^y."""
    F, max_lane, _ = lane_state(family, y, arrow_scale, grown)
    return abs(F) / max_lane if max_lane > 0 else 1.0


def _golden(f, a, b, iters=60):
    gr = (5.0 ** 0.5 - 1.0) / 2.0
    c, d = b - gr * (b - a), a + gr * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(iters):
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - gr * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + gr * (b - a)
            fd = f(d)
    return 0.5 * (a + b)


@dataclass(frozen=True)
class ClosureEvent:
    y: float
    height: float
    depth: float


def scan(family: Family, y0: float, y1: float, per_unit: int = 240, depth_cut: float = 2e-2) -> list[ClosureEvent]:
    """Locate focal-closure events on the growth path y in [y0, y1].

    Detection is intrinsic: local minima of c(Z) below the depth cut.  Genuine
    events sit at 1e-6..1e-12 (1e-3 in tiny banks); spurious dips at >~ 0.1."""
    f = lambda t: closure(family, t)
    ys = np.linspace(y0, y1, max(9, int((y1 - y0) * per_unit)))
    cs = np.array([f(float(t)) for t in ys])
    med = float(np.median(cs))
    step = float(ys[1] - ys[0])
    events = []
    for i in range(1, len(ys) - 1):
        if cs[i] < cs[i - 1] and cs[i] < cs[i + 1] and cs[i] < 0.25 * med:
            y = _golden(f, float(ys[i]) - 1.5 * step, float(ys[i]) + 1.5 * step)
            depth = f(y)
            if depth < depth_cut:
                events.append(ClosureEvent(y=y, height=math.exp(y), depth=depth))
    return events


# ============================================================================
# REFERENCE section — quarantined.  Published/independent ordinates, used ONLY
# for the final |diff| validation columns; they never enter the locator.
#   eta..chi8 : LMFDB / mpmath Hurwitz cross-check (~1e-9), as in the repo.
#   chi5c/chi7c: derived independently via mpmath Hurwitz zeta
#                (L = q^-s sum_a chi(a) zeta(s, a/q), |L| minimized; dps 20).
#   delta/e11 : LMFDB L-function pages (fetched 2026-07-01).
# ============================================================================

REFERENCE_ORDINATES: dict[str, tuple[float, ...]] = {
    "eta": (14.134725141734694, 21.022039638771555, 25.010857580145689),
    "chi3": (8.039737155681467, 11.249206207772935, 15.704619176721626),
    "chi4": (6.020948904697597, 10.243770304166555, 12.988098012312423),
    "chi5": (6.648453344727715, 9.831444432886670, 11.958845626083515),
    "chi8": (4.899973997007037, 7.628428841769398, 10.806588163861712),
    "chi5c": (6.183578, 8.457229),
    "chi7c": (5.198116, 8.413611, 9.979896),
    "delta": (9.222379399921103, 13.907549861392134),
    "e11": (6.362613894713089, 8.603539619290756, 10.035509097181079, 11.451258610345211, 13.568639057129995),
}

DEMO_WINDOWS: dict[str, tuple[tuple[float, float, int], ...]] = {
    "eta": ((13.60, 14.60, 240),),
    "chi3": ((1.50, 11.60, 240),),
    "chi4": ((1.50, 11.00, 240),),
    "chi5": ((1.50, 12.20, 240),),
    "chi8": ((1.50, 11.00, 240),),
    "chi5c": ((1.60, 11.00, 240),),
    "chi7c": ((1.60, 10.00, 240),),
    "delta": ((8.50, 9.80, 240), (13.55, 14.15, 120)),
    "e11": ((5.60, 11.70, 240), (13.35, 13.78, 120)),
}


# ============================================================================
# Tests
# ============================================================================


class FocalClosureTests(unittest.TestCase):
    def _locate(self, name, y0, y1, per_unit=240):
        events = scan(FAMILIES[name], y0, y1, per_unit=per_unit)
        self.assertTrue(events, f"{name}: no closure event in [{y0}, {y1}]")
        return min(events, key=lambda e: e.depth)

    def test_growth_window_properties(self) -> None:
        u = np.array([0.0, 0.3, 0.9, 1.0, 1.5])
        w = growth_window(u)
        self.assertAlmostEqual(float(w[0]), 1.0)
        self.assertTrue(np.all(np.diff(w) <= 0))
        self.assertEqual(float(w[3]), 0.0)

    def test_six_cell_closure_exact_integers(self) -> None:
        """Claim 1: the mu6 harmonic cancellation is EXACT in Z[zeta_6] —
        integer arithmetic, every complete eta block, no epsilon."""
        eta_sign = lambda n: 1 if n % 2 == 1 else -1
        for block in range(1, 1001):
            self.assertEqual(exact_cell_marker(block, eta_sign), (0, 0), block)

    def test_lane_balance_at_zero(self) -> None:
        """Claim 1, seen finitely: at a located zero the lanes are individually
        large and their weighted sum closes — 'negative = positive', a balance
        event, not a small-value readout."""
        g = REFERENCE_ORDINATES["chi3"][0]
        fam = FAMILIES["chi3"]
        y = _golden(lambda t: closure(fam, t), g - 0.05, g + 0.05)
        F, max_lane, lanes = lane_state(fam, y)
        self.assertGreaterEqual(len(lanes), 2)
        for _, R in lanes:
            self.assertGreater(abs(R), 1e4 * abs(F))    # each lane >> the imbalance
        P = next(R for u, R in lanes if abs(u - 1.0) < 1e-12)
        M = next(R for u, R in lanes if abs(u + 1.0) < 1e-12)
        self.assertLess(abs(P - M), 1e-4 * max_lane)    # P = M: the balance

    def test_real_dirichlet_closures(self) -> None:
        for name, (lo, hi), tol in (("chi3", (7.7, 8.4), 1e-5), ("chi4", (5.7, 6.4), 1e-3)):
            e = self._locate(name, lo, hi)
            self.assertLess(abs(e.y - REFERENCE_ORDINATES[name][0]), tol, name)

    def test_zeta_eta_first_zero_deep_bank(self) -> None:
        e = self._locate("eta", 13.95, 14.35, per_unit=100)
        self.assertLess(abs(e.y - REFERENCE_ORDINATES["eta"][0]), 1e-9)
        self.assertLess(e.depth, 1e-10)

    def test_complex_character_lane_polygon(self) -> None:
        for name, (lo, hi), k in (("chi5c", (5.9, 6.5), 0), ("chi7c", (8.1, 8.7), 1)):
            e = self._locate(name, lo, hi)
            self.assertLess(abs(e.y - REFERENCE_ORDINATES[name][k]), 1e-4, name)

    def test_delta_first_zero(self) -> None:
        FAMILIES["delta"].coeff(25_000)      # builder asserts tau/Hecke/Deligne
        e = self._locate("delta", 9.0, 9.45)
        self.assertLess(abs(e.y - REFERENCE_ORDINATES["delta"][0]), 1e-6)

    def test_e11_first_zeros(self) -> None:
        FAMILIES["e11"].coeff(12_000)        # builder asserts a_n table
        for (lo, hi), k, tol in (((6.1, 6.6), 0, 1e-3), ((8.35, 8.85), 1, 1e-4)):
            e = self._locate("e11", lo, hi)
            self.assertLess(abs(e.y - REFERENCE_ORDINATES["e11"][k]), tol)

    def test_growth_is_load_bearing(self) -> None:
        """Without growth the closure minimum is displaced from the true zero."""
        g = REFERENCE_ORDINATES["chi3"][0]
        fam = FAMILIES["chi3"]
        grown = _golden(lambda t: closure(fam, t, grown=True), g - 0.25, g + 0.25)
        hard = _golden(lambda t: closure(fam, t, grown=False), g - 0.25, g + 0.25)
        self.assertLess(abs(grown - g), 1e-5)
        self.assertGreater(abs(hard - g), 1e-3)

    def test_pi3_arrow_gauge(self) -> None:
        """In the arrows pi/3 is pure gauge: bare-n coordinates locate identically."""
        g = REFERENCE_ORDINATES["chi3"][0]
        fam = FAMILIES["chi3"]
        a = _golden(lambda t: closure(fam, t, arrow_scale=PI3), g - 0.25, g + 0.25)
        b = _golden(lambda t: closure(fam, t, arrow_scale=1.0), g - 0.25, g + 0.25)
        self.assertLess(abs(a - b), 1e-9)

    def test_depth_separates_genuine_from_spurious(self) -> None:
        fam = FAMILIES["chi3"]
        g = REFERENCE_ORDINATES["chi3"][0]
        self.assertLess(closure(fam, _golden(lambda t: closure(fam, t), g - 0.05, g + 0.05)), 1e-4)
        spurious = _golden(lambda t: closure(fam, t), 7.70, 7.90)
        self.assertGreater(closure(fam, spurious), 5e-2)


# ============================================================================
# CLI
# ============================================================================


def _report(names, per_unit_override=None):
    for name in names:
        fam = FAMILIES[name]
        ref = REFERENCE_ORDINATES[name]
        events = []
        for y0, y1, pu in DEMO_WINDOWS[name]:
            events += scan(fam, y0, y1, per_unit=per_unit_override or pu)
        print(f"{name}  (windows {[w[:2] for w in DEMO_WINDOWS[name]]}):")
        print(
            f"   {'closure y':>12} {'height Z=e^y':>14} {'depth':>10} {'max lane |R|':>12}"
            f" {'nearest ref':>13} {'|diff|':>9}"
        )
        for e in events:
            near = min(ref, key=lambda g: abs(g - e.y))
            _, max_lane, _ = lane_state(fam, e.y)
            print(
                f"   {e.y:>12.6f} {e.height:>14.1f} {e.depth:>10.2e} {max_lane:>12.3f}"
                f" {near:>13.6f} {abs(e.y - near):>9.1e}"
            )
        missed = [
            g
            for g in ref
            if any(y0 < g < y1 for y0, y1, _ in DEMO_WINDOWS[name])
            and min((abs(g - e.y) for e in events), default=9.0) > 1e-2
        ]
        print(f"   missed reference zeros in windows: {['%.4f' % g for g in missed] if missed else 'none'}\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("test", help="run the unit suite (~30 s)")
    demo = sub.add_parser("demo", help="full family tables incl. deep banks (~2-4 min)")
    demo.add_argument("--family", action="append", choices=sorted(FAMILIES), default=None)
    sc = sub.add_parser("scan", help="locate closure events for one family")
    sc.add_argument("--family", required=True, choices=sorted(FAMILIES))
    sc.add_argument("--y0", type=float, required=True)
    sc.add_argument("--y1", type=float, required=True)
    sc.add_argument("--per-unit", type=int, default=240)
    sc.add_argument("--depth-cut", type=float, default=2e-2)
    args = ap.parse_args()

    if args.cmd == "test":
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(FocalClosureTests)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1
    if args.cmd == "demo":
        print("FOCAL-CLOSURE GROWTH LOCATOR — whole finite bank, head readout y = log Z;")
        print("no L-function in the loop; references enter the |diff| column only.\n")
        _report(args.family or list(FAMILIES))
        return 0
    if args.cmd == "scan":
        fam = FAMILIES[args.family]
        events = scan(fam, args.y0, args.y1, per_unit=args.per_unit, depth_cut=args.depth_cut)
        for e in events:
            print(f"y={e.y:.9f}  Z={e.height:.3f}  depth={e.depth:.3e}")
        if not events:
            print("no closure events found")
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
