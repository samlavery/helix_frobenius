#!/usr/bin/env python3
"""Character-agnostic finite carrier/fiber harness for the pi/3 helix model.

This module has three deliberately separate layers.

1. C1 cumulative replacement layer: finite integer phasors use the carrier-cell
   clock exp(-i*(pi/3)*T*log n), with gamma read as T=gamma/(pi/3).  This is
   the default replacement test.

2. Native carrier layer: integer n is placed on the pitch-1 helix with cell
   phase exp(i n pi/3).  This is the no-log carrier spin.  The exact six-cell
   marker lives in the carrier phase.

3. Continuous finite focal layer: height z absorbs floor(z) complete integer
   slots plus a partial next slot.  Carrier phase starts at cell slot 0:
   exp(i*slot*pi/3).  Each absorbed phasor has scaled magnitude
   ((pi/3)(slot+1))^-1/2.  No log(n) spin is used.

Run:
    python3 carrier_fiber.py native --count 600000 --crossings 100000
    python3 carrier_fiber.py validate
    python3 carrier_fiber.py test
    python3 carrier_fiber.py scan --char eta_trivial --height-max 1376046.570489
"""

from __future__ import annotations

import argparse
import math
import unittest
from dataclasses import dataclass

import numpy as np


PI = math.pi
UCELL = PI / 3.0
TRIVIAL_FIRST_FOCAL_HEIGHT = math.exp(14.134725141734694)
TRIVIAL_FOCAL_COUNT = int(math.floor(TRIVIAL_FIRST_FOCAL_HEIGHT))
TRIVIAL_FOCAL_CROSSINGS = TRIVIAL_FOCAL_COUNT // 6
DEFAULT_C1_COUNT = 1_623_346

REFERENCE_GAMMAS: dict[str, tuple[float, ...]] = {
    "eta_trivial": (
        14.134725141734694,
        21.022039638771555,
        25.010857580145689,
        30.424876125859513,
        32.935061587739190,
        37.586178158825671,
        40.918719012147495,
        43.327073280914999,
        48.005150881167160,
        49.773832477672302,
    ),
    "chi3": (
        8.039737155681467,
        11.249206207772935,
        15.704619176721626,
        18.261997495693128,
        20.455770807742493,
        24.059414856493451,
        26.577868735774587,
        28.218164506233386,
        30.745040261382496,
        33.897388927259419,
    ),
    "chi4": (
        6.020948904697597,
        10.243770304166555,
        12.988098012312423,
        16.342607104587222,
        18.291993196123535,
    ),
    "chi5": (
        6.648453344727715,
        9.831444432886670,
        11.958845626083515,
        16.033821128384236,
        17.566994292325555,
    ),
    "chi8": (
        4.899973997007037,
        7.628428841769398,
        10.806588163861712,
        12.310542994236530,
        15.195754250645123,
    ),
}


@dataclass(frozen=True)
class HelixSettings:
    """Native pi/3 carrier settings.

    pitch=1 is the requested vertical pitch in gamma(k).  radial_rate=3 is the
    unit gauge for Delta=pi/3: r*Delta/pi = 1, so the wound radius satisfies
    R_n^2/n -> 1.
    """

    pitch: float = 1.0
    radial_rate: float = 3.0
    delta: float = UCELL

    def arclength(self, k: np.ndarray | float) -> np.ndarray | float:
        k_arr = np.asarray(k, dtype=np.float64)
        p = self.pitch
        r = self.radial_rate
        if r == 0.0:
            out = p * k_arr
        else:
            root = np.sqrt(p * p + r * r + 4.0 * PI * PI * r * r * k_arr * k_arr)
            out = 0.5 * k_arr * root
            out += ((p * p + r * r) / (4.0 * PI * r)) * np.arcsinh(
                2.0 * PI * r * k_arr / math.sqrt(p * p + r * r)
            )
        return float(out) if np.ndim(k) == 0 else out

    def speed(self, k: np.ndarray | float) -> np.ndarray | float:
        k_arr = np.asarray(k, dtype=np.float64)
        p = self.pitch
        r = self.radial_rate
        out = np.sqrt(p * p + r * r + (2.0 * PI * r * k_arr) ** 2)
        return float(out) if np.ndim(k) == 0 else out

    def wind_parameter(self, n: np.ndarray | int, iters: int = 14) -> np.ndarray | float:
        """Solve S(k)=n*pi/3 by Newton, vectorized."""
        n_arr = np.asarray(n, dtype=np.float64)
        s = self.delta * n_arr
        r = self.radial_rate
        target = max(r * self.delta / PI, np.finfo(float).eps)
        k = np.sqrt(np.maximum(n_arr * target, 0.0)) / max(r, np.finfo(float).eps)
        k = np.maximum(k, 0.0)
        for _ in range(iters):
            k -= (self.arclength(k) - s) / self.speed(k)
            k = np.maximum(k, 0.0)
        return float(k) if np.ndim(n) == 0 else k

    def radius(self, n: np.ndarray | int) -> np.ndarray | float:
        out = self.radial_rate * self.wind_parameter(n)
        return float(out) if np.ndim(n) == 0 else out

    def point(self, n: np.ndarray | int) -> np.ndarray | tuple[float, float, float]:
        k = self.wind_parameter(n)
        r = self.radial_rate * np.asarray(k)
        angle = 2.0 * PI * np.asarray(k)
        z = self.pitch * np.asarray(k)
        x = r * np.cos(angle)
        y = r * np.sin(angle)
        if np.ndim(np.asarray(n)) == 0:
            return (float(x), float(y), float(z))
        return np.stack([x, y, z], axis=-1)

    @property
    def radius_sq_over_n_target(self) -> float:
        return self.radial_rate * self.delta / PI


@dataclass(frozen=True)
class PeriodicCharacter:
    """Real periodic coefficient with lanes +1, -1, and optional neutral 0."""

    name: str
    modulus: int
    values: tuple[float, ...]
    description: str = ""

    def __post_init__(self) -> None:
        if len(self.values) != self.modulus:
            raise ValueError("values must have length modulus")

    def __call__(self, n: np.ndarray | int) -> np.ndarray | float:
        idx = np.asarray(n, dtype=np.int64) % self.modulus
        vals = np.asarray(self.values, dtype=np.float64)
        out = vals[idx]
        return float(out) if np.ndim(n) == 0 else out

    @property
    def active_fraction(self) -> float:
        return sum(1 for v in self.values if v != 0.0) / self.modulus


@dataclass(frozen=True)
class PencilFamilyReport:
    crossings: int
    mu_lambda_pairs: tuple[tuple[complex, complex], ...]
    admissible_blocks: int
    focal_markers: int
    max_abs_B: float
    min_abs_A: float
    max_abs_det: float
    max_abs_gram_det: float
    max_det_formula_error: float
    max_gram_formula_error: float


@dataclass(frozen=True)
class FocalScanHit:
    height: float
    readout: float
    absorbed_count: int
    partial: float
    residual: float
    min_abs_A: float
    max_abs_det: float
    max_abs_gram_det: float
    exact: bool
    at_window_edge: bool = False


@dataclass(frozen=True)
class ReplacementCheck:
    index: int
    gamma: float
    height: float
    absorbed_count: int
    partial_phasors: int
    residual: float
    nearest_height: float
    nearest_readout: float
    nearest_residual: float
    height_delta: float
    nearest_at_window_edge: bool
    passed: bool


@dataclass(frozen=True)
class CellClockCheck:
    index: int
    gamma: float
    height: float
    carrier_T: float
    absorbed_count: int
    residual: float
    nearest_T: float
    nearest_gamma: float
    nearest_residual: float
    T_delta: float
    min_abs_A: float
    max_abs_det: float
    max_abs_gram_det: float
    passed: bool


@dataclass(frozen=True)
class NoLogPhaseScan:
    law: str
    count: int
    tau: float
    residual: float
    min_abs_A: float
    max_abs_det: float
    max_abs_gram_det: float
    passed: bool


@dataclass(frozen=True)
class NoLogLaneFit:
    law: str
    count: int
    alpha: float
    beta: float
    residual: float
    min_abs_A: float
    max_abs_det: float
    max_abs_gram_det: float
    nfev: int
    passed: bool


@dataclass(frozen=True)
class NoLogPrefixHit:
    count: int
    residual: float
    readout: float


@dataclass(frozen=True)
class NoLogFocalHit:
    law: str
    tau: float
    height: float
    absorbed_count: int
    partial: float
    gap: float
    determinant: float
    readout: float
    passed: bool


@dataclass(frozen=True)
class HeightAbsorption:
    height: float
    readout: float
    absorbed_count: int
    complete_crossings: int
    partial_phasors: int


@dataclass(frozen=True)
class Eisenstein:
    """Exact a + b*zeta with zeta = exp(i*pi/3), zeta^2 = zeta - 1."""

    a: int = 0
    b: int = 0

    def __add__(self, other: "Eisenstein") -> "Eisenstein":
        return Eisenstein(self.a + other.a, self.b + other.b)

    def __neg__(self) -> "Eisenstein":
        return Eisenstein(-self.a, -self.b)

    def __sub__(self, other: "Eisenstein") -> "Eisenstein":
        return self + (-other)

    def __mul__(self, other: "Eisenstein") -> "Eisenstein":
        # (a+bz)(c+dz) = ac + (ad+bc)z + bd z^2, z^2=z-1.
        return Eisenstein(self.a * other.a - self.b * other.b, self.a * other.b + self.b * other.a + self.b * other.b)

    def scale(self, k: int) -> "Eisenstein":
        return Eisenstein(k * self.a, k * self.b)

    def is_zero(self) -> bool:
        return self.a == 0 and self.b == 0


ZETA6_POWERS: tuple[Eisenstein, ...] = (
    Eisenstein(1, 0),    # zeta^0
    Eisenstein(0, 1),    # zeta^1
    Eisenstein(-1, 1),   # zeta^2
    Eisenstein(-1, 0),   # zeta^3
    Eisenstein(0, -1),   # zeta^4
    Eisenstein(1, -1),   # zeta^5
)


def legendre_character(p: int) -> PeriodicCharacter:
    if p < 3 or p % 2 == 0:
        raise ValueError("p must be an odd prime for this simple Legendre factory")
    vals = [0.0]
    for a in range(1, p):
        vals.append(1.0 if pow(a, (p - 1) // 2, p) == 1 else -1.0)
    return PeriodicCharacter(f"chi{p}", p, tuple(vals), f"quadratic character mod {p}")


CHARACTERS: dict[str, PeriodicCharacter] = {
    "trivial": PeriodicCharacter("trivial", 1, (1.0,), "principal coefficient, no negative lane"),
    "eta_trivial": PeriodicCharacter(
        "eta_trivial", 2, (-1.0, 1.0), "eta regulator for the trivial/principal zeta channel"
    ),
    "chi3": PeriodicCharacter("chi3", 3, (0.0, 1.0, -1.0), "quadratic mod 3"),
    "chi4": PeriodicCharacter("chi4", 4, (0.0, 1.0, 0.0, -1.0), "Dirichlet beta"),
    "chi5": PeriodicCharacter("chi5", 5, (0.0, 1.0, -1.0, -1.0, 1.0), "quadratic mod 5"),
    "chi8": PeriodicCharacter("chi8", 8, (0.0, 1.0, 0.0, -1.0, 0.0, -1.0, 0.0, 1.0), "Kronecker mod 8"),
}


class CarrierFiber:
    def __init__(
        self,
        character: PeriodicCharacter = CHARACTERS["eta_trivial"],
        settings: HelixSettings | None = None,
        sigma: float = 0.5,
        phasor_scale: float = UCELL,
    ) -> None:
        self.character = character
        self.settings = settings or HelixSettings()
        self.sigma = sigma
        self.phasor_scale = phasor_scale

    @staticmethod
    def indices(count: int) -> np.ndarray:
        return np.arange(1, count + 1, dtype=np.int64)

    @staticmethod
    def slots(count: int) -> np.ndarray:
        return np.arange(0, count, dtype=np.int64)

    def absorption_at_height(self, height: float) -> HeightAbsorption:
        """At pitch 1, height z absorbs floor(z) integer phasor slots.

        The readout variable is log(z).  The absorbed finite bank splits into
        complete six-cell focal phasors and a trailing partial block.
        """
        if height <= 0.0:
            raise ValueError("height must be positive")
        absorbed = int(math.floor(height / self.settings.pitch))
        return HeightAbsorption(
            height=height,
            readout=math.log(height),
            absorbed_count=absorbed,
            complete_crossings=absorbed // 6,
            partial_phasors=absorbed % 6,
        )

    def channel_counts(self, count: int) -> dict[str, int]:
        c = self.character(self.indices(count))
        return {
            "positive": int(np.count_nonzero(c > 0.0)),
            "negative": int(np.count_nonzero(c < 0.0)),
            "neutral": int(np.count_nonzero(c == 0.0)),
            "total": int(count),
        }

    def native_phase(self, slot: np.ndarray | int) -> np.ndarray | complex:
        phase = np.exp(1j * self.settings.delta * np.asarray(slot, dtype=np.float64))
        return complex(phase) if np.ndim(slot) == 0 else phase

    def native_terms(self, count: int, block_constant: bool = True) -> np.ndarray:
        """No-log native cell phasors.

        block_constant=True uses one amplitude per six-cell focal block.  Then
        eta_trivial has exact block cancellation because the signed sixth roots
        add to zero in every finite block.
        """
        slot = self.slots(count)
        n = slot + 1
        c = self.character(n)
        if block_constant:
            block = (slot // 6) + 1
            amp = block.astype(np.float64) ** (-self.sigma)
        else:
            amp = n.astype(np.float64) ** (-self.sigma)
        return c * amp * self.native_phase(slot)

    def native_unique_terms(self, count: int) -> np.ndarray:
        """Finite native phasors with carrier spin in n and magnitude (scale*n)^-sigma."""
        slot = self.slots(count)
        n = slot + 1
        c = self.character(n)
        amp = (self.phasor_scale * n.astype(np.float64)) ** (-self.sigma)
        return c * amp * self.native_phase(slot)

    def no_log_phase_data(self, count: int, law: str) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        """Amplitude, fixed phase, and no-log phase frequency for a whole-fiber search.

        The scan value is `sum amp_n * exp(i*(base_n + tau*freq_n))`.
        No law here uses `log n`; the continuous parameter `tau` is a geometric
        twist/readout for the already-built carrier.
        """
        if count <= 0:
            raise ValueError("count must be positive")
        slot = self.slots(count)
        n = slot + 1
        coeff = self.character(n) * (self.phasor_scale * n.astype(np.float64)) ** (-self.sigma)
        zeros = np.zeros(count, dtype=np.float64)
        if law == "cell":
            return coeff, self.settings.delta * slot.astype(np.float64), zeros
        if law == "freq-n":
            return coeff, zeros, n.astype(np.float64)
        if law == "cell-twist":
            return coeff, self.settings.delta * slot.astype(np.float64), slot.astype(np.float64)
        if law == "helix":
            return coeff, zeros, 2.0 * PI * self.settings.wind_parameter(n)
        if law == "helix-cell":
            return coeff, self.settings.delta * slot.astype(np.float64), 2.0 * PI * self.settings.wind_parameter(n)
        raise ValueError(f"unknown no-log phase law {law!r}")

    def no_log_phase_value(self, tau: float, count: int, law: str) -> complex:
        coeff, base, freq = self.no_log_phase_data(count, law)
        return complex(np.sum(coeff * np.exp(1j * (base + tau * freq))))

    def scan_no_log_phase(
        self,
        count: int,
        law: str,
        tolerance: float = 1e-10,
        grid: int = 721,
        tau_min: float = 0.0,
        tau_max: float = 2.0 * PI,
        chunk: int = 8,
        refine_iters: int = 48,
    ) -> NoLogPhaseScan:
        """Scan a no-log whole-fiber phase law for focal cancellation.

        This intentionally ignores six-cell block cancellation.  It tests the
        cumulative fiber as one vector and then computes the same 2x2 pencil
        marker from the unsigned channel `A` and signed channel `B`.
        """
        if tau_max <= tau_min:
            raise ValueError("tau-max must be greater than tau-min")
        grid = max(5, int(grid))
        chunk = max(1, int(chunk))
        coeff, base, freq = self.no_log_phase_data(count, law)
        unsigned = float(np.sum(np.abs(coeff)))

        def objective(tau: float) -> float:
            z = complex(np.sum(coeff * np.exp(1j * (base + tau * freq))))
            return float(z.real * z.real + z.imag * z.imag)

        taus = np.linspace(tau_min, tau_max, grid, dtype=np.float64)
        vals = np.empty(grid, dtype=np.float64)
        for start in range(0, grid, chunk):
            stop = min(start + chunk, grid)
            phase = base[None, :] + taus[start:stop, None] * freq[None, :]
            z = (coeff[None, :] * np.exp(1j * phase)).sum(axis=1)
            vals[start:stop] = z.real * z.real + z.imag * z.imag

        i = int(np.argmin(vals))
        left = float(taus[max(0, i - 1)])
        right = float(taus[min(grid - 1, i + 1)])
        if left == right:
            tau_best = float(taus[i])
            best_sq = float(vals[i])
        else:
            gr = (math.sqrt(5.0) - 1.0) / 2.0
            a = left
            b = right
            c = b - gr * (b - a)
            d = a + gr * (b - a)
            fc = objective(c)
            fd = objective(d)
            for _ in range(max(0, int(refine_iters))):
                if fc <= fd:
                    b = d
                    d = c
                    fd = fc
                    c = b - gr * (b - a)
                    fc = objective(c)
                else:
                    a = c
                    c = d
                    fc = fd
                    d = a + gr * (b - a)
                    fd = objective(d)
            tau_best = 0.5 * (a + b)
            best_sq = objective(tau_best)

        residual = math.sqrt(max(best_sq, 0.0))
        max_abs_det = unsigned * residual
        return NoLogPhaseScan(
            law=law,
            count=count,
            tau=tau_best,
            residual=residual,
            min_abs_A=unsigned,
            max_abs_det=max_abs_det,
            max_abs_gram_det=max_abs_det * max_abs_det,
            passed=residual <= tolerance,
        )

    def no_log_lane_helix_value(self, alpha: float, beta: float, count: int) -> complex:
        """Whole-fiber no-log lane-helix value.

        `alpha` is the shared helix winding readout and `beta` is the
        lane-differential helix readout.  The phase is
        `cell + alpha*theta + beta*chi(n)*theta`; no term uses `log n`.
        """
        if count <= 0:
            raise ValueError("count must be positive")
        slot = self.slots(count)
        n = slot + 1
        lane = self.character(n)
        amp = (self.phasor_scale * n.astype(np.float64)) ** (-self.sigma)
        cell = self.settings.delta * slot.astype(np.float64)
        theta = 2.0 * PI * self.settings.wind_parameter(n)
        phase = cell + alpha * theta + beta * lane * theta
        return complex(np.sum(lane * amp * np.exp(1j * phase)))

    def no_log_lane_helix_prefix_hits(
        self,
        alpha: float,
        beta: float,
        count_max: int,
        threshold: float,
    ) -> tuple[NoLogPrefixHit | None, NoLogPrefixHit]:
        """Scan fixed-parameter no-log lane-helix prefixes up to `count_max`.

        Returns the first prefix below `threshold`, if any, and the best prefix
        over the whole scanned range.  Parameters are fixed before this scan, so
        this is the count-discovery check rather than a refit at every count.
        """
        if count_max <= 0:
            raise ValueError("count-max must be positive")
        slot = self.slots(count_max)
        n = slot + 1
        lane = self.character(n)
        amp = (self.phasor_scale * n.astype(np.float64)) ** (-self.sigma)
        cell = self.settings.delta * slot.astype(np.float64)
        theta = 2.0 * PI * self.settings.wind_parameter(n)
        phase = cell + alpha * theta + beta * lane * theta
        prefixes = np.cumsum(lane * amp * np.exp(1j * phase))
        residuals = np.abs(prefixes)
        first_idx = np.flatnonzero(residuals <= threshold)
        first = None
        if len(first_idx):
            i = int(first_idx[0])
            first = NoLogPrefixHit(i + 1, float(residuals[i]), math.log(i + 1))
        j = int(np.argmin(residuals))
        best = NoLogPrefixHit(j + 1, float(residuals[j]), math.log(j + 1))
        return first, best

    def no_log_focal_eigenheight_scan(
        self,
        count_max: int,
        law: str,
        tau: float = 0.0,
        threshold: float = 1e-10,
        min_height: float = 0.0,
        moment: str = "auto",
    ) -> NoLogFocalHit:
        """Scan continuous no-log prefixes for focal eigenheight cancellation.

        The focal condition is lane-centroid equality:
        `Pz/P = Mz/M`, equivalently `K = Pz*M - Mz*P = 0`.
        This does not use the block marker and does not use the whole-vector
        `B = P-M = 0` surrogate.
        """
        if count_max <= 1:
            raise ValueError("count-max must be greater than 1")
        if min_height < 0.0:
            raise ValueError("min-height must be nonnegative")
        n = self.indices(count_max + 1)
        lane = self.character(n)
        amp = (self.phasor_scale * n.astype(np.float64)) ** (-self.sigma)
        coeff, base, freq = self.no_log_phase_data(count_max + 1, law)
        term = amp * np.exp(1j * (base + tau * freq))
        if moment == "auto":
            moment = "wind" if law in ("helix", "helix-cell") else "count"
        if moment == "count":
            zcoord = n.astype(np.float64)
        elif moment == "wind":
            zcoord = np.asarray(self.settings.wind_parameter(n), dtype=np.float64)
        elif moment == "theta":
            zcoord = 2.0 * PI * np.asarray(self.settings.wind_parameter(n), dtype=np.float64)
        else:
            raise ValueError(f"unknown no-log focal moment {moment!r}")
        pos = lane > 0
        neg = lane < 0

        P_prefix = np.r_[0.0 + 0.0j, np.cumsum(np.where(pos, term, 0.0 + 0.0j))[:-1]]
        M_prefix = np.r_[0.0 + 0.0j, np.cumsum(np.where(neg, term, 0.0 + 0.0j))[:-1]]
        Pz_prefix = np.r_[0.0 + 0.0j, np.cumsum(np.where(pos, zcoord * term, 0.0 + 0.0j))[:-1]]
        Mz_prefix = np.r_[0.0 + 0.0j, np.cumsum(np.where(neg, zcoord * term, 0.0 + 0.0j))[:-1]]

        K0 = Pz_prefix * M_prefix - Mz_prefix * P_prefix
        dK = np.zeros(count_max + 1, dtype=np.complex128)
        dK[pos] = term[pos] * (zcoord[pos] * M_prefix[pos] - Mz_prefix[pos])
        dK[neg] = term[neg] * (Pz_prefix[neg] - zcoord[neg] * P_prefix[neg])
        denom = np.abs(dK) ** 2
        alpha = np.zeros(count_max + 1, dtype=np.float64)
        active = denom > 1e-300
        alpha[active] = -np.real(K0[active] * np.conjugate(dK[active])) / denom[active]
        alpha = np.clip(alpha, 0.0, 1.0)

        term_alpha = alpha * term
        P = P_prefix + np.where(pos, term_alpha, 0.0 + 0.0j)
        M = M_prefix + np.where(neg, term_alpha, 0.0 + 0.0j)
        Pz = Pz_prefix + np.where(pos, alpha * zcoord * term, 0.0 + 0.0j)
        Mz = Mz_prefix + np.where(neg, alpha * zcoord * term, 0.0 + 0.0j)
        K = Pz * M - Mz * P
        min_idx = max(2, int(math.floor(min_height)))
        valid = (np.arange(count_max + 1) >= min_idx) & (np.abs(P) > 1e-12) & (np.abs(M) > 1e-12)
        gap = np.full(count_max + 1, np.inf, dtype=np.float64)
        gap[valid] = np.abs(Pz[valid] / P[valid] - Mz[valid] / M[valid])

        passed = valid & (gap <= threshold)
        if np.any(passed):
            idx = int(np.flatnonzero(passed)[0])
        else:
            idx = int(np.argmin(gap))
        height = float(idx + alpha[idx])
        return NoLogFocalHit(
            law=law,
            tau=float(tau),
            height=height,
            absorbed_count=idx,
            partial=float(alpha[idx]),
            gap=float(gap[idx]),
            determinant=float(abs(K[idx])),
            readout=math.log(height),
            passed=bool(gap[idx] <= threshold),
        )

    def fit_no_log_lane_helix(
        self,
        count: int,
        starts: tuple[tuple[float, float], ...],
        tolerance: float = 1e-10,
        max_nfev: int = 80,
    ) -> NoLogLaneFit:
        """Fit the two-parameter no-log lane-helix readout against the whole fiber."""
        try:
            from scipy.optimize import least_squares
        except ImportError as exc:  # pragma: no cover
            raise RuntimeError("no-log lane fitting requires scipy") from exc
        if count <= 0:
            raise ValueError("count must be positive")
        if not starts:
            raise ValueError("at least one start is required")
        slot = self.slots(count)
        n = slot + 1
        lane = self.character(n)
        amp = (self.phasor_scale * n.astype(np.float64)) ** (-self.sigma)
        cell = self.settings.delta * slot.astype(np.float64)
        theta = 2.0 * PI * self.settings.wind_parameter(n)
        unsigned = float(np.sum(np.abs(lane) * amp))

        def residual_vec(x: np.ndarray) -> np.ndarray:
            phase = cell + float(x[0]) * theta + float(x[1]) * lane * theta
            z = complex(np.sum(lane * amp * np.exp(1j * phase)))
            return np.array([z.real, z.imag], dtype=np.float64)

        best = None
        for start in starts:
            result = least_squares(
                residual_vec,
                np.array(start, dtype=np.float64),
                xtol=1e-12,
                ftol=1e-12,
                gtol=1e-12,
                max_nfev=max_nfev,
                method="lm",
            )
            residual = float(np.linalg.norm(result.fun))
            if best is None or residual < best[0]:
                best = (residual, result)
        assert best is not None
        residual, result = best
        max_abs_det = unsigned * residual
        return NoLogLaneFit(
            law="lane-helix",
            count=count,
            alpha=float(result.x[0]),
            beta=float(result.x[1]),
            residual=residual,
            min_abs_A=unsigned,
            max_abs_det=max_abs_det,
            max_abs_gram_det=max_abs_det * max_abs_det,
            nfev=int(result.nfev),
            passed=residual <= tolerance,
        )

    def continuous_focal_value(self, height: float) -> complex:
        """Finite focal value at height z.

        At pitch 1, height z absorbs floor(z) complete integer phasors and
        a fractional part of the next phasor.  Phase is exp(i n*pi/3);
        magnitude is (phasor_scale*n)^-sigma.  There is no log(n) spin here.
        """
        absorption = self.absorption_at_height(height)
        if absorption.absorbed_count == 0:
            base = 0.0 + 0.0j
        else:
            base = complex(np.sum(self.native_unique_terms(absorption.absorbed_count)))
        alpha = (height / self.settings.pitch) - absorption.absorbed_count
        if alpha <= 0.0:
            return base
        next_n = absorption.absorbed_count + 1
        return base + alpha * self.native_unique_terms(next_n)[-1]

    def continuous_unsigned_value(self, height: float) -> float:
        """Unsigned admissibility channel for the whole absorbed fiber."""
        absorption = self.absorption_at_height(height)
        if absorption.absorbed_count == 0:
            base = 0.0
        else:
            n = np.arange(1, absorption.absorbed_count + 1, dtype=np.float64)
            c = np.abs(self.character(n.astype(np.int64)))
            base = float(np.sum(c * (self.phasor_scale * n) ** (-self.sigma)))
        alpha = (height / self.settings.pitch) - absorption.absorbed_count
        if alpha <= 0.0:
            return base
        next_n = absorption.absorbed_count + 1
        return base + float(alpha * abs(self.character(next_n)) * ((self.phasor_scale * next_n) ** (-self.sigma)))

    def whole_fiber_pencil_stats(
        self,
        height: float,
        mu_lambda_pairs: tuple[tuple[complex, complex], ...] = ((0.0 + 0.0j, 1.0 + 0.0j),),
    ) -> tuple[float, float, float]:
        """Harmonic Gram pencil statistics for the whole continuous fiber at height z.

        A(z) is the unsigned cumulative channel and B(z) is the full signed
        focal fiber.  For H=[[A,B],[mu*A,lambda*B]], det H=(lambda-mu)A B
        and det(H*H)=|det H|^2, so the Gram family detects the same event as
        whole-fiber focal cancellation B(z)=0 whenever A!=0 and lambda!=mu.
        """
        A = complex(self.continuous_unsigned_value(height))
        B = self.continuous_focal_value(height)
        max_abs_det = 0.0
        max_abs_gram_det = 0.0
        for mu, lam in mu_lambda_pairs:
            det = (lam - mu) * A * B
            max_abs_det = max(max_abs_det, abs(det))
            max_abs_gram_det = max(max_abs_gram_det, abs(det) ** 2)
        return abs(A), max_abs_det, max_abs_gram_det

    def replacement_checks(
        self,
        gammas: tuple[float, ...],
        max_height: float,
        threshold: float,
        search_radius: int = 1000,
    ) -> list[ReplacementCheck]:
        checks = []
        for i, gamma in enumerate(gammas, 1):
            height = math.exp(gamma)
            if height > max_height:
                continue
            absorption = self.absorption_at_height(height)
            residual = abs(self.continuous_focal_value(height))
            nearest = self.nearest_focal_eigenheight(height, search_radius=search_radius)
            checks.append(
                ReplacementCheck(
                    index=i,
                    gamma=gamma,
                    height=height,
                    absorbed_count=absorption.absorbed_count,
                    partial_phasors=absorption.partial_phasors,
                    residual=residual,
                    nearest_height=nearest.height,
                    nearest_readout=nearest.readout,
                    nearest_residual=nearest.residual,
                    height_delta=nearest.height - height,
                    nearest_at_window_edge=nearest.at_window_edge,
                    passed=residual <= threshold,
                )
            )
        return checks

    def nearest_focal_eigenheight(self, center_height: float, search_radius: int = 1000) -> FocalScanHit:
        """Nearest local whole-fiber Gram-pencil focal candidate around a height."""
        if center_height <= 0.0:
            raise ValueError("center_height must be positive")
        center_slot = int(math.floor(center_height / self.settings.pitch))
        lo = max(0, center_slot - search_radius)
        hi = center_slot + search_radius + 1
        terms = self.native_unique_terms(hi + 1)
        prefix = np.zeros(hi + 1, dtype=np.complex128)
        prefix[1:] = np.cumsum(terms[:hi])
        slots = np.arange(lo, hi + 1, dtype=np.int64)
        starts = prefix[slots]
        v = terms[slots]
        denom = np.abs(v) ** 2
        alpha = np.zeros_like(denom, dtype=np.float64)
        active = denom > 0.0
        alpha[active] = -np.real(starts[active] * np.conjugate(v[active])) / denom[active]
        alpha = np.clip(alpha, 0.0, 1.0)
        heights = (slots.astype(np.float64) + alpha) * self.settings.pitch
        residuals = np.abs(starts + alpha * v)
        valid = heights > 0.0
        if not np.any(valid):
            raise ValueError("local search produced no positive heights")
        masked = np.where(valid, residuals, np.inf)
        idx = int(np.argmin(masked))
        h = float(heights[idx])
        min_abs_A, max_abs_det, max_abs_gram_det = self.whole_fiber_pencil_stats(h)
        return FocalScanHit(
            height=h,
            readout=math.log(h),
            absorbed_count=int(math.floor(h / self.settings.pitch)),
            partial=float(alpha[idx]),
            residual=float(residuals[idx]),
            min_abs_A=min_abs_A,
            max_abs_det=max_abs_det,
            max_abs_gram_det=max_abs_gram_det,
            exact=bool(residuals[idx] <= 1e-10),
            at_window_edge=bool(idx == 0 or idx == len(slots) - 1),
        )

    def find_continuous_focal_crossings(
        self,
        height_max: float,
        tolerance: float = 1e-10,
        keep: int = 8,
    ) -> list[FocalScanHit]:
        """Scan the continuous finite focal path for origin crossings.

        On each interval [N, N+1], the value is a line segment
        S_N + alpha*v_(N+1).  The closest point to zero on that segment is
        computed directly; residual <= tolerance is reported as an exact
        finite crossing at the requested tolerance.
        """
        if height_max <= 0.0:
            raise ValueError("height_max must be positive")
        max_slot = int(math.floor(height_max / self.settings.pitch))
        terms = self.native_unique_terms(max_slot + 1)
        prefixes = np.empty(max_slot + 1, dtype=np.complex128)
        prefixes[0] = 0.0 + 0.0j
        if max_slot:
            prefixes[1:] = np.cumsum(terms[:max_slot])
        v = terms[: max_slot + 1]
        denom = np.abs(v) ** 2
        alpha = np.zeros_like(denom, dtype=np.float64)
        active = denom > 0.0
        alpha[active] = -np.real(prefixes[active] * np.conjugate(v[active])) / denom[active]
        alpha = np.clip(alpha, 0.0, 1.0)
        height_units = np.arange(0, max_slot + 1, dtype=np.float64) + alpha
        height = height_units * self.settings.pitch
        valid = (height > 0.0) & (height <= height_max)
        residual = np.abs(prefixes + alpha * v)

        exact_idx = np.flatnonzero(valid & (residual <= tolerance))
        if len(exact_idx) == 0:
            candidates = np.flatnonzero(valid)
            order = candidates[np.argsort(residual[candidates])[:keep]]
        else:
            order = exact_idx[:keep]

        hits = []
        seen_heights: set[int] = set()
        for i in order:
            h = float(height[i])
            key = round(h * 1_000_000_000)
            if key in seen_heights:
                continue
            seen_heights.add(key)
            min_abs_A, max_abs_det, max_abs_gram_det = self.whole_fiber_pencil_stats(h)
            hits.append(
                FocalScanHit(
                    height=h,
                    readout=math.log(h),
                    absorbed_count=int(math.floor(h / self.settings.pitch)),
                    partial=float(alpha[i]),
                    residual=float(residual[i]),
                    min_abs_A=min_abs_A,
                    max_abs_det=max_abs_det,
                    max_abs_gram_det=max_abs_gram_det,
                    exact=bool(residual[i] <= tolerance),
                    at_window_edge=False,
                )
            )
        return hits

    def focal_block_sums(self, crossings: int) -> np.ndarray:
        count = 6 * crossings
        terms = self.native_terms(count, block_constant=True)
        return terms.reshape(crossings, 6).sum(axis=1)

    def exact_cell_marker(self, block_index: int) -> Eisenstein:
        """Exact signed six-cell marker in Z[zeta_6] for one focal block."""
        if block_index < 1:
            raise ValueError("block_index is 1-based")
        start_slot = 6 * (block_index - 1)
        total = Eisenstein()
        for offset in range(6):
            slot = start_slot + offset
            n = slot + 1
            c = int(self.character(n))
            total = total + ZETA6_POWERS[slot % 6].scale(c)
        return total

    def exact_focal_marker_count(self, crossings: int) -> int:
        return sum(1 for block in range(1, crossings + 1) if self.exact_cell_marker(block).is_zero())

    def native_harmonic_channels(self, crossings: int) -> tuple[np.ndarray, np.ndarray]:
        """Finite native channels per six-cell crossing block.

        B is the pi/3-scaled signed closure channel.  A is the finite unsigned
        admissibility channel over the same block; it is positive whenever the
        block has an active phasor.
        """
        count = 6 * crossings
        slot = self.slots(count)
        n = slot + 1
        c = self.character(n)
        block = (slot // 6) + 1
        amp = block.astype(np.float64) ** (-self.sigma)
        phase = self.native_phase(slot)
        signed = UCELL * c * amp * phase
        unsigned = UCELL * np.abs(c) * amp
        B = signed.reshape(crossings, 6).sum(axis=1)
        A = unsigned.reshape(crossings, 6).sum(axis=1).astype(np.complex128)
        return A, B

    @staticmethod
    def harmonic_pencil(A: complex, B: complex, mu: complex, lam: complex) -> np.ndarray:
        return np.array([[A, B], [mu * A, lam * B]], dtype=np.complex128)

    @staticmethod
    def harmonic_pencil_det_formula(A: np.ndarray, B: np.ndarray, mu: complex, lam: complex) -> np.ndarray:
        return (lam - mu) * A * B

    @staticmethod
    def gram_matrix(matrix: np.ndarray) -> np.ndarray:
        return matrix.conjugate().T @ matrix

    def verify_focal_marker_pencil_family(
        self,
        crossings: int,
        mu_lambda_pairs: tuple[tuple[complex, complex], ...] = ((0.0 + 0.0j, 1.0 + 0.0j),),
        tolerance: float = 1e-10,
    ) -> PencilFamilyReport:
        A, B = self.native_harmonic_channels(crossings)
        admissible = np.abs(A) > tolerance
        focal_marker = admissible & (np.abs(B) < tolerance)
        max_abs_det = 0.0
        max_abs_gram_det = 0.0
        max_det_err = 0.0
        max_gram_err = 0.0
        for mu, lam in mu_lambda_pairs:
            det_formula = self.harmonic_pencil_det_formula(A, B, mu, lam)
            det_direct = (A * (lam * B)) - (B * (mu * A))
            gram_formula = np.abs(det_formula) ** 2
            max_abs_det = max(max_abs_det, float(np.max(np.abs(det_direct))))
            max_abs_gram_det = max(max_abs_gram_det, float(np.max(gram_formula)))
            max_det_err = max(max_det_err, float(np.max(np.abs(det_direct - det_formula))))

            sample_count = min(crossings, 32)
            if sample_count:
                for i in np.linspace(0, crossings - 1, sample_count, dtype=np.int64):
                    H = self.harmonic_pencil(A[i], B[i], mu, lam)
                    gram_det = np.linalg.det(self.gram_matrix(H))
                    max_gram_err = max(max_gram_err, abs(gram_det - gram_formula[i]))

        return PencilFamilyReport(
            crossings=crossings,
            mu_lambda_pairs=mu_lambda_pairs,
            admissible_blocks=int(np.count_nonzero(admissible)),
            focal_markers=int(np.count_nonzero(focal_marker)),
            max_abs_B=float(np.max(np.abs(B))) if crossings else 0.0,
            min_abs_A=float(np.min(np.abs(A))) if crossings else 0.0,
            max_abs_det=max_abs_det,
            max_abs_gram_det=max_abs_gram_det,
            max_det_formula_error=max_det_err,
            max_gram_formula_error=max_gram_err,
        )

    def pi3_scaled_native_sum(self, count: int, block_constant: bool = True) -> complex:
        return UCELL * complex(np.sum(self.native_terms(count, block_constant=block_constant)))

    def cell_clock_arrays(self, count: int) -> tuple[np.ndarray, np.ndarray, float]:
        return self.finite_clock_arrays(count, self.sigma)

    def finite_clock_arrays(self, count: int, sigma: float) -> tuple[np.ndarray, np.ndarray, float]:
        """Cumulative c1-compatible cell-clock arrays for integers 1..count.

        This is the continuous replacement path used by c1/helix_model.py:
        coefficients and unique magnitudes are cumulative in n, while the
        phasor clock is exp(-i*(pi/3)*T*log n).  No six-cell reset is applied.
        """
        n_int = self.indices(count)
        n = n_int.astype(np.float64)
        coeff = self.character(n_int)
        amp = coeff * n ** (-sigma)
        unsigned = float(np.sum(np.abs(coeff) * n ** (-sigma)))
        return amp.astype(np.float64), np.log(n), unsigned

    @staticmethod
    def cell_clock_value_from_arrays(
        T: float,
        amp: np.ndarray,
        log_n: np.ndarray,
        delta: float = UCELL,
        channel_scale: float = UCELL,
    ) -> complex:
        return channel_scale * complex(np.sum(amp * np.exp(-1j * delta * T * log_n)))

    def cell_clock_value(self, T: float, count: int) -> complex:
        amp, log_n, _unsigned = self.cell_clock_arrays(count)
        return self.cell_clock_value_from_arrays(T, amp, log_n, self.settings.delta)

    def finite_cell_clock_channel(
        self,
        T: float,
        count: int,
        sigma: float,
        channel_scale: float = 1.0,
    ) -> complex:
        amp, log_n, _unsigned = self.finite_clock_arrays(count, sigma)
        return self.cell_clock_value_from_arrays(T, amp, log_n, self.settings.delta, channel_scale)

    def cell_clock_pencil_stats(
        self,
        T: float,
        count: int,
        mu_lambda_pairs: tuple[tuple[complex, complex], ...] = ((0.0 + 0.0j, 1.0 + 0.0j),),
    ) -> tuple[float, float, float, float]:
        A = self.finite_cell_clock_channel(T, count, sigma=1.5, channel_scale=1.0)
        B = self.finite_cell_clock_channel(T, count, sigma=self.sigma, channel_scale=self.settings.delta)
        return self.pencil_stats_from_channels(A, B, mu_lambda_pairs)

    @staticmethod
    def pencil_stats_from_channels(
        A: complex,
        B: complex,
        mu_lambda_pairs: tuple[tuple[complex, complex], ...] = ((0.0 + 0.0j, 1.0 + 0.0j),),
    ) -> tuple[float, float, float, float]:
        max_abs_det = 0.0
        max_abs_gram_det = 0.0
        for mu, lam in mu_lambda_pairs:
            det = (lam - mu) * A * B
            max_abs_det = max(max_abs_det, abs(det))
            max_abs_gram_det = max(max_abs_gram_det, abs(det) ** 2)
        return abs(B), abs(A), max_abs_det, max_abs_gram_det

    def analytic_channels(self, T: float, dps: int = 50) -> tuple[complex, complex]:
        """Lean-aligned analytic harmonic channels.

        Aχ(T) = Lχ(3/2 + i*(pi/3)T)
        Bχ(T) = (pi/3) * Lχ(1/2 + i*(pi/3)T)
        """
        import mpmath as mp

        old_dps = mp.mp.dps
        mp.mp.dps = max(int(dps), 30)
        try:
            gamma = mp.mpf(str(self.settings.delta * T))
            values = [mp.mpf(str(v)) for v in self.character.values]
            A = mp.dirichlet(mp.mpf("1.5") + 1j * gamma, values)
            B = mp.mpf(str(self.settings.delta)) * mp.dirichlet(mp.mpf("0.5") + 1j * gamma, values)
            return complex(A), complex(B)
        finally:
            mp.mp.dps = old_dps

    def analytic_cell_clock_pencil_stats(
        self,
        T: float,
        dps: int = 50,
        mu_lambda_pairs: tuple[tuple[complex, complex], ...] = ((0.0 + 0.0j, 1.0 + 0.0j),),
    ) -> tuple[float, float, float, float]:
        A, B = self.analytic_channels(T, dps=dps)
        return self.pencil_stats_from_channels(A, B, mu_lambda_pairs)

    def nearest_cell_clock_focal_T(
        self,
        center_T: float,
        count: int,
        window: float = 0.05,
        grid: int = 33,
    ) -> tuple[float, float]:
        """Find the nearest local c1-clock focal minimum in T.

        The finite bank has one real parameter T and a complex focal channel
        B(T), so this returns the local minimum of |B(T)| in the requested
        window.  Exact focal cancellation is still the marker: |B|=0.
        """
        amp, log_n, _unsigned = self.finite_clock_arrays(count, self.sigma)

        def objective(T: float) -> float:
            z = self.cell_clock_value_from_arrays(T, amp, log_n, self.settings.delta, self.settings.delta)
            return float((z.real * z.real) + (z.imag * z.imag))

        if window <= 0.0:
            return center_T, math.sqrt(objective(center_T))

        grid = max(5, int(grid))
        if grid % 2 == 0:
            grid += 1
        lo = center_T - window
        hi = center_T + window
        ts = np.linspace(lo, hi, grid)
        vals = np.array([objective(float(t)) for t in ts], dtype=np.float64)
        i = int(np.argmin(vals))
        left = float(ts[max(0, i - 1)])
        right = float(ts[min(grid - 1, i + 1)])
        if left == right:
            return float(ts[i]), math.sqrt(float(vals[i]))

        gr = (math.sqrt(5.0) - 1.0) / 2.0
        a = left
        b = right
        c = b - gr * (b - a)
        d = a + gr * (b - a)
        fc = objective(c)
        fd = objective(d)
        for _ in range(42):
            if fc <= fd:
                b = d
                d = c
                fd = fc
                c = b - gr * (b - a)
                fc = objective(c)
            else:
                a = c
                c = d
                fc = fd
                d = a + gr * (b - a)
                fd = objective(d)
        t_best = 0.5 * (a + b)
        return t_best, math.sqrt(objective(t_best))

    def cell_clock_replacement_checks(
        self,
        gammas: tuple[float, ...],
        max_height: float,
        threshold: float,
        t_window: float = 0.05,
        grid: int = 33,
        count_override: int | None = None,
        mode: str = "analytic",
        dps: int = 50,
    ) -> list[CellClockCheck]:
        checks = []
        for i, gamma in enumerate(gammas, 1):
            height = math.exp(gamma)
            if mode == "finite" and height > max_height and count_override is None:
                continue
            count = count_override if count_override is not None else int(math.floor(height / self.settings.pitch))
            carrier_T = gamma / self.settings.delta
            if mode == "analytic":
                residual, min_abs_A, max_abs_det, max_abs_gram_det = self.analytic_cell_clock_pencil_stats(
                    carrier_T,
                    dps=dps,
                )
                nearest_T = carrier_T
                nearest_residual = residual
                count = 0
            elif mode == "finite":
                residual, min_abs_A, max_abs_det, max_abs_gram_det = self.cell_clock_pencil_stats(carrier_T, count)
                nearest_T, nearest_residual = self.nearest_cell_clock_focal_T(
                    carrier_T,
                    count,
                    window=t_window,
                    grid=grid,
                )
            else:
                raise ValueError(f"unknown c1 validation mode {mode!r}")
            checks.append(
                CellClockCheck(
                    index=i,
                    gamma=gamma,
                    height=height,
                    carrier_T=carrier_T,
                    absorbed_count=count,
                    residual=residual,
                    nearest_T=nearest_T,
                    nearest_gamma=self.settings.delta * nearest_T,
                    nearest_residual=nearest_residual,
                    T_delta=nearest_T - carrier_T,
                    min_abs_A=min_abs_A,
                    max_abs_det=max_abs_det,
                    max_abs_gram_det=max_abs_gram_det,
                    passed=residual <= threshold,
                )
            )
        return checks

class CarrierFiberTests(unittest.TestCase):
    def test_eta_trivial_six_cell_cancellation_exact(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        blocks = fiber.focal_block_sums(1000)
        self.assertLess(float(np.max(np.abs(blocks))), 1e-11)

    def test_eta_trivial_first_focal_count_has_balanced_lanes(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        absorption = fiber.absorption_at_height(TRIVIAL_FIRST_FOCAL_HEIGHT)
        self.assertEqual(absorption.absorbed_count, TRIVIAL_FOCAL_COUNT)
        self.assertEqual(absorption.complete_crossings, TRIVIAL_FOCAL_CROSSINGS)
        self.assertEqual(absorption.partial_phasors, 0)
        self.assertEqual(
            fiber.channel_counts(TRIVIAL_FOCAL_COUNT),
            {"positive": 688_023, "negative": 688_023, "neutral": 0, "total": TRIVIAL_FOCAL_COUNT},
        )

    def test_pi3_scaling_preserves_zero(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        raw = complex(np.sum(fiber.native_terms(600, block_constant=True)))
        scaled = fiber.pi3_scaled_native_sum(600, block_constant=True)
        self.assertLess(abs(raw), 1e-12)
        self.assertLess(abs(scaled), 1e-12)
        self.assertGreater(UCELL, 0.0)

    def test_pitch_one_unit_gauge_area_law(self) -> None:
        settings = HelixSettings(pitch=1.0, radial_rate=3.0)
        n = np.array([10_000, 40_000, 160_000], dtype=np.int64)
        ratios = settings.radius(n) ** 2 / n
        self.assertEqual(settings.pitch, 1.0)
        self.assertLess(abs(float(ratios[-1]) - settings.radius_sq_over_n_target), 0.02)

    def test_character_agnostic_counts(self) -> None:
        fiber = CarrierFiber(CHARACTERS["chi3"])
        self.assertEqual(
            fiber.channel_counts(12),
            {"positive": 4, "negative": 4, "neutral": 4, "total": 12},
        )

    def test_harmonic_pencil_family_eta_crossings(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        self.assertEqual(fiber.exact_focal_marker_count(1000), 1000)
        report = fiber.verify_focal_marker_pencil_family(
            1000,
            mu_lambda_pairs=((0.0 + 0.0j, 1.0 + 0.0j), (2.0 + 0.0j, -3.0 + 0.0j), (1.0j, 2.0 - 1.0j)),
        )
        self.assertEqual(report.admissible_blocks, 1000)
        self.assertEqual(report.focal_markers, 1000)
        self.assertLess(report.max_abs_det, 1e-10)
        self.assertLess(report.max_abs_gram_det, 1e-20)
        self.assertLess(report.max_det_formula_error, 1e-14)

    def test_continuous_focal_value_uses_unique_magnitudes(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        z = 12.5
        direct = complex(np.sum(fiber.native_unique_terms(12))) + 0.5 * fiber.native_unique_terms(13)[-1]
        self.assertLess(abs(fiber.continuous_focal_value(z) - direct), 1e-15)
        unscaled = CarrierFiber(CHARACTERS["eta_trivial"], phasor_scale=1.0)
        self.assertGreater(abs(unscaled.continuous_focal_value(z) - fiber.continuous_focal_value(z)), 1e-3)

    def test_continuous_scan_reports_native_residuals(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        hits = fiber.find_continuous_focal_crossings(100.0, keep=4)
        self.assertTrue(hits)
        self.assertTrue(all(hit.height > 0 for hit in hits))
        self.assertTrue(all(hit.residual >= 0 for hit in hits))
        self.assertTrue(all(hit.min_abs_A > 0 for hit in hits))
        self.assertTrue(all(hit.max_abs_gram_det >= 0 for hit in hits))

    def test_no_log_cell_law_matches_native_prefix(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        count = 128
        self.assertLess(
            abs(fiber.no_log_phase_value(0.0, count, "cell") - fiber.continuous_focal_value(float(count))),
            1e-14,
        )

    def test_no_log_phase_scan_reports_whole_fiber_marker(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        result = fiber.scan_no_log_phase(256, "freq-n", grid=65, chunk=4)
        self.assertEqual(result.law, "freq-n")
        self.assertEqual(result.count, 256)
        self.assertGreaterEqual(result.tau, 0.0)
        self.assertLessEqual(result.tau, 2.0 * PI)
        self.assertGreaterEqual(result.residual, 0.0)
        self.assertGreater(result.min_abs_A, 0.0)
        self.assertAlmostEqual(result.max_abs_gram_det, result.max_abs_det * result.max_abs_det)

    def test_no_log_helix_law_has_unique_spin_rates(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        _, _, freq = fiber.no_log_phase_data(64, "helix")
        rounded = np.round(freq, 12)
        self.assertEqual(len(np.unique(rounded)), len(rounded))
        self.assertTrue(np.all(np.diff(freq) > 0.0))

    def test_no_log_lane_helix_value_is_finite(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        z = fiber.no_log_lane_helix_value(0.1, 0.2, 64)
        self.assertTrue(np.isfinite(z.real))
        self.assertTrue(np.isfinite(z.imag))

    def test_no_log_lane_helix_prefix_hits_report_best(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        first, best = fiber.no_log_lane_helix_prefix_hits(0.1, 0.2, 64, 1e-12)
        self.assertIsNone(first)
        self.assertGreaterEqual(best.count, 1)
        self.assertLessEqual(best.count, 64)
        self.assertGreaterEqual(best.residual, 0.0)

    def test_no_log_focal_eigenheight_scan_reports_gap(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        hit = fiber.no_log_focal_eigenheight_scan(256, "cell", threshold=1e-12)
        self.assertEqual(hit.law, "cell")
        self.assertGreater(hit.height, 0.0)
        self.assertGreaterEqual(hit.gap, 0.0)
        self.assertGreaterEqual(hit.determinant, 0.0)
        gated = fiber.no_log_focal_eigenheight_scan(256, "cell", threshold=1e-12, min_height=128.0)
        self.assertGreaterEqual(gated.height, 128.0)

    def test_no_log_helix_focal_auto_uses_winding_moment(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        auto = fiber.no_log_focal_eigenheight_scan(256, "helix", threshold=1e-12, moment="auto")
        wind = fiber.no_log_focal_eigenheight_scan(256, "helix", threshold=1e-12, moment="wind")
        count = fiber.no_log_focal_eigenheight_scan(256, "helix", threshold=1e-12, moment="count")
        self.assertAlmostEqual(auto.gap, wind.gap)
        self.assertNotAlmostEqual(auto.gap, count.gap)

    def test_c1_cell_clock_matches_scaled_eta_sum(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        gamma = 2.5
        carrier_T = gamma / UCELL
        count = 64
        n_int = fiber.indices(count)
        n = n_int.astype(np.float64)
        direct = UCELL * np.sum(
            fiber.character(n_int)
            * n ** (-0.5)
            * np.exp(-1j * gamma * np.log(n))
        )
        self.assertLess(abs(fiber.cell_clock_value(carrier_T, count) - direct), 1e-14)

    def test_c1_cell_clock_pencil_detects_same_marker(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        residual, min_abs_A, max_abs_det, max_abs_gram_det = fiber.cell_clock_pencil_stats(1.0, 128)
        self.assertGreater(min_abs_A, 0.0)
        self.assertAlmostEqual(max_abs_det, min_abs_A * residual)
        self.assertAlmostEqual(max_abs_gram_det, (min_abs_A * residual) ** 2)

    def test_analytic_channels_match_lean_scaling(self) -> None:
        fiber = CarrierFiber(CHARACTERS["eta_trivial"])
        gamma = REFERENCE_GAMMAS["eta_trivial"][0]
        carrier_T = gamma / UCELL
        residual, min_abs_A, max_abs_det, max_abs_gram_det = fiber.analytic_cell_clock_pencil_stats(
            carrier_T,
            dps=50,
        )
        self.assertLess(residual, 1e-12)
        self.assertGreater(min_abs_A, 0.0)
        self.assertLess(max_abs_det, 1e-12)
        self.assertLess(max_abs_gram_det, 1e-24)


def run_native(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    absorption = resolve_absorption(fiber, args.height, args.count)
    counts = fiber.channel_counts(absorption.absorbed_count)
    crossings = args.crossings if args.crossings is not None else absorption.complete_crossings
    blocks = fiber.focal_block_sums(crossings)
    max_resid = float(np.max(np.abs(blocks))) if len(blocks) else 0.0
    continuous_value = fiber.continuous_focal_value(absorption.height)
    total_scaled = fiber.pi3_scaled_native_sum(6 * crossings, block_constant=True)
    sample_n = np.array([10_000, 100_000, max(absorption.absorbed_count, 1)], dtype=np.int64)
    radii_ratio = fiber.settings.radius(sample_n) ** 2 / sample_n

    print(f"character        : {char.name} ({char.description})")
    print(f"pitch            : {fiber.settings.pitch}")
    print(f"cell unit        : pi/3 = {UCELL:.16f}")
    print(f"phasor scale     : {fiber.phasor_scale:.12f}")
    print(f"radial rate      : {fiber.settings.radial_rate}")
    print(f"height z         : {absorption.height:.6f}")
    print(f"readout log(z)   : {absorption.readout:.12f}")
    print(f"absorbed slots   : {absorption.absorbed_count}")
    print(f"complete/partial : {absorption.complete_crossings} complete, {absorption.partial_phasors} partial")
    print(f"lane counts      : {counts}")
    print(f"focal crossings  : {crossings} complete six-cell blocks")
    print(f"max block residual (native n*pi/3 spin): {max_resid:.3e}")
    print(f"continuous focal residual at height     : {abs(continuous_value):.3e}")
    print(f"pi/3 scaled total over complete blocks : {abs(total_scaled):.3e}")
    print("radius^2/n samples:")
    for n, ratio in zip(sample_n, radii_ratio):
        print(f"  n={int(n):>9}: {float(ratio):.8f}")
    return 0 if max_resid < args.tolerance else 1


def run_pencil(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    pairs = parse_pairs(args.pair)
    absorption = resolve_absorption(fiber, args.height, None)
    crossings = args.crossings if args.crossings is not None else absorption.complete_crossings
    exact_markers = fiber.exact_focal_marker_count(crossings)
    report = fiber.verify_focal_marker_pencil_family(crossings, pairs, tolerance=args.tolerance)
    print(f"character              : {char.name} ({char.description})")
    print(f"pitch                  : {fiber.settings.pitch}")
    print(f"cell unit              : pi/3 = {UCELL:.16f}")
    print(f"phasor scale           : {fiber.phasor_scale:.12f}")
    print(f"height z               : {absorption.height:.6f}")
    print(f"readout log(z)         : {absorption.readout:.12f}")
    print(f"absorbed slots         : {absorption.absorbed_count}")
    print(f"complete/partial       : {absorption.complete_crossings} complete, {absorption.partial_phasors} partial")
    print(f"focal crossings        : {report.crossings} complete six-cell blocks")
    print(f"exact Eisenstein marks : {exact_markers}/{report.crossings}")
    print(f"admissible blocks A!=0 : {report.admissible_blocks}/{report.crossings}")
    print(f"focal markers A!=0,B=0 : {report.focal_markers}/{report.crossings}")
    print(f"min |A|                : {report.min_abs_A:.3e}")
    print(f"max |B|                : {report.max_abs_B:.3e}")
    print(f"max |det H|            : {report.max_abs_det:.3e}")
    print(f"max det Gram(H)        : {report.max_abs_gram_det:.3e}")
    print(f"max det formula error  : {report.max_det_formula_error:.3e}")
    print(f"max Gram formula error : {report.max_gram_formula_error:.3e}")
    print("pencil pairs (mu, lambda):")
    for mu, lam in report.mu_lambda_pairs:
        print(f"  mu={format_complex(mu)}  lambda={format_complex(lam)}")
    ok = (
        exact_markers == report.crossings
        and report.admissible_blocks == report.crossings
        and report.focal_markers == report.crossings
        and report.max_abs_det < args.tolerance
    )
    return 0 if ok else 1


def run_scan(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    hits = fiber.find_continuous_focal_crossings(args.height_max, tolerance=args.tolerance, keep=args.keep)
    print(f"character       : {char.name} ({char.description})")
    print(f"pitch           : {fiber.settings.pitch}")
    print(f"phasor scale    : {fiber.phasor_scale:.12f}")
    print(f"height max      : {args.height_max:.6f}")
    print("native focal scan: phase exp(i*slot*pi/3), slot starts at 0; magnitude (scale*(slot+1))^-1/2")
    for i, hit in enumerate(hits, 1):
        tag = "exact" if hit.exact else "nearest"
        print(
            f"{i:>3}  {tag:>7}  height={hit.height:.9f}  log(height)={hit.readout:.9f}  "
            f"absorbed={hit.absorbed_count}  partial={hit.partial:.6f}  "
            f"|B|={hit.residual:.3e}  |A|={hit.min_abs_A:.3e}  "
            f"|detH|={hit.max_abs_det:.3e}  detGram={hit.max_abs_gram_det:.3e}"
        )
    return 0 if any(hit.exact for hit in hits) else 1


def run_validate_native(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    if char.name not in REFERENCE_GAMMAS:
        raise SystemExit(f"no reference gamma table for {char.name!r}")
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    gammas = REFERENCE_GAMMAS[char.name][: args.limit]
    checks = fiber.replacement_checks(gammas, args.max_height, args.threshold, search_radius=args.search_radius)
    print(f"character       : {char.name} ({char.description})")
    print(f"pitch           : {fiber.settings.pitch}")
    print(f"spin law        : native exp(i*slot*pi/3), slot starts at 0")
    print(f"magnitude       : (scale*n)^-1/2")
    print(f"phasor scale    : {fiber.phasor_scale:.12f}")
    print(f"readout map     : gamma -> z=exp(gamma), log(z)=gamma")
    print(f"height scale    : 1.000000000000")
    print(f"local search    : +/- {args.search_radius} integer slots")
    print(f"max height      : {args.max_height:.6e}")
    print(f"threshold       : {args.threshold:.3e}")
    if not checks:
        print("no reference heights within max-height")
        return 1
    print(
        f"{'k':>3} {'gamma':>14} {'height z':>14} {'absorbed':>10} {'partial':>7} "
        f"{'residual':>12} {'near height':>14} {'delta':>11} {'near resid':>12} {'edge':>5} {'result':>7}"
    )
    for check in checks:
        result = "pass" if check.passed else "miss"
        print(
            f"{check.index:>3} {check.gamma:>14.9f} {check.height:>14.6e} "
            f"{check.absorbed_count:>10} {check.partial_phasors:>7} {check.residual:>12.3e} "
            f"{check.nearest_height:>14.6e} {check.height_delta:>11.3f} "
            f"{check.nearest_residual:>12.3e} {str(check.nearest_at_window_edge):>5} {result:>7}"
        )
    return 0 if all(check.passed for check in checks) else 1


def run_validate_c1(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    if char.name not in REFERENCE_GAMMAS:
        raise SystemExit(f"no reference gamma table for {char.name!r}")
    if args.threshold is None:
        # finite mode carries the conditional-convergence floor of the
        # truncated bank, ~(pi/3)*c/sqrt(count) ~ 5e-4 at the default count;
        # the analytic certificate has no floor.
        args.threshold = 1e-10 if args.mode == "analytic" else 1e-3
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    gammas = REFERENCE_GAMMAS[char.name][: args.limit]
    checks = fiber.cell_clock_replacement_checks(
        gammas,
        args.max_height,
        args.threshold,
        t_window=args.t_window,
        grid=args.grid,
        count_override=args.count,
        mode=args.mode,
        dps=args.dps,
    )
    print(f"character       : {char.name} ({char.description})")
    print(f"pitch           : {fiber.settings.pitch}")
    print(f"cell unit       : pi/3 = {fiber.settings.delta:.16f}")
    print(f"spin law        : c1 cumulative exp(-i*(pi/3)*T*log n)")
    print(f"pencil mode     : {args.mode}")
    if args.mode == "analytic":
        print("channels        : A=L(3/2+i gamma), B=(pi/3)*L(1/2+i gamma)")
        print(f"mpmath dps      : {args.dps}")
    else:
        print("channels        : finite A=sum chi(n)n^-3/2 n^-i gamma, B=(pi/3)*sum chi(n)n^-1/2 n^-i gamma")
    print(f"readout map     : gamma -> z=exp(gamma), T=gamma/(pi/3)")
    print(f"height scale    : 1.000000000000")
    print(f"T search window : +/- {args.t_window:.6g} with grid {args.grid}")
    print(f"max height      : {args.max_height:.6e}")
    print(f"count override  : {args.count if args.mode == 'finite' and args.count is not None else 'analytic'}")
    print(f"threshold       : {args.threshold:.3e}")
    if not checks:
        print("no reference heights within max-height")
        return 1
    print(
        f"{'k':>3} {'gamma':>14} {'T':>14} {'source':>10} "
        f"{'|B(T)|':>12} {'near T':>14} {'near gamma':>14} {'dT':>11} "
        f"{'near |B|':>12} {'|A|':>12} {'|detH|':>12} {'detGram':>12} {'result':>7}"
    )
    for check in checks:
        result = "pass" if check.passed else "miss"
        source = "analytic" if args.mode == "analytic" else str(check.absorbed_count)
        print(
            f"{check.index:>3} {check.gamma:>14.9f} {check.carrier_T:>14.9f} "
            f"{source:>10} {check.residual:>12.3e} "
            f"{check.nearest_T:>14.9f} {check.nearest_gamma:>14.9f} "
            f"{check.T_delta:>11.3e} {check.nearest_residual:>12.3e} "
            f"{check.min_abs_A:>12.3e} {check.max_abs_det:>12.3e} "
            f"{check.max_abs_gram_det:>12.3e} {result:>7}"
        )
    return 0 if all(check.passed for check in checks) else 1


def run_no_log_search(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        sigma=args.sigma,
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    laws = tuple(args.law or ("freq-n", "cell-twist", "helix", "helix-cell"))
    print(f"character       : {char.name} ({char.description})")
    print(f"count           : {args.count}")
    print(f"sigma           : {args.sigma:.6g}")
    print(f"pitch           : {fiber.settings.pitch}")
    print(f"cell unit       : pi/3 = {fiber.settings.delta:.16f}")
    print(f"phasor scale    : {fiber.phasor_scale:.12f}")
    print(f"tau interval    : [{args.tau_min:.9g}, {args.tau_max:.9g}]")
    print(f"grid/chunk      : {args.grid}/{args.chunk}")
    print(f"threshold       : {args.threshold:.3e}")
    print("block path      : ignored")
    print(
        f"{'law':>12} {'tau*':>14} {'|B|':>12} {'|A|':>12} "
        f"{'|detH|':>12} {'detGram':>12} {'result':>7}"
    )
    results = []
    for law in laws:
        result = fiber.scan_no_log_phase(
            args.count,
            law,
            tolerance=args.threshold,
            grid=args.grid,
            tau_min=args.tau_min,
            tau_max=args.tau_max,
            chunk=args.chunk,
            refine_iters=args.refine_iters,
        )
        results.append(result)
        tag = "pass" if result.passed else "miss"
        print(
            f"{result.law:>12} {result.tau:>14.9f} {result.residual:>12.3e} "
            f"{result.min_abs_A:>12.3e} {result.max_abs_det:>12.3e} "
            f"{result.max_abs_gram_det:>12.3e} {tag:>7}"
        )
    return 0 if any(result.passed for result in results) else 1


def run_no_log_fit(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        sigma=args.sigma,
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    starts = tuple(parse_start(item) for item in args.start)
    result = fiber.fit_no_log_lane_helix(
        args.count,
        starts=starts,
        tolerance=args.threshold,
        max_nfev=args.max_nfev,
    )
    check = abs(fiber.no_log_lane_helix_value(result.alpha, result.beta, args.count))
    print(f"character       : {char.name} ({char.description})")
    print(f"count           : {args.count}")
    print(f"sigma           : {args.sigma:.6g}")
    print(f"pitch           : {fiber.settings.pitch}")
    print(f"cell unit       : pi/3 = {fiber.settings.delta:.16f}")
    print(f"phasor scale    : {fiber.phasor_scale:.12f}")
    print("law             : cell + alpha*helix_theta + beta*lane*helix_theta")
    print("block path      : ignored")
    print(f"starts          : {len(starts)}")
    print(f"threshold       : {args.threshold:.3e}")
    print(
        f"{'law':>12} {'alpha':>14} {'beta':>14} {'|B|':>12} {'direct |B|':>12} "
        f"{'|A|':>12} {'|detH|':>12} {'detGram':>12} {'nfev':>6} {'result':>7}"
    )
    tag = "pass" if result.passed else "miss"
    print(
        f"{result.law:>12} {result.alpha:>14.9f} {result.beta:>14.9f} "
        f"{result.residual:>12.3e} {check:>12.3e} {result.min_abs_A:>12.3e} "
        f"{result.max_abs_det:>12.3e} {result.max_abs_gram_det:>12.3e} "
        f"{result.nfev:>6} {tag:>7}"
    )
    return 0 if result.passed else 1


def run_no_log_discover(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        sigma=args.sigma,
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    starts = tuple(parse_start(item) for item in args.start)
    fitted = fiber.fit_no_log_lane_helix(
        args.count_max,
        starts=starts,
        tolerance=args.threshold,
        max_nfev=args.max_nfev,
    )
    first, best = fiber.no_log_lane_helix_prefix_hits(
        fitted.alpha,
        fitted.beta,
        args.count_max,
        args.threshold,
    )
    print(f"character       : {char.name} ({char.description})")
    print(f"count max       : {args.count_max}")
    print(f"sigma           : {args.sigma:.6g}")
    print(f"pitch           : {fiber.settings.pitch}")
    print(f"cell unit       : pi/3 = {fiber.settings.delta:.16f}")
    print(f"phasor scale    : {fiber.phasor_scale:.12f}")
    print("law             : cell + alpha*helix_theta + beta*lane*helix_theta")
    print("block path      : ignored")
    print(f"threshold       : {args.threshold:.3e}")
    print(f"fitted alpha    : {fitted.alpha:.12f}")
    print(f"fitted beta     : {fitted.beta:.12f}")
    print(f"fit |B|max      : {fitted.residual:.3e}")
    endpoint_only = first is not None and first.count == args.count_max
    if first is None:
        print("first prefix    : none")
    else:
        print(
            f"first prefix    : count={first.count} log(count)={first.readout:.12f} "
            f"|B|={first.residual:.3e}"
        )
    print(
        f"best prefix     : count={best.count} log(count)={best.readout:.12f} "
        f"|B|={best.residual:.3e}"
    )
    if endpoint_only and not args.allow_endpoint:
        print("result          : endpoint-only")
        return 1
    print(f"result          : {'pass' if first is not None else 'miss'}")
    return 0 if first is not None else 1


def run_no_log_focal_discover(args: argparse.Namespace) -> int:
    char = get_character(args.char)
    fiber = CarrierFiber(
        char,
        HelixSettings(pitch=args.pitch, radial_rate=args.radial_rate),
        sigma=args.sigma,
        phasor_scale=parse_height_scale(args.phasor_scale),
    )
    laws = tuple(args.law or ("cell", "freq-n", "cell-twist", "helix", "helix-cell"))
    taus = [float(x) for x in (args.tau or [])]
    if args.tau_grid:
        if args.tau_grid < 2:
            raise SystemExit("--tau-grid must be at least 2")
        taus.extend(float(x) for x in np.linspace(args.tau_min, args.tau_max, args.tau_grid, endpoint=False))
    if not taus:
        taus = [0.0]
    deduped_taus = []
    seen_taus = set()
    for tau in taus:
        key = round(tau, 12)
        if key not in seen_taus:
            seen_taus.add(key)
            deduped_taus.append(tau)
    taus = deduped_taus
    print(f"character       : {char.name} ({char.description})")
    print(f"count max       : {args.count_max}")
    print(f"sigma           : {args.sigma:.6g}")
    print(f"pitch           : {fiber.settings.pitch}")
    print(f"cell unit       : pi/3 = {fiber.settings.delta:.16f}")
    print(f"phasor scale    : {fiber.phasor_scale:.12f}")
    print("condition       : Pz/P = Mz/M")
    print("block path      : ignored")
    print(f"moment          : {args.moment}")
    print(f"min height      : {args.min_height:.6f}")
    print(f"tau count       : {len(taus)}")
    print(f"threshold       : {args.threshold:.3e}")
    print(
        f"{'law':>12} {'tau':>12} {'height':>14} {'log(height)':>14} "
        f"{'absorbed':>10} {'partial':>9} {'gap':>12} {'|K|':>12} {'result':>7}"
    )
    hits = []
    for law in laws:
        for tau in taus:
            hit = fiber.no_log_focal_eigenheight_scan(
                args.count_max,
                law,
                tau=tau,
                threshold=args.threshold,
                min_height=args.min_height,
                moment=args.moment,
            )
            hits.append(hit)
            tag = "pass" if hit.passed else "miss"
            print(
                f"{hit.law:>12} {hit.tau:>12.6f} {hit.height:>14.6f} "
                f"{hit.readout:>14.9f} {hit.absorbed_count:>10} {hit.partial:>9.6f} "
                f"{hit.gap:>12.3e} {hit.determinant:>12.3e} {tag:>7}"
            )
    return 0 if any(hit.passed for hit in hits) else 1


def get_character(name: str) -> PeriodicCharacter:
    if name in CHARACTERS:
        return CHARACTERS[name]
    if name.startswith("chi") and name[3:].isdigit():
        return legendre_character(int(name[3:]))
    raise SystemExit(f"unknown character {name!r}; choices include {', '.join(sorted(CHARACTERS))}, chi<p>")


def resolve_absorption(fiber: CarrierFiber, height: float | None, count: int | None) -> HeightAbsorption:
    if height is None and count is None:
        height = TRIVIAL_FIRST_FOCAL_HEIGHT
    if height is not None:
        return fiber.absorption_at_height(height)
    assert count is not None
    height_from_count = count * fiber.settings.pitch
    return HeightAbsorption(
        height=height_from_count,
        readout=math.log(height_from_count) if height_from_count > 0.0 else float("-inf"),
        absorbed_count=count,
        complete_crossings=count // 6,
        partial_phasors=count % 6,
    )


def parse_complex(text: str) -> complex:
    try:
        return complex(text.replace("i", "j"))
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid complex value {text!r}") from exc


def parse_height_scale(text: str) -> float:
    aliases = {
        "1": 1.0,
        "identity": 1.0,
        "pi/3": PI / 3.0,
        "3/pi": 3.0 / PI,
    }
    if text in aliases:
        return aliases[text]
    try:
        return float(text)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid height scale {text!r}") from exc


def parse_pairs(items: list[str]) -> tuple[tuple[complex, complex], ...]:
    if not items:
        return ((0.0 + 0.0j, 1.0 + 0.0j), (2.0 + 0.0j, -3.0 + 0.0j), (1.0j, 2.0 - 1.0j))
    pairs = []
    for item in items:
        if ":" not in item:
            raise SystemExit(f"pencil pair {item!r} must be formatted as mu:lambda")
        raw_mu, raw_lam = item.split(":", 1)
        pairs.append((parse_complex(raw_mu), parse_complex(raw_lam)))
    return tuple(pairs)


def parse_start(text: str) -> tuple[float, float]:
    if ":" not in text:
        raise argparse.ArgumentTypeError("start must be formatted as alpha:beta")
    raw_alpha, raw_beta = text.split(":", 1)
    try:
        return (float(raw_alpha), float(raw_beta))
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid start {text!r}") from exc


def format_complex(z: complex) -> str:
    return f"{z.real:.6g}{z.imag:+.6g}j"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    native = sub.add_parser("native", help="test no-log native pi/3 focal cancellation")
    native.add_argument("--char", default="eta_trivial")
    native.add_argument("--height", type=float, default=None, help="carrier height z; readout is log(z)")
    native.add_argument("--count", type=int, default=None, help="override absorbed integer slots directly")
    native.add_argument("--crossings", type=int)
    native.add_argument("--pitch", type=float, default=1.0)
    native.add_argument("--radial-rate", type=float, default=3.0)
    native.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude: pi/3, 1, 3/pi, or number")
    native.add_argument("--tolerance", type=float, default=1e-10)
    native.set_defaults(func=run_native)

    pencil = sub.add_parser("pencil", help="verify finite harmonic pencil rank-drop at native crossings")
    pencil.add_argument("--char", default="eta_trivial")
    pencil.add_argument("--height", type=float, default=None, help="carrier height z; readout is log(z)")
    pencil.add_argument("--crossings", type=int, default=None)
    pencil.add_argument("--pitch", type=float, default=1.0)
    pencil.add_argument("--radial-rate", type=float, default=3.0)
    pencil.add_argument("--phasor-scale", default="pi/3", help="scale inside whole-fiber phasor magnitude")
    pencil.add_argument("--tolerance", type=float, default=1e-10)
    pencil.add_argument(
        "--pair",
        action="append",
        default=[],
        help="mu:lambda complex pair, e.g. 0:1 or 1j:2-1j. Repeat to test a family.",
    )
    pencil.set_defaults(func=run_pencil)

    scan = sub.add_parser("scan", help="continuous native focal-height scan")
    scan.add_argument("--char", default="eta_trivial")
    scan.add_argument("--height-max", type=float, default=TRIVIAL_FIRST_FOCAL_HEIGHT)
    scan.add_argument("--keep", type=int, default=8)
    scan.add_argument("--pitch", type=float, default=1.0)
    scan.add_argument("--radial-rate", type=float, default=3.0)
    scan.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    scan.add_argument("--tolerance", type=float, default=1e-10)
    scan.set_defaults(func=run_scan)

    validate = sub.add_parser("validate", help="default c1 cumulative pi/3-clock validation against reference heights")
    validate.add_argument("--char", default="eta_trivial")
    validate.add_argument("--limit", type=int, default=10)
    validate.add_argument("--max-height", type=float, default=TRIVIAL_FIRST_FOCAL_HEIGHT)
    validate.add_argument("--threshold", type=float, default=None,
                          help="pass threshold; default 1e-3 (finite floor) or 1e-10 (analytic)")
    validate.add_argument("--mode", choices=("analytic", "finite"), default="finite",
                          help="finite (default): channels from the truncated phasor bank, no L call; "
                               "analytic: mpmath L-value certificate (final-validation use only)")
    validate.add_argument("--dps", type=int, default=50, help="decimal precision for analytic mode")
    validate.add_argument("--count", type=int, default=DEFAULT_C1_COUNT, help="override absorbed integer slots directly")
    validate.add_argument("--t-window", type=float, default=0.05, help="carrier-T search radius around gamma/(pi/3)")
    validate.add_argument("--grid", type=int, default=33, help="coarse grid size before golden search")
    validate.add_argument("--pitch", type=float, default=1.0)
    validate.add_argument("--radial-rate", type=float, default=3.0)
    validate.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    validate.set_defaults(func=run_validate_c1)

    validate_c1 = sub.add_parser("validate-c1", help="alias for the default c1 cumulative pi/3-clock validation")
    validate_c1.add_argument("--char", default="eta_trivial")
    validate_c1.add_argument("--limit", type=int, default=10)
    validate_c1.add_argument("--max-height", type=float, default=TRIVIAL_FIRST_FOCAL_HEIGHT)
    validate_c1.add_argument("--threshold", type=float, default=None,
                             help="pass threshold; default 1e-3 (finite floor) or 1e-10 (analytic)")
    validate_c1.add_argument("--mode", choices=("analytic", "finite"), default="finite")
    validate_c1.add_argument("--dps", type=int, default=50, help="decimal precision for analytic mode")
    validate_c1.add_argument("--count", type=int, default=DEFAULT_C1_COUNT, help="override absorbed integer slots directly")
    validate_c1.add_argument("--t-window", type=float, default=0.05, help="carrier-T search radius around gamma/(pi/3)")
    validate_c1.add_argument("--grid", type=int, default=33, help="coarse grid size before golden search")
    validate_c1.add_argument("--pitch", type=float, default=1.0)
    validate_c1.add_argument("--radial-rate", type=float, default=3.0)
    validate_c1.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    validate_c1.set_defaults(func=run_validate_c1)

    validate_native = sub.add_parser("validate-native", help="diagnose old no-log native focal model against reference heights")
    validate_native.add_argument("--char", default="eta_trivial")
    validate_native.add_argument("--limit", type=int, default=5)
    validate_native.add_argument("--max-height", type=float, default=TRIVIAL_FIRST_FOCAL_HEIGHT)
    validate_native.add_argument("--threshold", type=float, default=1e-6)
    validate_native.add_argument("--search-radius", type=int, default=1000, help="integer-slot radius for local eigenheight search")
    validate_native.add_argument("--pitch", type=float, default=1.0)
    validate_native.add_argument("--radial-rate", type=float, default=3.0)
    validate_native.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    validate_native.set_defaults(func=run_validate_native)

    no_log_search = sub.add_parser("no-log-search", help="scan whole-fiber no-log phase laws")
    no_log_search.add_argument("--char", default="eta_trivial")
    no_log_search.add_argument("--count", type=int, default=TRIVIAL_FOCAL_COUNT)
    no_log_search.add_argument("--law", action="append", default=None, choices=("cell", "freq-n", "cell-twist", "helix", "helix-cell"))
    no_log_search.add_argument("--sigma", type=float, default=0.5)
    no_log_search.add_argument("--pitch", type=float, default=1.0)
    no_log_search.add_argument("--radial-rate", type=float, default=3.0)
    no_log_search.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    no_log_search.add_argument("--tau-min", type=float, default=0.0)
    no_log_search.add_argument("--tau-max", type=float, default=2.0 * PI)
    no_log_search.add_argument("--grid", type=int, default=721)
    no_log_search.add_argument("--chunk", type=int, default=8)
    no_log_search.add_argument("--refine-iters", type=int, default=48)
    no_log_search.add_argument("--threshold", type=float, default=1e-10)
    no_log_search.set_defaults(func=run_no_log_search)

    no_log_fit = sub.add_parser("no-log-fit", help="fit the whole-fiber no-log lane-helix readout")
    no_log_fit.add_argument("--char", default="eta_trivial")
    no_log_fit.add_argument("--count", type=int, default=TRIVIAL_FOCAL_COUNT)
    no_log_fit.add_argument("--sigma", type=float, default=0.5)
    no_log_fit.add_argument("--pitch", type=float, default=1.0)
    no_log_fit.add_argument("--radial-rate", type=float, default=3.0)
    no_log_fit.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    no_log_fit.add_argument("--threshold", type=float, default=1e-10)
    no_log_fit.add_argument("--max-nfev", type=int, default=80)
    no_log_fit.add_argument(
        "--start",
        action="append",
        default=["14.39639015:1", "0.005:1", "0:1", "1:1"],
        help="initial alpha:beta for the fit; repeatable",
    )
    no_log_fit.set_defaults(func=run_no_log_fit)

    no_log_discover = sub.add_parser("no-log-discover", help="fit once, then discover fixed-parameter prefix crossings")
    no_log_discover.add_argument("--char", default="eta_trivial")
    no_log_discover.add_argument("--count-max", type=int, default=2_000_000)
    no_log_discover.add_argument("--sigma", type=float, default=0.5)
    no_log_discover.add_argument("--pitch", type=float, default=1.0)
    no_log_discover.add_argument("--radial-rate", type=float, default=3.0)
    no_log_discover.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    no_log_discover.add_argument("--threshold", type=float, default=1e-10)
    no_log_discover.add_argument("--max-nfev", type=int, default=80)
    no_log_discover.add_argument("--allow-endpoint", action="store_true")
    no_log_discover.add_argument(
        "--start",
        action="append",
        default=["14.39639015:1", "0.005:1", "0:1", "1:1"],
        help="initial alpha:beta for the max-count fit; repeatable",
    )
    no_log_discover.set_defaults(func=run_no_log_discover)

    no_log_focal = sub.add_parser("no-log-focal-discover", help="discover no-log focal eigenheights")
    no_log_focal.add_argument("--char", default="eta_trivial")
    no_log_focal.add_argument("--count-max", type=int, default=2_000_000)
    no_log_focal.add_argument("--law", action="append", default=None, choices=("cell", "freq-n", "cell-twist", "helix", "helix-cell"))
    no_log_focal.add_argument("--tau", action="append", default=None, help="fixed no-log twist tau; repeatable")
    no_log_focal.add_argument("--tau-grid", type=int, default=0, help="add this many evenly-spaced tau values")
    no_log_focal.add_argument("--tau-min", type=float, default=0.0)
    no_log_focal.add_argument("--tau-max", type=float, default=2.0 * PI)
    no_log_focal.add_argument("--min-height", type=float, default=0.0, help="ignore focal candidates below this height")
    no_log_focal.add_argument("--moment", default="auto", choices=("auto", "count", "wind", "theta"))
    no_log_focal.add_argument("--sigma", type=float, default=0.5)
    no_log_focal.add_argument("--pitch", type=float, default=1.0)
    no_log_focal.add_argument("--radial-rate", type=float, default=3.0)
    no_log_focal.add_argument("--phasor-scale", default="pi/3", help="scale inside phasor magnitude")
    no_log_focal.add_argument("--threshold", type=float, default=1e-10)
    no_log_focal.set_defaults(func=run_no_log_focal_discover)

    test = sub.add_parser("test", help="run built-in tests")
    test.set_defaults(func=lambda _args: run_tests())
    return parser


def run_tests() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CarrierFiberTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
