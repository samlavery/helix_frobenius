"""att516 — TRACK B1/B2: the cell-resolved doubled pencil (HP_SKELETON.md).

Ledger 108 named the defect of the 2-lane detector: summing each lane to a
complex SCALAR makes the lane Gram identically rank-degenerate (scalar
Cauchy-Schwarz equality).  Ledger 110 built that scalar detector, confirmed the
P=M shadow at +5.7 sigma, and measured it ~50x too weak to resolve an injected
drift delta = 0.05; it specified the fix -- genuine lane VECTORS -- and the fix
was never built.  This is the fix: each channel is resolved over the mu6 carrier
cells, so the rows are 6-vectors and the Gram is not identically singular.

THE OBJECT (double-ended, per ledger 109's cosh-drift functional):
  cell-resolved channel at abscissa sigma, cell j:
     B_j(y, sigma) = sum_{n = j mod 6} c_n w_n x_n^{-sigma} exp(-i y log x_n)
  rows: the two FE ends sigma = 1/2 + delta and sigma = 1/2 - delta
  G = M M^H (2x2 Hermitian PSD);  contact functional
     kappa = det G / (|row+|^2 |row-|^2) = sin^2(angle between the end vectors).
  delta = 0 makes the rows identical => kappa == 0 identically (the on-line
  degeneracy); delta != 0 is the drift, and kappa is its signal.

IDENTITY CHECKS RUN FIRST (a failure is a BUG, not a finding):
  (I1) the cell sums reproduce the compiled channel identity B = (pi/3)*L:
       sum_j B_j(y, 1/2) / gauge  ==  eta(1/2 + iy) = (1 - 2^{1-s}) zeta(s).
  (I2) kappa(y, 0) == 0 to machine precision at every y (row identity).
  (I3) the compiled ledger balance (CarrierLedgerBalance.ledger_balance_constant_free)
       reproduced numerically at Re s > 1 from the zero cache.

Then the B2 calibration with its PRE-REGISTERED decision rule:
  resolution >= 10x the 2-lane baseline (ledger 110: excess +0.0074 against a
  noise floor ~0.4 at delta = 0.05, i.e. SNR ~ 0.019) => the lift is
  load-bearing for detection.  Below that => it is not, at this projection.

Read-only.  No repo state is modified.
"""

from __future__ import annotations

import math
import numpy as np
import mpmath as mp

PI3 = math.pi / 3.0


# ---------------------------------------------------------------- the bank

def growth_window(u):
    """focal_closure.growth_window, verbatim: w(0)=1, w(1)=0, C-infinity."""
    return np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)


def cell_channels(y, sigma, gauge=PI3, cells=6, signed=True):
    """Cell-resolved channel vector at head height Z = e^y, abscissa sigma.

    Returns a complex array of length `cells`: entry j is the sum over bank
    sites n = j (mod cells).  eta family (the zeta channel): c_n = (-1)^{n+1}.
    """
    Z = math.exp(y)
    N = int(Z)
    n = np.arange(1, N + 1, dtype=np.float64)
    c = np.where((np.arange(1, N + 1) % 2) == 1, 1.0, -1.0)      # eta coefficients
    if not signed:
        c = np.abs(c)
    w = growth_window(n / Z)
    x = gauge * n
    term = c * w * x ** (-sigma) * np.exp(-1j * y * np.log(x))
    idx = (np.arange(1, N + 1) % cells)
    out = np.zeros(cells, dtype=np.complex128)
    np.add.at(out, idx, term)
    return out


def kappa(y, delta, cells=6, gauge=PI3):
    """Contact functional: sin^2 of the angle between the two FE end vectors."""
    vp = cell_channels(y, 0.5 + delta, gauge=gauge, cells=cells)
    vm = cell_channels(y, 0.5 - delta, gauge=gauge, cells=cells)
    np2 = float(np.vdot(vp, vp).real)
    nm2 = float(np.vdot(vm, vm).real)
    if np2 <= 0.0 or nm2 <= 0.0:
        return float("nan")
    ip = np.vdot(vp, vm)
    return float(max(0.0, 1.0 - (abs(ip) ** 2) / (np2 * nm2)))


# ------------------------------------------------------- identity check I1

def eta_exact(y, dps=30):
    """eta(1/2 + iy) = (1 - 2^{1-s}) zeta(s), the compiled ordered readout."""
    mp.mp.dps = dps
    s = mp.mpf(0.5) + 1j * mp.mpf(y)
    return complex((1 - mp.power(2, 1 - s)) * mp.zeta(s))


def check_I1(ys):
    print("=" * 74)
    print("I1  cell sums vs the compiled channel identity  B = (pi/3) * L")
    print("    sum_j B_j(y, 1/2) / gauge_factor   vs   eta(1/2 + iy)")
    print("=" * 74)
    print(f"{'y':>10} {'|bank|':>13} {'|eta|':>13} {'rel err':>11}  {'note':<14}")
    worst = 0.0
    for y, note in ys:
        v = cell_channels(y, 0.5)
        # gauge: x = (pi/3) n  =>  x^{-1/2} e^{-iy log x} = (pi/3)^{-1/2-iy} n^{-1/2-iy}
        g = complex(mp.power(mp.mpf(PI3), mp.mpf(-0.5) - 1j * mp.mpf(y)))
        bank = complex(v.sum()) / g
        ex = eta_exact(y)
        rel = abs(bank - ex) / max(abs(ex), 1e-300)
        worst = max(worst, rel if abs(ex) > 1e-6 else 0.0)
        print(f"{y:10.6f} {abs(bank):13.6e} {abs(ex):13.6e} {rel:11.3e}  {note:<14}")
    print(f"\n  worst relative error away from zeros: {worst:.3e}")
    return worst


# ------------------------------------------------------- identity check I2

def check_I2(ys):
    print()
    print("=" * 74)
    print("I2  kappa(y, 0) == 0 identically  (the two FE ends coincide on-line)")
    print("=" * 74)
    mx = 0.0
    for y, note in ys:
        k = kappa(y, 0.0)
        mx = max(mx, k)
        print(f"  y = {y:10.6f}   kappa = {k:.3e}   {note}")
    print(f"\n  max kappa at delta = 0: {mx:.3e}   (machine zero expected)")
    return mx


# ------------------------------------------------------- identity check I3

def check_I3(s_test=(2.3, 30.0), nzeros=2000, dps=30):
    """The compiled constant-free ledger balance, numerically:

        2 L(Lambda)(s) = - sum_rho m ((s-rho)^-1 - ((1-s)-rho)^-1)
                         + 2 (1/s + 1/(s-1) + Gamma_R'/Gamma_R(s))

    (CriticalLinePhasor.LedgerBalance.ledger_balance_constant_free, Re s > 1.)
    """
    print()
    print("=" * 74)
    print("I3  compiled ledger balance  (CarrierLedgerBalance, Re s > 1)")
    print("=" * 74)
    mp.mp.dps = dps
    sig, t = s_test
    s = mp.mpf(sig) + 1j * mp.mpf(t)

    lhs = -2 * mp.zeta(s, derivative=1) / mp.zeta(s)          # 2 L(Lambda)(s) = -2 zeta'/zeta

    gam = np.load("tmp/att015_zeros_to_30000.npy")[:nzeros]
    zs = 0.5 + 1j * gam
    acc = mp.mpc(0)
    for z in zs:                                               # rho and its conjugate
        for rho in (mp.mpc(0.5, float(z.imag)), mp.mpc(0.5, -float(z.imag))):
            acc += 1 / (s - rho) - 1 / ((1 - s) - rho)
    zero_side = -acc

    def log_deriv_GammaR(z):
        # Gamma_R(s) = pi^{-s/2} Gamma(s/2)  =>  logDeriv = -log(pi)/2 + psi(s/2)/2
        return -mp.log(mp.pi) / 2 + mp.digamma(z / 2) / 2

    carrier = 2 * (1 / s + 1 / (s - 1) + log_deriv_GammaR(s))
    rhs = zero_side + carrier

    print(f"  s          = {complex(s)}")
    print(f"  LHS  2L(Lam)= {complex(lhs)}")
    print(f"  RHS         = {complex(rhs)}")
    print(f"  |LHS - RHS| = {float(abs(lhs - rhs)):.6e}      (zeros used: {2*len(zs)})")
    print(f"  tail scale  ~ {float(2*abs(s)/gam[nzeros-1]):.2e}  (truncation, not error)")
    return float(abs(lhs - rhs))


# ------------------------------------------------------------ B2 calibration

def calibrate(y0, deltas=(0.0, 0.01, 0.02, 0.05), cells_list=(2, 3, 6), span=0.05, npts=9):
    """kappa at the located event vs matched off-event points, per cell count."""
    print()
    print("=" * 74)
    print("B2  contact functional: cell resolution vs the 2-lane baseline")
    print("    (ledger 110 scalar baseline at delta=0.05: excess +0.0074, floor ~0.4,")
    print("     SNR ~ 0.019;  PRE-REGISTERED bar: 10x that SNR)")
    print("=" * 74)
    offs = [y0 + span * (0.4 + 0.6 * i / (npts - 1)) for i in range(npts)]
    print(f"{'cells':>6} {'delta':>7} {'kappa(zero)':>14} {'kappa(off) med':>16} "
          f"{'off spread':>12} {'SNR':>10}")
    results = {}
    for cells in cells_list:
        for d in deltas:
            kz = kappa(y0, d, cells=cells)
            ko = np.array([kappa(u, d, cells=cells) for u in offs])
            med = float(np.median(ko))
            spread = float(np.std(ko))
            snr = abs(kz - med) / spread if spread > 0 else float("nan")
            results[(cells, d)] = (kz, med, spread, snr)
            print(f"{cells:6d} {d:7.3f} {kz:14.6e} {med:16.6e} "
                  f"{spread:12.3e} {snr:10.3f}")
    return results


def main():
    # the first zeta zero: the only event the growth bank reaches at this cost
    # (Z = e^y phasors; y = 14.13 is ~1.37e6 sites).
    gamma1 = 14.134725141734693
    ys = [(gamma1, "ZERO gamma_1"), (gamma1 + 0.05, "off"), (gamma1 - 0.05, "off"),
          (13.0, "off"), (15.0, "off")]

    e1 = check_I1(ys)
    e2 = check_I2(ys)
    e3 = check_I3()

    print()
    print("IDENTITY GATE:", "PASS" if (e1 < 1e-2 and e2 < 1e-20) else "FAIL",
          f"  (I1 {e1:.2e} < 1e-2, I2 {e2:.2e} < 1e-20)")
    if not (e1 < 1e-2 and e2 < 1e-20):
        print("  -> BUG, not a finding.  Stop; do not read the calibration.")
        return

    calibrate(gamma1)


if __name__ == "__main__":
    main()
