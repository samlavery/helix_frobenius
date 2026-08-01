"""Weil positivity on the carrier's harmonic-cell basis (fast numpy/FFT version).

THE MECHANISM UNDER TEST (novel, 2026-07-31).  Weil's criterion: RH holds iff the
explicit-formula functional

    W(g) = pole(g) + arch(g) - prime(g)        [ = sum_rho ghat(gamma_rho) ]

is >= 0 for every g = h conv h~ (positive-definite test function).  Classically
untouchable for generic tests.  THE BET: on the CARRIER'S OWN harmonic-cell test
family -- bumps centered on the pi/3 cells, where the house has exact arithmetic
(Z[zeta6] closure, exact P=M balance, per-cell conduction cancellation) -- the prime
side is exactly the conduction sum, so positivity may become a per-cell computation.

MANDATORY (house control law): a NON-EULER stream must break it.  If the control
passes too, the mechanism is target-inert => DEAD.

Normalization (Weil/Bombieri), h real even, g = h conv h~, ghat = hhat^2 >= 0:

  sum_rho ghat(gamma) = 2*int g(u) cosh(u/2) du                         [pole]
                      + (1/2pi) int ghat(r) (Re psi(1/4+ir/2) - log pi) dr [arch]
                      - 2*sum_n Lambda(n)/sqrt(n) * g(log n)             [prime]

All integrals on a uniform grid; ghat by FFT; g by autocorrelation.
"""

import numpy as np
from scipy.special import digamma

PI3 = np.pi / 3          # the carrier's harmonic cell width (mu6)


# ------------------------------------------------------------------ streams
def von_mangoldt_array(N):
    """Lambda(n) for n <= N -- the Euler stream (prime powers only)."""
    lam = np.zeros(N + 1)
    sieve = np.zeros(N + 1, dtype=bool)
    for p in range(2, N + 1):
        if not sieve[p]:
            lp = np.log(p)
            q = p
            while q <= N:
                lam[q] = lp
                if q != p:
                    pass
                q *= p
            for m in range(p * p, N + 1, p):
                sieve[m] = True
    return lam


def control_array(N, lam):
    """CONTROL: same support and size, multiplicativity BROKEN by an aperiodic
    (golden-rotation) modulation -- no Euler product.  The mechanism MUST fail here."""
    n = np.arange(N + 1)
    phi = 0.6180339887498948
    return lam * np.cos(2 * np.pi * n * phi)


# ------------------------------------------------------------------ machinery
def build_grid(U, M):
    """Uniform grid on [-U, U] with M points (M even)."""
    u = np.linspace(-U, U, M, endpoint=False)
    du = u[1] - u[0]
    return u, du


def cell_bump(u, center, width):
    """C-infinity bump on one harmonic cell."""
    x = (u - center) / width
    out = np.zeros_like(u)
    m = np.abs(x) < 1
    out[m] = np.exp(-1.0 / (1.0 - x[m] ** 2)) * np.e
    return out


def make_h(u, centers, width, weights):
    """Even cell-basis test function."""
    h = np.zeros_like(u)
    for c, w in zip(centers, weights):
        h += w * (cell_bump(u, c, width) + cell_bump(u, -c, width))
    return h


def autocorrelation(h, du):
    """g = h conv h~ on the same grid (circular, grid is padded by design)."""
    H = np.fft.fft(h)
    g = np.fft.ifft(H * np.conjugate(H)).real * du
    return np.fft.fftshift(g)


def hhat_on(rgrid, h, u, du):
    """hhat(r) = int h(u) e^{iru} du, real for real even h."""
    return np.array([np.sum(h * np.cos(r * u)) * du for r in rgrid])


def weil_functional(u, du, h, lam, N, R, NR):
    g = autocorrelation(h, du)

    # pole term: 2 int g cosh(u/2)
    pole = 2.0 * np.sum(g * np.cosh(u / 2.0)) * du

    # prime term: 2 sum_n Lambda(n)/sqrt(n) g(log n)   (grid interpolation)
    ns = np.arange(2, N + 1)
    logs = np.log(ns)
    inside = logs < u[-1]
    gvals = np.interp(logs[inside], u, g)
    prime = 2.0 * np.sum(lam[ns[inside]] / np.sqrt(ns[inside]) * gvals)

    # arch term: (1/2pi) int ghat(r) (Re psi(1/4 + ir/2) - log pi) dr
    rgrid = np.linspace(-R, R, NR)
    dr = rgrid[1] - rgrid[0]
    hh = hhat_on(rgrid, h, u, du)
    ghat = hh ** 2                       # psd by construction
    w = np.real(digamma(0.25 + 0.5j * rgrid)) - np.log(np.pi)
    arch = np.sum(ghat * w) * dr / (2.0 * np.pi)

    return pole + arch - prime, pole, arch, prime


# ------------------------------------------------------------------ the probe
def run():
    print("=" * 78)
    print("WEIL POSITIVITY ON THE CARRIER'S HARMONIC-CELL BASIS")
    print("cells at pi/3 (mu6 harmonic scale, never unit-1); control = non-Euler stream")
    print("=" * 78)

    U, M = 12.0, 1 << 15
    u, du = build_grid(U, M)
    width = PI3 / 2
    N = 200000
    R, NR = 60.0, 4001

    lam = von_mangoldt_array(N)
    ctrl = control_array(N, lam)

    families = []
    for k in range(1, 6):
        families.append((f"cells 1..{k}",
                         [PI3 * j for j in range(1, k + 1)],
                         [1.0] * k))
    families.append(("cells 1..4 alternating (P=M)",
                     [PI3 * j for j in range(1, 5)],
                     [1.0, -1.0, 1.0, -1.0]))
    families.append(("cells 1..6 (full turn)",
                     [PI3 * j for j in range(1, 7)],
                     [1.0] * 6))

    print(f"\n{'family':<30} {'W_Euler':>13} {'W_control':>13}   {'E':>4} {'C':>4}")
    print("-" * 78)

    eu, ct = [], []
    for name, centers, weights in families:
        h = make_h(u, centers, width, weights)
        we, pe, ae, pre = weil_functional(u, du, h, lam, N, R, NR)
        wc, _, _, _ = weil_functional(u, du, h, ctrl, N, R, NR)
        eu.append(we)
        ct.append(wc)
        print(f"{name:<30} {we:>13.5e} {wc:>13.5e}   "
              f"{'pos' if we > 0 else 'NEG':>4} {'pos' if wc > 0 else 'NEG':>4}")

    print("-" * 78)
    min_e, min_c = min(eu), min(ct)
    print(f"\nMIN over families: Euler = {min_e:.6e}    control = {min_c:.6e}")

    p1 = min_e > 0
    p2 = min_c < min_e
    print("\nKILL-TEST:")
    print(f"  (1) Euler positivity (min W_Euler > 0) ......... {'PASS' if p1 else 'FAIL'}")
    print(f"  (2) control breaks (min W_ctrl < min W_Euler) .. {'PASS' if p2 else 'FAIL'}")
    if min_e != 0:
        print(f"  separation (Euler-control)/|Euler| = {(min_e - min_c) / abs(min_e):.4f}")

    print("\nVERDICT:")
    if p1 and p2:
        print("  SURVIVES round 1 -- Euler positive where the non-Euler control is not.")
        print("  Next: widen the family, test margin collapse, then exactness (Z[zeta6]).")
    elif not p1:
        print("  DEAD as stated: the Euler functional is NOT positive on this family.")
        print("  Publish the null; the cell bumps are not admissible in this")
        print("  normalization (or the truncations distort the balance).")
    else:
        print("  TARGET-INERT: the control passes too -- positivity here does not")
        print("  consume the Euler stream.  DEAD by the house control law.")
    print("=" * 78)


if __name__ == "__main__":
    run()
