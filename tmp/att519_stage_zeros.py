"""att519 -- are the finite theta-stages real-rooted?  (STRONGER-constructive candidate test)

A2 (XiStageHolomorphy.lean) compiled: the stages
    Xi_U(z) = 2 * int_0^U Phi(u) cos(z u) du,
    Phi(u)  = 4 * sum_n (2 pi^2 n^4 e^{9u/2} - 3 pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}}
are entire in z and converge to Xi(z) = xi(1/2 + i z) locally uniformly on C, derivatives
included.  If every stage were real-rooted, RH would follow (Hurwitz through the compiled
convergence).  Real-rootedness of the stages is STRICTLY STRONGER than RH and is a property
of an explicit finite object -- exactly the leaf shape rule 11 asks for.  So: measure it.

PRE-REGISTERED DECISION RULE.  For each extent U and window T, count zeros of Xi_U inside the
rectangle |Re z| <= T, |Im z| <= H by the argument principle (winding number of Xi_U along
the boundary, adaptively sampled so consecutive phase steps stay below pi/2), and count REAL
zeros by sign changes of the real-valued Xi_U on [-T, T].  Equality of the two counts at
every (U, T) tested SUPPORTS real-rootedness in the window; any excess in the rectangle
REFUTES it and the excess zeros are located and reported.

PREDICTION (recorded before running): the stages are NOT real-rooted for small U; non-real
zeros appear beyond the tracking window where the stage has "its own" zeros (exponential
type U gives density ~U/pi per unit, while Xi's density is ~log(t/2pi)/(2pi)).  For U >= 2
the tracking window exceeds T = 100 and the stage zeros coincide with the known real zeros
of Xi there, so the counts agree for the wrong reason.  The informative rows are U <= 1.

Read-only.  No repo state modified.
"""

from __future__ import annotations

import math
import numpy as np

PI = math.pi


def phi(u: np.ndarray, nmax: int = 60) -> np.ndarray:
    """Riemann's theta kernel Phi(u) on u >= 0 (series converges super-exponentially)."""
    u = np.asarray(u, dtype=np.float64)
    out = np.zeros_like(u)
    e2 = np.exp(2.0 * u)
    e9 = np.exp(4.5 * u)
    e5 = np.exp(2.5 * u)
    for n in range(1, nmax + 1):
        out += (2 * PI**2 * n**4 * e9 - 3 * PI * n**2 * e5) * np.exp(-PI * n * n * e2)
    return 4.0 * out


def gauss_legendre(U: float, m: int = 4000):
    x, w = np.polynomial.legendre.leggauss(m)
    u = 0.5 * U * (x + 1.0)
    return u, 0.5 * U * w


def make_stage(U: float, m: int = 4000):
    u, w = gauss_legendre(U, m)
    pw = phi(u) * w

    def xi_stage(z):
        z = np.asarray(z, dtype=np.complex128)
        # cos(z u) for complex z, vectorised over z
        zu = np.multiply.outer(z, u)
        return 2.0 * (np.cos(zu) @ pw)

    return xi_stage


def real_zero_count(f, T: float, npts: int = 20001):
    t = np.linspace(0.0, T, npts)          # Xi_U is even; count on [0, T] and double
    v = f(t).real
    s = np.sign(v)
    changes = np.sum(s[1:] * s[:-1] < 0)
    # a zero exactly at 0 would show as v[0] == 0; Xi_U(0) > 0 here
    return 2 * int(changes)


def winding_count(f, T: float, H: float, n_side: int = 4000, max_refine: int = 6):
    """Zeros inside the rectangle [-T,T] x [-H,H] via the argument principle.
    Adaptive refinement until every consecutive phase step is < pi/2."""
    corners = [complex(-T, -H), complex(T, -H), complex(T, H), complex(-T, H), complex(-T, -H)]
    total = 0.0
    for a, b in zip(corners[:-1], corners[1:]):
        n = n_side
        for _ in range(max_refine):
            zs = a + (b - a) * np.linspace(0.0, 1.0, n + 1)
            vals = f(zs)
            ph = np.angle(vals)
            d = np.diff(ph)
            d = (d + PI) % (2 * PI) - PI
            if np.max(np.abs(d)) < PI / 2:
                break
            n *= 2
        total += np.sum(d)
    return int(round(total / (2 * PI)))


def locate_offaxis(f, T: float, H: float, nx: int = 1200, ny: int = 81):
    """Coarse grid minima of |Xi_U| off the real axis (Im z > 0.05), refined by Newton."""
    xs = np.linspace(-T, T, nx)
    ys = np.linspace(0.05, H, ny)
    X, Y = np.meshgrid(xs, ys)
    Z = X + 1j * Y
    A = np.abs(f(Z.ravel())).reshape(Z.shape)
    cands = []
    for i in range(1, ny - 1):
        for j in range(1, nx - 1):
            a = A[i, j]
            if a < A[i - 1, j] and a < A[i + 1, j] and a < A[i, j - 1] and a < A[i, j + 1]:
                cands.append(Z[i, j])
    zeros = []
    h = 1e-6
    for z0 in cands:
        z = z0
        for _ in range(60):
            fz = f(np.array([z]))[0]
            dfz = (f(np.array([z + h]))[0] - f(np.array([z - h]))[0]) / (2 * h)
            if dfz == 0:
                break
            step = fz / dfz
            z = z - step
            if abs(step) < 1e-13:
                break
        if abs(f(np.array([z]))[0]) < 1e-9 and abs(z.imag) > 1e-6 and abs(z.real) <= T and abs(z.imag) <= H:
            if all(abs(z - w) > 1e-6 for w in zeros):
                zeros.append(z)
    return sorted(zeros, key=lambda w: (w.real, w.imag))


def main():
    H = 2.0
    print("Phi(0) =", float(phi(np.array([0.0]))[0]), "  Phi(1) =", float(phi(np.array([1.0]))[0]),
          "  Phi(2) =", float(phi(np.array([2.0]))[0]))
    print()
    print(f"{'U':>5} {'T':>5} | {'zeros in rect':>13} {'real zeros':>10} {'excess':>7} | verdict")
    print("-" * 78)
    results = []
    for U in (0.25, 0.5, 0.75, 1.0, 1.5, 2.0):
        f = make_stage(U)
        for T in (40.0, 100.0):
            nrect = winding_count(f, T, H)
            nreal = real_zero_count(f, T)
            excess = nrect - nreal
            verdict = "REAL-ROOTED in window" if excess == 0 else f"NON-REAL zeros: {excess}"
            print(f"{U:5.2f} {T:5.0f} | {nrect:13d} {nreal:10d} {excess:7d} | {verdict}")
            results.append((U, T, nrect, nreal, excess))
    print()
    # locate the off-axis zeros for the informative rows
    for U in (0.25, 0.5, 1.0):
        f = make_stage(U)
        zs = locate_offaxis(f, 100.0, H)
        print(f"U = {U}: off-axis zeros in |Re z|<=100, 0.05<Im z<=2 (upper half listed): {len(zs)}")
        for z in zs[:12]:
            print(f"    z = {z.real:10.4f} {z.imag:+8.4f} i   |Xi_U| = {abs(f(np.array([z]))[0]):.1e}")
        if len(zs) > 12:
            print(f"    ... ({len(zs) - 12} more)")
    print()
    # the tracking window: where does the stage leave Xi?  |Xi_U(t) - Xi_{U'}(t)| on the real axis
    fU = make_stage(1.0)
    fV = make_stage(3.0)
    t = np.linspace(0, 100, 2001)
    d = np.abs(fU(t) - fV(t))
    print("U=1 vs U=3 on the real axis: max |diff| on [0,100] =", f"{d.max():.2e}",
          " (argmax t =", f"{t[np.argmax(d)]:.1f})")
    print("|Xi_3(t)| at t = 14.13, 21.02, 50, 100:",
          [f"{abs(fV(np.array([x]))[0]):.2e}" for x in (14.134725, 21.022040, 50.0, 100.0)])


if __name__ == "__main__":
    main()
