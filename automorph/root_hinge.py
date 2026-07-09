"""Read the root number from the line phase (the weld-ray pinning test).

Prediction (from the weld anti-involution, = UnitMidpoint.mirror_fixed_iff with
Delta = arg eps): for primitive chi, Lambda(1/2+it, chi) = eps * conj(Lambda(1/2+it, chi))
on the whole line, so its phase is PINNED:

    arg Lambda(1/2+it, chi)  =  arg(eps)/2   (mod pi),  for ALL t.

The fiber-side measurable: psi(t) := [arg F(t) + theta_chi(t)] mod pi should be a
CONSTANT between vanishings (jumping by pi at each), equal to arg(eps)/2, where
theta_chi is the exact Gamma-phase

    theta_chi(t) = (t/2) ln(q/pi) + Im log Gamma( (1/2 + a)/2 + it/2 ),   a = parity.

Ground truth: eps = tau(chi) / (i^a sqrt(q)) from the Gauss sum — pure arithmetic,
no L-function.  For self-dual chi, eps = 1 and the pinning degenerates to psi = 0
(the real Hardy Z): the hinge first-cell offset from pi/2 IS arg(eps)/2.

Cases: chi3 (real control, expect 0), chi5 order 4 + its conjugate (expect +-arg eps/2),
chi7 order 6.  Oracle column: mpmath Hurwitz L at two off-zero ordinates (final
verification only).
"""
import math

import numpy as np
from scipy.special import loggamma

N, dy, Y1 = 12000, 0.005, 60.0


def char_values(q, g, order, conj=False):
    vals = np.zeros(q, dtype=np.complex128)
    x = 1
    for k in range(q - 1):
        vals[x] = np.exp(2j * math.pi * (k % order) / order)
        x = (x * g) % q
    return np.conj(vals) if conj else vals


CASES = [
    ("chi3 (real)", 3, 2, 2, False),
    ("chi5 ord4", 5, 2, 4, False),
    ("conj chi5", 5, 2, 4, True),
    ("chi7 ord6", 7, 3, 6, False),
    ("conj chi7", 7, 3, 6, True),
]

print(f"{'case':>12} {'a':>2} {'|eps|':>7} {'pred=argeps/2':>14} {'measured':>9} {'circ sd':>8} "
      f"{'hinge(t=1)':>10} {'oracle':>8} {'n zeros':>7}")

for name, q, g, order, conj in CASES:
    vals = char_values(q, g, order, conj)
    a = 0 if abs(vals[q - 1] - 1.0) < 1e-9 else 1
    tau = sum(vals[r] * np.exp(2j * math.pi * r / q) for r in range(1, q))
    eps = tau / ((1j ** a) * math.sqrt(q))
    pred = (np.angle(eps) / 2) % math.pi

    n = np.arange(1, N + 1, dtype=np.int64)
    c = vals[n % q]
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = c * w * n.astype(np.float64) ** (-0.5)
    ln = np.log(n.astype(np.float64))

    ny = int(Y1 / dy) + 1
    ys = dy * np.arange(ny)
    z = amp.copy()
    step = np.exp(-1j * dy * ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum()
        z *= step
    absF = np.abs(F)

    theta = (ys / 2) * math.log(q / math.pi) + np.imag(loggamma((0.5 + a) / 2 + 1j * ys / 2))
    psi = np.mod(np.angle(F) + theta, math.pi)

    med = float(np.median(absF))
    mask = absF > 0.5 * med          # keep points well away from vanishings
    zc = int(np.sum((absF[1:-1] < absF[:-2]) & (absF[1:-1] < absF[2:]) & (absF[1:-1] < 0.2 * med)))

    zbar = np.mean(np.exp(2j * psi[mask]))          # circular stats on the mod-pi angle
    meas = (np.angle(zbar) / 2) % math.pi
    csd = math.sqrt(max(0.0, -0.5 * math.log(max(abs(zbar), 1e-300)))) / 1.0

    j1 = int(round(1.0 / dy))                       # hinge-side reading at t = 1
    hinge = psi[j1]

    import mpmath as mp
    mp.mp.dps = 30
    def L_or(t):
        s = mp.mpf("0.5") + 1j * mp.mpf(t)
        return complex(q ** (-s) * mp.fsum([vals[r] * mp.zeta(s, mp.mpf(r) / q) for r in range(1, q)]))
    to = 17.3
    tho = (to / 2) * math.log(q / math.pi) + float(np.imag(loggamma((0.5 + a) / 2 + 1j * to / 2)))
    orac = (np.angle(L_or(to)) + tho) % math.pi

    def dpi(x, y):
        d = abs(x - y) % math.pi
        return min(d, math.pi - d)

    print(f"{name:>12} {a:>2} {abs(eps):>7.4f} {pred/math.pi:>13.4f}p {meas/math.pi:>8.4f}p "
          f"{csd/math.pi:>7.4f}p {hinge/math.pi:>9.4f}p {orac/math.pi:>7.4f}p {zc:>7}"
          f"   [d(meas,pred)={dpi(meas,pred)/math.pi:.4f}p]")

print()
print("If d(meas,pred) ~ 0 in every row and the conjugate rows are mirror images, the root")
print("number is read from the line phase — the weld ray realized (mirror_fixed_iff, Delta=arg eps).")
