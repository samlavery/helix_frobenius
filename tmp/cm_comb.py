"""The CM comb: the conjugate-pair (two-clock) structure at right angles.

Level-32 CM curve 32.a (y^2 = x^3 - x), form eta(4t)^2 eta(8t)^2.  For every
p = 3 mod 4 the Satake pair sits at theta_p = pi/2 exactly (a_p = 0):
    k=1 clock  amplitude |2cos(theta)|   = 0     -> ln p   DEAD
    k=2 clock  amplitude |2cos(2theta)|/2 = 1    -> ln p^2 FULL STRENGTH
For p = 1 mod 4 the k=1 clock is alive (a_p = 2a from p = a^2+b^2).
Bad prime 2 (additive): all 2-power lines dead.

Predicted comb:  ln2 ln3 ln4 ln7 ln8 ln11 DEAD;  ln5 ln13 ln9 ALIVE (ln9 from
the silent-at-k=1 prime 3!); composites ln18 ln21 null.  No single-clock medium
can light ln9 while ln3 is dark.
"""
import math
import sys

import numpy as np


def eta_sq_dilated(N, d):
    """(prod (1-q^{dn}))^2 as a dense length-N array."""
    c = np.zeros(N, dtype=np.float64)
    k = 0
    while True:
        done = True
        for kk in (k, -k) if k else (0,):
            m = d * (kk * (3 * kk - 1) // 2)
            if 0 <= m < N:
                c[m] += (-1) ** kk
                done = False
        if k and done:
            break
        k += 1
    L = 1
    while L < 2 * N:
        L *= 2
    f = np.fft.rfft(c, L)
    return np.round(np.fft.irfft(f * f, L)[:N])


def a32(N):
    A = eta_sq_dilated(N, 4)
    B = eta_sq_dilated(N, 8)
    L = 1
    while L < 2 * N:
        L *= 2
    prod = np.round(np.fft.irfft(np.fft.rfft(A, L) * np.fft.rfft(B, L), L)[:N])
    a = np.zeros(N + 1)
    a[1:] = prod[:N]
    assert a[1] == 1 and a[2] == 0 and a[3] == 0 and a[7] == 0 and a[11] == 0, "comb coeffs"
    assert abs(a[5]) == 2 and abs(a[13]) == 6 and a[9] == -3, (a[5], a[13], a[9])
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1)
    lam[1:] = a[1:] / np.sqrt(n[1:])
    return lam


N = 560000
lam = a32(N)
print("coefficients verified: a2=a3=a7=a11=0, |a5|=2, a9=-3, |a13|=6 (CM comb structure)")

t_lo, t_hi, dy = 50.0, 150.0, 0.01
n = np.arange(1, N + 1, dtype=np.float64)
u = n / N
w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
amp = lam[1:] * w * n ** (-0.5)
ln = np.log(n)
ny = int((t_hi - t_lo) / dy) + 1
taus = t_lo + dy * np.arange(ny)
z = amp * np.exp(-1j * t_lo * ln)
step = np.exp(-1j * dy * ln)
F = np.empty(ny, dtype=np.complex128)
for j in range(ny):
    F[j] = z.sum()
    z *= step

absF = np.abs(F)
x = np.log(np.maximum(absF, np.percentile(absF, 1.0)))
x -= x.mean()
P = np.abs(np.fft.rfft(x * np.hanning(len(x)))) ** 2
freq = 2 * math.pi * np.fft.rfftfreq(len(x), d=dy)
res = 2 * math.pi / (t_hi - t_lo)
targets = [("ln2", 2, "dead(bad)"), ("ln3", 3, "DEAD k=1"), ("ln4", 4, "dead(bad)"),
           ("ln5", 5, "ALIVE"), ("ln7", 7, "DEAD k=1"), ("ln9", 9, "ALIVE k=2!"),
           ("ln11", 11, "DEAD k=1"), ("ln13", 13, "ALIVE"), ("ln18*", 18, "null"),
           ("ln21*", 21, "null"), ("ln25", 25, "k=2 of alive p"), ("ln49", 49, "ALIVE k=2")]
print(f"[32.a CM comb] span {t_hi-t_lo:.0f}, resolution {res:.3f}")
print(f"   {'line':>6} {'peak/bg':>12}   prediction")
for name, nn, pred in targets:
    om = math.log(nn)
    pk = np.abs(freq - om) < max(0.012, 2.0 * res)
    bg = (np.abs(freq - om) > 0.09) & (np.abs(freq - om) < 0.28)
    for _, n2, _ in targets:
        if n2 != nn:
            bg &= np.abs(freq - math.log(n2)) > 0.05
    ratio = float(P[pk].max() / np.median(P[bg]))
    print(f"   {name:>6} {ratio:>12.1f}   {pred}")
