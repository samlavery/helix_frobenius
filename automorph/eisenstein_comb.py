"""The Eisenstein mirror comb: 27.a = eta(3t)^2 eta(9t)^2, CM by Z[zeta_6] --
the carrier's own mu_6 field as a CM medium.

Role swap vs 32.a:  prime 3 is now BAD (additive) -> ln3, ln9 DEAD (ln9 was
32.a's brightest line);  prime 2 is now GOOD INERT (theta_2 = pi/2) -> the
2-tower ALTERNATES:  ln2 dead, ln4 ALIVE (0.5), ln8 dead, ln16 alive (0.125).
Split primes (p = 1 mod 3): ln7 alive (|a_7|=1), ln13 alive (|a_13|=5).
Inert k=1 (p = 2 mod 3): ln2, ln5, ln11 dead.

Anomaly cross-check: 32.a showed a forbidden bright line at its bad-prime
window (ln4).  Here the bad tower is 3 -- if a bad-prime ghost exists, ln3/ln9
should light up despite zero Euler content.
"""
import math

import numpy as np


def eta_sq_dilated(N, d):
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


def a27(N):
    A = eta_sq_dilated(N, 3)
    B = eta_sq_dilated(N, 9)
    L = 1
    while L < 2 * N:
        L *= 2
    prod = np.round(np.fft.irfft(np.fft.rfft(A, L) * np.fft.rfft(B, L), L)[:N])
    a = np.zeros(N + 1)
    a[1:] = prod[:N]
    assert a[1] == 1 and a[2] == 0 and a[3] == 0 and a[5] == 0 and a[9] == 0, "support/bad tower"
    assert a[4] == -2, a[4]                       # Hecke: a_4 = a_2^2 - 2 (good inert 2)
    assert abs(a[7]) == 1 and abs(a[13]) == 5, (a[7], a[13])   # split primes, 4p = L^2+27M^2
    assert a[8] == 0 and a[16] == 4, (a[8], a[16])             # 2-tower: a_8=0, a_16=-2*a_4=4
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1)
    lam[1:] = a[1:] / np.sqrt(n[1:])
    return lam


N = 480000
lam = a27(N)
print("27.a coefficients verified: support 1 mod 3; a_4=-2, a_8=0, a_16=2 (alternating 2-tower);")
print("|a_7|=1, |a_13|=5 (split); 3-tower all zero (additive)")

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
targets = [("ln2", 2, "DEAD (inert k=1)"), ("ln3", 3, "DEAD (bad) <- ghost check"),
           ("ln4", 4, "ALIVE 0.5 (inert k=2)"), ("ln5", 5, "DEAD (inert k=1)"),
           ("ln7", 7, "alive (split, |a|=1)"), ("ln8", 8, "DEAD (inert k=3)"),
           ("ln9", 9, "DEAD (bad) <- was 32.a's top line"), ("ln11", 11, "DEAD (inert k=1)"),
           ("ln13", 13, "ALIVE (split, |a|=5)"), ("ln16", 16, "alive 0.125 (inert k=4)"),
           ("ln18*", 18, "null"), ("ln21*", 21, "null"), ("ln25", 25, "alive weak (k=2)")]
print(f"[27.a Eisenstein mirror comb] span {t_hi-t_lo:.0f}, resolution {res:.3f}")
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
