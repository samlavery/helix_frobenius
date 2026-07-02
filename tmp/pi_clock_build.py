"""Build 27.a coefficients once for span [50,450], N ~ 4.2M. Save lambda to tmp/."""
import time
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
    assert a[4] == -2, a[4]
    assert abs(a[7]) == 1 and abs(a[13]) == 5, (a[7], a[13])
    assert a[8] == 0 and a[16] == 4, (a[8], a[16])
    # extra bad-tower check deep in
    assert a[81] == 0 and a[27] == 0, ("3-tower", a[27], a[81])
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1)
    lam[1:] = a[1:] / np.sqrt(n[1:])
    return lam

# N chosen so highest freq (a few pi) is well-resolved at t_hi=450.
# Rule of thumb from spec: N = 30 * 27 * (450/(2*pi))^2
N = int(30 * 27 * (450.0 / (2 * np.pi))**2)
print("N =", N)
t0 = time.time()
lam = a27(N)
print("built lambda in %.1fs" % (time.time() - t0))
# Save the amplitude-weighted vector components needed for the sweep:
# amp = lam[1:] * bump_window * n^{-0.5}; but window depends on N only, so precompute amp & ln.
n = np.arange(1, N + 1, dtype=np.float64)
u = n / N
w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
amp = (lam[1:] * w * n**(-0.5)).astype(np.float64)
ln = np.log(n)
# amp is float64 ~ 4.2M * 8 bytes = 34MB; ln same. Save as float64 for phase accuracy.
np.save("pi_clock_amp.npy", amp)
np.save("pi_clock_ln.npy", ln)
print("saved amp, ln; nonzero amp entries:", int((amp != 0).sum()))
