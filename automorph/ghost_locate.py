import math, sys
import numpy as np
sys.path.insert(0, "tmp")

def spectrum(lam, N, t_lo, t_hi, dy):
    n = np.arange(1, N + 1, dtype=np.float64)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0/np.clip(1.0 - u*u, 1e-300, None)), 0.0)
    amp = lam[1:N+1] * w * n**-0.5
    ln = np.log(n)
    ny = int((t_hi - t_lo)/dy) + 1
    z = amp * np.exp(-1j*t_lo*ln); step = np.exp(-1j*dy*ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum(); z *= step
    x = np.log(np.maximum(np.abs(F), np.percentile(np.abs(F), 1.0))); x -= x.mean()
    P = np.abs(np.fft.rfft(x*np.hanning(len(x))))**2
    freq = 2*math.pi*np.fft.rfftfreq(len(x), d=dy)
    return freq, P

def peaks_in(freq, P, lo, hi):
    sel = (freq >= lo) & (freq <= hi)
    idx = np.where(sel)[0]
    out = []
    med = np.median(P[sel])
    for i in idx[1:-1]:
        if P[i] > P[i-1] and P[i] > P[i+1] and P[i] > 20*med:
            # parabolic interpolation on log power
            y0, y1, y2 = np.log(P[i-1]), np.log(P[i]), np.log(P[i+1])
            d = 0.5*(y0-y2)/(y0-2*y1+y2)
            out.append((freq[i] + d*(freq[1]-freq[0]), P[i]/med))
    return out

from cm_comb import a32
lam32 = a32(560000)
f, P = spectrum(lam32, 560000, 50.0, 150.0, 0.01)
print("32.a ghost region [1.20, 1.70]  (ln4=1.3863, pi/2=1.5708, ln5=1.6094):")
for om, h in peaks_in(f, P, 1.20, 1.70):
    print(f"    peak at omega = {om:.4f}   height {h:.0f}x")

from eisenstein_comb import a27
lam27 = a27(480000)
f, P = spectrum(lam27, 480000, 50.0, 150.0, 0.01)
print("27.a ghost region [1.90, 2.30]  (ln7=1.9459, ln8=2.0794, 2pi/3=2.0944, ln9=2.1972):")
for om, h in peaks_in(f, P, 1.90, 2.30):
    print(f"    peak at omega = {om:.4f}   height {h:.0f}x")
