import math
import numpy as np

def eta_sq_dilated(N, d):
    c = np.zeros(N)
    k = 0
    while True:
        done = True
        for kk in (k, -k) if k else (0,):
            m = d * (kk * (3*kk - 1)//2)
            if 0 <= m < N: c[m] += (-1)**kk; done = False
        if k and done: break
        k += 1
    L = 1
    while L < 2*N: L *= 2
    f = np.fft.rfft(c, L)
    return np.round(np.fft.irfft(f*f, L)[:N])

N = 480000
A = eta_sq_dilated(N,3); B = eta_sq_dilated(N,9)
L = 1
while L < 2*N: L *= 2
prod = np.round(np.fft.irfft(np.fft.rfft(A,L)*np.fft.rfft(B,L), L)[:N])
a = np.zeros(N+1); a[1:] = prod[:N]
nn = np.arange(0, N+1, dtype=np.float64)
lam = np.zeros(N+1); lam[1:] = a[1:]/np.sqrt(nn[1:])

n = np.arange(1, N+1, dtype=np.float64)
u = n/N
w = np.where(u<1.0, np.exp(1.0-1.0/np.clip(1.0-u*u,1e-300,None)), 0.0)
amp = lam[1:]*w*n**-0.5
ln = np.log(n)
t_lo, dy = 50.0, 0.01
ny = 10001
z = amp*np.exp(-1j*t_lo*ln); step = np.exp(-1j*dy*ln)
F = np.empty(ny, dtype=np.complex128)
for j in range(ny):
    F[j] = z.sum(); z *= step
x = np.log(np.maximum(np.abs(F), np.percentile(np.abs(F),1.0))); x -= x.mean()
P = np.abs(np.fft.rfft(x*np.hanning(len(x))))**2
freq = 2*math.pi*np.fft.rfftfreq(len(x), d=dy)
sel = (freq>=1.85)&(freq<=2.35)
med = np.median(P[sel])
print("27.a region [1.85, 2.35]  (ln7=1.9459, ln8=2.0794, 2pi/3=2.0944, ln9=2.1972); local maxima >5x:")
idx = np.where(sel)[0]
for i in idx[1:-1]:
    if P[i]>P[i-1] and P[i]>P[i+1] and P[i]>5*med:
        y0,y1,y2 = np.log(P[i-1]),np.log(P[i]),np.log(P[i+1])
        d = 0.5*(y0-y2)/(y0-2*y1+y2)
        print(f"    omega = {freq[i]+d*(freq[1]-freq[0]):.4f}   height {P[i]/med:.0f}x")
