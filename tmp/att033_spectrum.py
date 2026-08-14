#!/usr/bin/env python3
"""
Attempt 033 v2 — verify the derived spectral kernel and data-validate the Z-assembly.

Derived analytically (contour integration, one-sided transforms):
  I(v) = int_0^inf [e^{-(u+iv)L} - e^{-2(u+iv)L}]/(u+iv)^2 du,
  Ihat(omega) = 0 for omega > -L;  Ihat(-Omega) = 2*pi*[(Omega-L)_+ - (Omega-2L)_+]/Omega.
GATE A: quadrature-phi -> FFT -> compare to the formula.
GATE B: Z(t) = -(1/(pi L)) * Im sum_gamma I(t-gamma) over the cached zeros (window),
        compare int Z^2/T against att030's measured int (S-P_x)^2/T at matching x:
        L = log x. (att030: x=1000 -> 2pi^2 c_R = 1.053 over [1000,19000].)
        NOTE exact normalization: S = P + Z with Z as above (identity (15) integrated),
        so int Z^2 should REPRODUCE att030's remainder (up to the pole/trivial terms).
"""
import numpy as np
import time

# ---- GATE A ----
def phi_quad(vgrid, L, n=60000):
    U = 50.0/L
    u = (np.arange(n)+0.5)*(U/n)
    out = np.empty(len(vgrid))
    for i, v in enumerate(vgrid):
        w = u + 1j*v
        out[i] = np.imag(np.sum((np.exp(-w*L) - np.exp(-2*w*L))/w**2)*(U/n))
    return out

L = 3.0
n = 2**16
V = 80.0
v = (np.arange(n) - n/2)*(2*V/n)
v[np.abs(v) < 1e-12] = 1e-9
t0 = time.time()
phi = phi_quad(v, L, n=20000)
dv = 2*V/n
om = np.fft.fftshift(np.fft.fftfreq(n, d=dv))*2*np.pi
# I(v) complex: phi = Im I. Compute complex I for the transform of I itself:
def I_quad_complex(vgrid, L, n=20000):
    U = 50.0/L
    u = (np.arange(n)+0.5)*(U/n)
    out = np.empty(len(vgrid), dtype=complex)
    for i, vv in enumerate(vgrid):
        w = u + 1j*vv
        out[i] = np.sum((np.exp(-w*L) - np.exp(-2*w*L))/w**2)*(U/n)
    return out
I = I_quad_complex(v, L)
ftI = np.fft.fftshift(np.fft.fft(np.fft.ifftshift(I)))*dv
def Ihat_formula(omega, L):
    Om = -omega
    out = np.zeros_like(Om)
    m = Om > L
    out[m] = 2*np.pi*(np.minimum(Om[m]-L, L))/Om[m]
    return out
pred = Ihat_formula(om, L)
sel = (np.abs(om) < 25) & (np.abs(om) > 0.5)
err = np.max(np.abs(ftI[sel].real - pred[sel]))/np.max(pred)
errim = np.max(np.abs(ftI[sel].imag))/np.max(pred)
print(f"GATE A: max rel err (Re) = {err:.3e},  stray Im = {errim:.3e}  [{time.time()-t0:.0f}s]", flush=True)

# ---- GATE B ----
REPO = "/Users/samuellavery/work/helix_frobenius"
zeros = np.sort(np.load(f"{REPO}/tmp/att019_zeros_to20k.npy"))
T0, T1 = 1000.0, 19000.0
x = 1000.0
Lx = np.log(x)
dt = 0.02
ts = np.arange(T0, T1, dt)
# Z(t) = -(1/(pi*Lx)) * Im sum_gamma I(t-gamma); profile has long 1/v-ish reach:
# evaluate by FFT-convolution: place delta at each zero on the grid, convolve with Im I.
t0 = time.time()
grid = np.zeros(len(ts))
idx = np.searchsorted(ts, zeros[(zeros > T0-100) & (zeros < T1+100)])
np.add.at(grid, np.clip(idx, 0, len(ts)-1), 1.0)
# profile on symmetric grid
M = 2**19
Vmax = M//2*dt
vv = (np.arange(M) - M//2)*dt
vv[np.abs(vv) < 1e-12] = 1e-9
prof = phi_quad(vv, Lx, n=4000)      # Im I on the grid
# convolve (linear, via FFT with zero padding)
K = int(2**np.ceil(np.log2(len(ts)+M)))
Fg = np.fft.rfft(grid, K)
Fp = np.fft.rfft(np.fft.ifftshift(np.pad(prof, (0, K-M))), K)  # center profile at 0
Z = np.fft.irfft(Fg*Fp, K)[:len(ts)]*(-1.0/(np.pi*Lx))
# subtract mean-drift: Z should be mean ~ 0 over the window after the density part —
# the identity's pole+trivial terms are tiny; the profile's step-part vs density: the
# raw sum contains the N(t)-step content; S-P also contains it. Compare directly:
Zc = Z - np.mean(Z)
print(f"GATE B: int Z^2/T = {np.mean(Zc**2):.5f}  -> 2pi^2 * that = {2*np.pi**2*np.mean(Zc**2):.3f}"
      f"   (att030 target: 1.053 at x=1000)   [{time.time()-t0:.0f}s]", flush=True)
