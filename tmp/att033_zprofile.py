#!/usr/bin/env python3
"""
Attempt 033 — the exact per-zero profile of Selberg's zero term Z(t), its spectrum,
and the band/tail mass split (the analytical spine of the explicit-c_R derivation).

From Selberg's unconditional identity (Simonic (15)):
  Z-contribution of an on-line zero at ordinate gamma, v := t - gamma, L := log x:
    I(v) = int_0^inf [e^{-(u+iv)L} - e^{-2(u+iv)L}] / (u+iv)^2 du
         = e^{-iLv}/(iv) + L*E1(iLv) - e^{-2iLv}/(iv) - 2L*E1(2iLv)
    phi(v) = Im I(v);  Z(t) = -(1/(pi L)) sum_rho phi-type terms.
Checks:
  A. closed form vs direct quadrature.
  B. phi's Fourier transform: support/decay; mass split at |omega| <= l (the band,
     l = log(T/2pi)) for L = theta*l: the fraction beyond omega = l as a function of theta.
     (M-frequency units: omega in t-space; band alpha<=1 <=> omega <= l.)
  C. the per-zero L2 norm int phi^2 dv (the diagonal unit of the mean square).
Note: phi has a +-pi/2-step DC part (the counting step) which pairs with the density
subtraction; for the spectral split analysis we work with phi' (the derivative kernel) or
window the step — here: analyze psi(v) := phi(v) - (pi/2)*sgn-step-part... simplest:
numerically use phi_odd-step-removed: phi(v) - step*arctan-model? We handle it by
differentiating: the SPECTRUM of phi is phihat(w) = (step-pole at 0) + regular part;
the mean-square pair-analysis uses the regular part against F; compute |phihat|^2*w^2
(the S'-normalized reading) which kills the pole cleanly.
"""
import numpy as np
from scipy.special import exp1
import time

def Iclosed(v, L):
    w1 = 1j*L*np.asarray(v, dtype=complex)
    w2 = 2j*L*np.asarray(v, dtype=complex)
    return (np.exp(-w1)/(1j*v) + L*exp1(w1) - np.exp(-w2)/(1j*v) - 2*L*exp1(w2))

def Iquad(v, L, U=None, n=200000):
    if U is None:
        U = 60.0/L
    u = (np.arange(n)+0.5)*(U/n)
    w = u + 1j*v
    return np.sum((np.exp(-w*L) - np.exp(-2*w*L))/w**2)*(U/n)

L = 3.0
print("GATE A: closed form vs quadrature (L=3):", flush=True)
for v in [0.13, 0.77, 2.4, -1.1]:
    a, b = Iclosed(v, L), Iquad(v, L)
    print(f"  v={v:+5.2f}: closed {a:.6f}  quad {b:.6f}  |diff| {abs(a-b):.2e}", flush=True)

# B: spectrum. Work with the S'-normalized reading: the pair kernel in the mean square of
# Z is |phihat(w)|^2; phi = step + regular. Numerically: compute phi on a wide grid,
# subtract the exact step (pi/2)*sgn(v)*[leading]: the step coefficient: phi(v->inf) ->
# Im[e^{-iLv}/(iv) ...] -> 0?? check asymptotics numerically first.
theta_list = [1/3, 1/2]
l = 9.0   # log(T/2pi) at T ~ 5e4-ish; results scale in omega/L so theta is what matters
for theta in theta_list:
    L = theta*l
    V = 400.0/L
    n = 2**20
    v = (np.arange(n) - n/2)*(2*V/n)
    v[v == 0] = 1e-9
    phi = np.imag(Iclosed(v, L))
    # asymptotic step: measure plateau at large |v|
    plat_p = np.mean(phi[int(n*0.95):])
    plat_m = np.mean(phi[:int(n*0.05)])
    step = (plat_p - plat_m)/2
    sgn = np.sign(v)
    reg = phi - (plat_p+plat_m)/2 - step*sgn
    # spectrum of the regular part + the step handled analytically (its transform 2step/(iw))
    dv = 2*V/n
    w = np.fft.fftshift(np.fft.fftfreq(n, d=dv))*2*np.pi
    ft = np.fft.fftshift(np.fft.fft(np.fft.ifftshift(reg)))*dv
    ft_full = ft + step*2/(1j*np.where(np.abs(w) < 1e-12, 1e-12, w))  # step transform
    # the S'-normalized pair reading: |w*phihat(w)|^2 (kills the 1/w pole)
    P2 = np.abs(w*ft_full)**2
    band = np.abs(w) <= l
    tail = np.abs(w) > l
    mband, mtail = np.trapezoid(P2[band], w[band]), np.trapezoid(P2[tail], w[tail])
    print(f"theta={theta:.3f} (L={L:.2f}, l={l}): step={step:.4f} (pi/2={np.pi/2:.4f}) "
          f" mass beyond band = {mtail/(mband+mtail)*100:.2f}%"
          f"  [spectral edge ~ 2L = {2*L:.1f} vs l = {l}]", flush=True)
    # where does the spectrum die: report mass beyond 2L*(1+eps)
    beyond2L = np.abs(w) > 2*L*1.05
    print(f"    mass beyond 2.1L: {np.trapezoid(P2[beyond2L], w[beyond2L])/(mband+mtail)*100:.3f}%", flush=True)
