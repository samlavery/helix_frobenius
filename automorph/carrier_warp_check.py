"""Carrier warp — quick check (owner's idea, 2026-07-03): scale the carrier by a
FLUCTUATING clock value — each number's phasor warped by a wave on its own winding
angle — and verify the two theorem-shaped consequences on a finite bank:

  (1) JACOBI-ANGER SIDEBANDS: the warp A(n) = exp(i eps sin(k Theta(n))) with Theta
      completely additive decomposes EXACTLY into a Bessel-weighted sum of
      character-twisted banks: A(n) = sum_m J_m(eps) chi_m(n), chi_m(n) = e^{imk Theta(n)}
      completely multiplicative.  The warped helix IS a twist family.  (Here
      Theta(n) = (pi/3)*Omega(n), so the sidebands are the Liouville-type twists
      beta^Omega(n), beta = e^{ik pi/3} - the house pi/3 clock.)
  (2) WIGGLE ATTRIBUTION (lock-in): a simple zero of the readout moves under the warp
      exactly as the first-order sideband prediction says:
        droot = -(eps/2) * (F_plus - F_minus) / F'   at the unwarped root
      (from e^{i eps sin} ~ 1 + (eps/2)(e^{i k Th} - e^{-i k Th})).
      A feature that tracks the warp is bank-funded; the instrument measures it.

Bank: smoothed truncated zeta F(s) = sum_{n<=N} a_n n^{-s} e^{-n/N} (never-clip entry),
N >> gamma so the truncation tracks zeta's first zero.  Scope: finite validated
instance; no RH assumed.
"""
import numpy as np
from mpmath import mp, mpc, besselj, findroot

mp.dps = 25
N = 4000
K = 1                      # warp harmonic index (frequency k on the angle clock)
THETA_UNIT = np.pi / 3     # the house clock: Theta(n) = (pi/3) * Omega(n)

# Omega(n) = number of prime factors with multiplicity (completely additive)
Omega = np.zeros(N + 1, dtype=int)
for p in range(2, N + 1):
    if Omega[p] == 0:      # p prime
        pk = p
        while pk <= N:
            for mult in range(pk, N + 1, pk):
                Omega[mult] += 1
            pk *= p
ns = np.arange(1, N + 1)
Th = THETA_UNIT * Omega[1:]
smooth = np.exp(-ns / N)

def bank(s, coeff):
    """F(s) = sum coeff_n n^{-s} e^{-n/N}, s complex (mpmath scalar)."""
    ex = np.array([mp.power(n, -s) for n in ns])
    return complex(np.sum(coeff * smooth * ex))

def bank_mp(s, coeff):
    tot = mpc(0)
    for n, c, w in zip(ns, coeff, smooth):
        tot += c * w * mp.power(int(n), -s)
    return tot

# --- (1) Jacobi-Anger identity on the bank --------------------------------------
eps = 0.15
warp = np.exp(1j * eps * np.sin(K * Th))
M = 8
ja = np.zeros_like(warp, dtype=complex)
for m in range(-M, M + 1):
    ja += complex(besselj(m, eps)) * np.exp(1j * m * K * Th)
print("(1) Jacobi-Anger sideband decomposition of the warp (per-phasor, N=%d):" % N)
print("    max |warp - Bessel-sum(M=%d)| = %.2e" % (M, np.max(np.abs(warp - ja))))
s0 = mpc(mp.mpf(1) / 2, mp.mpf("14.134725"))
Fw = bank_mp(s0, warp)
Fja = bank_mp(s0, ja)
print("    at s=1/2+14.1347i: |F_warped - F_bessel_sum| = %.2e" % abs(Fw - Fja))
print("    => the warped helix IS a Bessel-weighted family of multiplicative twists")

# --- (2) wiggle attribution: zero tracks the sideband prediction -----------------
ones = np.ones(N, dtype=complex)
plus = np.exp(1j * K * Th)          # chi_+ twist (completely multiplicative)
minus = np.exp(-1j * K * Th)        # chi_- twist

f0 = lambda s: bank_mp(s, ones)
root0 = findroot(f0, s0)
h = mpc(0, mp.mpf("1e-8"))
Fp0 = (f0(root0 + h) - f0(root0 - h)) / (2 * h)   # F'
Fplus = bank_mp(root0, plus)
Fminus = bank_mp(root0, minus)

print("(2) wiggle attribution at the first zero (unwarped root %s):" % mp.nstr(root0, 12))
print("      eps      measured droot          predicted -(eps/2)(F+-F-)/F'    |rel err|")
for eps in [0.02, 0.05, 0.1]:
    warp_e = np.exp(1j * eps * np.sin(K * Th))
    fe = lambda s: bank_mp(s, warp_e)
    root_e = findroot(fe, root0)
    droot = root_e - root0
    pred = -(eps / 2) * (Fplus - Fminus) / Fp0
    rel = abs(droot - pred) / abs(droot)
    print("    %5.2f   %s   %s   %.3f" % (eps, mp.nstr(droot, 8), mp.nstr(pred, 8), rel))
print("    (rel err should shrink ~linearly in eps: first-order lock-in law)")
