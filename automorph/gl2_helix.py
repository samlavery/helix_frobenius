"""The GL(2) helix built literally: SU(2) rotors on the carrier, trace readout.

The lifted-representation claim (FIBER_DYNAMICS section 4): the helix IS the representation;
the 1D L-function is its character.  For GL(2) that means the medium at prime p is not a
phase e^{i a_p} but an SU(2) CONJUGACY CLASS M_p = diag(alpha_p, beta_p), alpha = e^{i theta_p},
beta = conj(alpha) (det = 1: the Frobenius conjugate-pair law made local at every prime), and
everything downstream is forced:

  (1) Ramanujan-Deligne = REALITY of the clock angle: |lambda_p| <= 2  <=>  theta_p real.
  (2) The p-power ladder = SU(2) characters: lambda(p^k) = tr Sym^k M_p = U_k(cos theta_p)
      (Chebyshev-II) — verified EXACTLY against the eta^24 tau values.
  (3) The Euler factor = the rotor's characteristic determinant:
      sum_k lambda(p^k) x^k = 1/det(I - M_p x).
  (4) The full fiber = the trace of the monodromy bank: rebuilding ALL lambda(n) from the
      angles {theta_p} alone reproduces the L-function — same zeros, same everything.

So the "GL(2) helix" needs no new geometry: the carrier is unchanged (pi/3 cells, area law);
only the transverse fiber is C^2 with the rotor acting, and the readout is the trace.
"""
import sys

import numpy as np

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")
from focal_closure import delta_lambda

NMAX = 20000
lam = delta_lambda(NMAX)                # exact tau(n)/n^{11/2}, indexed by n (lam[0] = 0)

primes = [p for p in range(2, NMAX + 1)
          if all(p % q for q in range(2, int(p ** 0.5) + 1))]

# (1) Ramanujan = real angles
viol = [p for p in primes if abs(lam[p]) > 2.0]
print(f"(1) Ramanujan reality: |lambda_p| <= 2 for all {len(primes)} primes <= {NMAX}: "
      f"{'PASS' if not viol else f'VIOLATED at {viol[:5]}'}")
theta = {p: float(np.arccos(np.clip(lam[p] / 2.0, -1, 1))) for p in primes}

# (2) ladder = Chebyshev-II of the angle, exact match at prime powers
err2 = 0.0
for p in primes:
    if p * p > NMAX:
        break
    k, pk = 2, p * p
    while pk <= NMAX:
        th = theta[p]
        Uk = np.sin((k + 1) * th) / np.sin(th) if abs(np.sin(th)) > 1e-12 else (k + 1) * np.cos(k * np.pi if th > 1 else 0)
        err2 = max(err2, abs(lam[pk] - Uk))
        k += 1
        pk *= p
print(f"(2) SU(2) character ladder lambda(p^k) = U_k(cos theta_p): max |err| = {err2:.2e}")

# (3) Euler factor = rotor determinant, spot check at p = 2, x = 0.3
p, x = 2, 0.3
M = np.diag([np.exp(1j * theta[p]), np.exp(-1j * theta[p])])
det_side = 1.0 / np.linalg.det(np.eye(2) - M * x).real
ser_side = sum(lam[p ** k] * x ** k for k in range(0, 9) if p ** k <= NMAX) + \
           sum((np.sin((k + 1) * theta[p]) / np.sin(theta[p])) * x ** k
               for k in range(9, 60))
print(f"(3) Euler factor = 1/det(I - M_p x) at p=2, x=0.3: det {det_side:.10f} "
      f"vs ladder series {ser_side:.10f}  (diff {abs(det_side-ser_side):.1e})")

# (4) rebuild ALL lambda(n) from the angles alone (multiplicativity = tensor of rotors)
lam_geo = np.zeros(NMAX + 1)
lam_geo[1] = 1.0
spf = np.zeros(NMAX + 1, dtype=np.int64)
for p in primes[::-1]:
    spf[p::p] = p
for n in range(2, NMAX + 1):
    p = int(spf[n]); m = n
    k = 0
    while m % p == 0:
        m //= p; k += 1
    th = theta[p]
    Uk = np.sin((k + 1) * th) / np.sin(th) if abs(np.sin(th)) > 1e-12 else 0.0
    lam_geo[n] = lam_geo[m] * Uk
mx = float(np.max(np.abs(lam_geo[1:] - lam[1:])))
print(f"(4) full trace readout: max |lambda_geo(n) - lambda_tau(n)| over n <= {NMAX}: {mx:.2e}")

# the readout shadow: fiber from ANGLES ONLY locates the same vanishings
n = np.arange(1, NMAX + 1, dtype=np.float64)
u = n / NMAX
w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
amp = lam_geo[1:] * w * n ** (-0.5)
ln = np.log(n)
dy = 0.01
ys = 9.0 + dy * np.arange(int(6.0 / dy) + 1)
z = amp * np.exp(-1j * ys[0] * ln)
step = np.exp(-1j * dy * ln)
F = np.empty(len(ys), dtype=np.complex128)
for j in range(len(ys)):
    F[j] = z.sum()
    z *= step
absF = np.abs(F)
zs = [f"{ys[j] - (F[j] / ((F[j+1] - F[j-1]) / (2*dy))).real:.4f}"
      for j in range(1, len(ys) - 1)
      if absF[j] < absF[j-1] and absF[j] < absF[j+1] and absF[j] < 0.2]
print(f"(5) vanishings from the rotor bank in t in [9,15]: {zs}")
print("    (Delta's first two zeros: 9.2224, 13.9075 — LMFDB)")
print()
print("The GL(2) helix is the SAME carrier with a C^2 fiber: per-prime SU(2) rotors")
print("(det 1 = conjugate strands), ladder = characters, L = trace. Langlands data")
print("IS the geometry; the 1D object is its shadow.")
