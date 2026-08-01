"""Phasor-native re-do of the clock-cell laws: the bank, not the ledger.

Carrier-frame bank at height t (canonical phasors, sigma=1/2, phase = log_entry mode
rotated by the clock): site-n phasor 2*n^(-1/2)*cos(theta(t) - t*ln n), n <= m(t) =
floor(sqrt(t/2pi)); resultant Z(t) = DC + subBank + remainder, DC = 2*cos(theta(t)).

At a zero the bank closes exactly: DC = -(subBank + R), i.e. with tau the event's
clock phase and k its Gram cell,

    (-1)^(k+1) * cos(pi*tau) = beta,   beta := (subBank + R)/2.

So every law measured in the readout chart (pinning, centering, floors, occupancy)
must be CARRIED by the n>=2 phasors -- the Euler stream.  Measured here:
  1. anchor: bank closure at all cached zeros (RS with C0 remainder)
  2. the slaving identity: cos-readout tau vs sub-bank beta, per (s,k) class
  3. defect episodes = sub-bank exceedance (|beta| near/over 1)
  4. floors: sub-bank sign at the mid-cell DC-null decides k=0 / k=1 / k=2
  5. exploratory: mu6 sector structure of the complex sub-bank phasor at zeros
"""

import bisect
import numpy as np
from scipy.special import loggamma

ZC = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"
GC = "/Users/samuellavery/work/helix_frobenius/tmp/gram_cache.txt"
zeros = [float(x) for x in open(ZC).read().split()]
gram = [float(x) for x in open(GC).read().split()][0::2]

def theta(t):
    t = np.asarray(t, dtype=float)
    return np.imag(loggamma(0.25 + 0.5j * t)) - 0.5 * t * np.log(np.pi)

def theta_prime(t):
    return 0.5 * np.log(np.asarray(t) / (2 * np.pi))

TWO_PI = 2 * np.pi

def bank_parts(t):
    """(DC, subBank, remainder, complex subPhasor) of the carrier-frame bank at t."""
    th = float(theta(t))
    m = int(np.floor(np.sqrt(t / TWO_PI)))
    n = np.arange(2, m + 1, dtype=float)
    phases = th - t * np.log(n)
    sub = 2.0 * np.sum(np.cos(phases) / np.sqrt(n)) if m >= 2 else 0.0
    subC = np.sum(np.exp(1j * phases) / np.sqrt(n)) if m >= 2 else 0.0 + 0.0j
    p = np.sqrt(t / TWO_PI) - m
    c2 = np.cos(TWO_PI * p)
    if abs(c2) > 0.05:
        C0 = np.cos(TWO_PI * (p * p - p - 1.0 / 16.0)) / c2
        R = (-1.0) ** (m + 1) * (TWO_PI / t) ** 0.25 * C0
        Rok = True
    else:
        R, Rok = 0.0, False
    return 2.0 * np.cos(th), sub, R, Rok, subC

M = max(n for n in range(len(gram) - 1) if gram[n + 1] <= zeros[-1] - 5.0)
zarr = np.array(zeros)
zin = zarr[(zarr > gram[0]) & (zarr <= gram[M])]
ph = theta(zin) / np.pi
cell = np.floor(ph).astype(int)
tau = ph - cell
s = np.array([bisect.bisect_right(zeros, gram[n]) - 1 - n for n in range(M + 1)])
k = np.bincount(cell, minlength=M)

# ---- 1+2: bank closure and the slaving identity at every zero ----
DCs, subs, Rs, Roks, subCs = [], [], [], [], []
for g in zin:
    dc, sub, R, Rok, subC = bank_parts(g)
    DCs.append(dc); subs.append(sub); Rs.append(R); Roks.append(Rok); subCs.append(subC)
DCs, subs, Rs = np.array(DCs), np.array(subs), np.array(Rs)
Roks = np.array(Roks); subCs = np.array(subCs)

closure = DCs + subs + Rs
env = (TWO_PI / zin) ** 0.75
print("== 1. bank closure at %d zeros (C0 remainder where stable: %d) ==" %
      (len(zin), Roks.sum()))
print("RMS(DC + subBank + R) = %.4f  (stable-R only: %.4f;  ~t^-3/4 envelope RMS %.4f)"
      % (np.sqrt((closure**2).mean()),
         np.sqrt((closure[Roks]**2).mean()), np.sqrt((env**2).mean())))

beta = (subs + Rs) / 2.0
E = -((-1.0) ** (k[cell] if False else cell)) * np.cos(np.pi * tau)  # -(-1)^k cos(pi tau)
E = -((-1.0) ** cell) * np.cos(np.pi * tau)
resid = E - beta
print("\n== 2. slaving identity: -(-1)^k cos(pi tau) = beta(subBank) ==")
print("identity residual: RMS %.4f (stable-R: %.4f)   corr(E, beta) = %.6f"
      % (np.sqrt((resid**2).mean()), np.sqrt((resid[Roks]**2).mean()),
         np.corrcoef(E, beta)[0, 1]))
print("mean beta = %+.5f  (centering law: E[beta]=0 <-> mean tau = 1/2)" % beta.mean())
print("P(|beta| <= 1/2) = %.4f  (middle-third occupancy, phasor form)" %
      (np.abs(beta) <= 0.5).mean())

# per-class: defect events carry large sub-bank projection
print("\n== 3. defect episodes = Euler-stream exceedance ==")
sc = s[:-1]
for sv, kv in [(0, 1), (1, 1), (-1, 2), (0, 2)]:
    mcells = np.nonzero((sc == sv) & (k == kv))[0]
    if mcells.size == 0:
        continue
    msk = np.isin(cell, mcells)
    b = np.abs(beta[msk])
    print("  (s=%+d,k=%d): events %4d   |beta|: mean %.3f  min %.3f  max %.3f"
          % (sv, kv, int(msk.sum()), b.mean(), b.min(), b.max()))

# ---- 4. floors: sub-bank sign at the mid-cell DC-null ----
print("\n== 4. mid-cell DC-null: sub-bank decides the cell class ==")
zmid = np.empty(M)
for n in range(M):
    target = (n + 0.5) * np.pi
    r = 0.5 * (gram[n] + gram[n + 1])
    for _ in range(50):
        step = (float(theta(r)) - target) / float(theta_prime(r))
        r -= step
        if abs(step) < 1e-11:
            break
    zmid[n] = r
signed = np.empty(M)   # (-1)^n * (subBank + R) at the DC-null
okmid = np.zeros(M, dtype=bool)
for n in range(M):
    dc, sub, R, Rok, _ = bank_parts(zmid[n])
    signed[n] = (-1.0) ** n * (sub + R)
    okmid[n] = Rok
print("(dc at null: max|DC| = %.2e — the DC phasor is off)" %
      max(abs(bank_parts(zmid[n])[0]) for n in range(0, M, 97)))
for kv in (0, 1, 2, 3):
    mk = k == kv
    if not mk.any():
        continue
    v = signed[mk]
    print("  k=%d cells (%4d): (-1)^n Z(null): mean %+.3f   P(>0) = %.4f"
          % (kv, int(mk.sum()), v.mean(), (v > 0).mean()))

# ---- 5. mu6 sectors of the complex sub-bank phasor at zeros (exploratory) ----
print("\n== 5. mu6 sectors of arg(subPhasor) at zeros (exploratory) ==")
args = np.angle(subCs)          # in (-pi, pi]
sect = np.floor(((args + np.pi) / (np.pi / 3.0))).astype(int) % 6
counts = np.bincount(sect, minlength=6) / len(sect)
print("sector occupancy (pi/3 bins): " + "  ".join("%.4f" % c for c in counts))
chi2 = len(sect) * 6 * np.sum((counts - 1 / 6.0) ** 2)
print("chi2 vs uniform (5 dof): %.2f" % chi2)
print("\ndone.")
