#!/usr/bin/env python3
"""att537c — diagnose the P1 failure of att537b: print both Gram matrices at L = 0.3, their
transpose/conjugate relation, the arch/prime split, the zero-side convergence in N, and an
independent mpmath evaluation of one Archimedean line integral."""
import numpy as np, mpmath as mp, sys
sys.path.insert(0, "tmp")
from att537b_phasor_bank_gram_fast import *

L = 0.30; nb = 4; w = L / nb
centres = [-L + w + 2 * w * i for i in range(nb)]
zs = zeros(1000)
np.set_printoptions(precision=4, suppress=True, linewidth=150)

Mz500 = gram_zero_side(centres, w, zs[:500])
Mz = gram_zero_side(centres, w, zs)
print("zero side N=1000:\n", Mz)
print("zero side N=500 (convergence):\n", Mz500)
Mp, nt = gram_prime_side(centres, w, L)
print("prime side:\n", Mp)
print("relFrob(Mp, Mz)   =", np.linalg.norm(Mp - Mz) / np.linalg.norm(Mz))
print("relFrob(Mp, Mz^T) =", np.linalg.norm(Mp - Mz.T) / np.linalg.norm(Mz))
print("relFrob(Mp, conj Mz) =", np.linalg.norm(Mp - Mz.conj()) / np.linalg.norm(Mz))

# arch / prime split of the (0,0) entry, and an mpmath check of the two line integrals
a, b = -0.5, 1.5
t = np.arange(-250, 250 + 0.005, 0.01)
sb = b + 1j * t; sa = a + 1j * t
c = centres[0]
FGb = F_on(c, w, sb) * np.conj(F_on(c, w, 1 - np.conj(sb)))
FGa = F_on(c, w, sa) * np.conj(F_on(c, w, 1 - np.conj(sa)))
Ib = np.trapz(FGb * E(sb), t); Ia = np.trapz(FGa * E(1 - sa), t)
print("entry (0,0): arch_b=%s arch_a=%s  arch=(Ib+Ia)/2pi=%s" % (Ib, Ia, (Ib + Ia) / (2 * np.pi)))
print("             prime part = %s" % (Mp[0, 0] - (Ib + Ia) / (2 * np.pi)).real.__neg__())
print("             zero side  = %s" % Mz[0, 0])

# tail check: integrand size at |t| = 250
print("|FGb*E| at t=250:", abs((FGb * E(sb))[-1]), " at t=100:", abs((FGb * E(sb))[np.searchsorted(t, 100)]))

# mpmath check of Ib via quad (slow but independent) on a coarser tolerance
mp.mp.dps = 15
def Fmp(s):
    f = lambda x: mp.e ** (-1 / (1 - ((x - c) / w) ** 2)) * mp.e ** ((s - mp.mpf(1) / 2) * x) if abs((x - c) / w) < 1 else mp.mpf(0)
    return mp.quad(f, [c - w, c, c + w])
def FGmp(s):
    return Fmp(s) * mp.conj(Fmp(1 - mp.conj(s)))
def Emp(s):
    return 1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2
Ib_mp = mp.quad(lambda tt: FGmp(b + 1j * tt) * Emp(b + 1j * tt), [-60, -20, -5, 0, 5, 20, 60])
print("mpmath Ib over [-60,60]:", Ib_mp, "  numpy Ib over [-60,60]:",
      np.trapz((FGb * E(sb))[np.abs(t) <= 60], t[np.abs(t) <= 60]))
