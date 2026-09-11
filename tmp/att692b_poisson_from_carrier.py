"""Reconstruct η off the carrier from ON-CARRIER data only: the half-plane Poisson integral
   η(σ+it) = (1/π) ∫ (σ−½)/((σ−½)² + (t−τ)²) · η(½+iτ) dτ, using η(½+iτ) only.
   Test point s₁ = 1 + 2πi/log 2 (alternation zero) and control s₂ = 1 + 8i (η ≠ 0)."""
import mpmath as mp, numpy as np, time
mp.mp.dps = 15
t0 = time.time()
taus = np.arange(-400, 400, 0.02)
line = np.array([complex(mp.altzeta(0.5 + 1j*float(tau))) for tau in taus])   # ON-CARRIER readout only
print("line readout evaluated at %d points in %.0fs" % (len(taus), time.time()-t0))
def poisson(sigma, t):
    ker = (sigma - 0.5) / ((sigma - 0.5)**2 + (t - taus)**2) / np.pi
    return np.trapz(ker * line, taus)
s1 = complex(1, float(2*mp.pi/mp.log(2))); s2 = complex(1, 8.0)
for s, name in ((s1, "s1 = 1 + 2πi/log2 (alternation point)"), (s2, "s2 = 1 + 8i (control)")):
    rec = poisson(s.real, s.imag); direct = complex(mp.altzeta(s))
    print("%-42s  Poisson from carrier: %s   direct η: %s   |diff| = %.3f" % (name, np.round(rec, 4), np.round(direct, 4), abs(rec - direct)))
