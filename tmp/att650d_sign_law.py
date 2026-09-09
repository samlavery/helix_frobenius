#!/usr/bin/env python3
"""
att650d — the sign structure of ledger 650 as an IDENTITY in S(t).  (Sam: "turn it into a law";
"S(t) turns them all into a positive?")

For a simple zero ρ_n = ½ + iγ_n on the line, all lower zeros on the line and simple:
   η(ρ_n−2)/η′(ρ_n) = i · A_n · exp(i(π S(γ_n⁺) + Φ_n)),   A_n > 0,
   A_n = |(1−ρ)(2−ρ)|/4π² · |B_n| · |ζ(ρ+2)| / |Z′(γ_n)|,  B_n = (1−2^{3−ρ})/(1−2^{1−ρ}),
   Φ_n = arg B_n + arg[(γ²−¾) + 2iγ] − arg ζ(5/2+iγ),
   S(γ_n⁺) = n − 1 − ϑ(γ_n)/π.
Derivation: ζ(ρ−2) = χ(ρ−2) ζ(3−ρ) = χ(ρ−2) conj ζ(ρ+2); χ(ρ−2)/χ(ρ) = −(1−ρ)(2−ρ)/4π²; χ(ρ) = e^{−2iϑ};
ζ′(ρ) = −i e^{−iϑ} Z′(γ); sgn Z′(γ_n) = (−1)^{n−1}; e^{−iϑ(γ_n)} = (−1)^{n−1} e^{iπS(γ_n⁺)}.
The grown fiber's event is displaced from ρ_n by δ_Z = Z^{−2} · i A_n e^{i(πS+Φ)}: its σ-component is
−Z^{−2} A_n sin(π S(γ_n⁺) + Φ_n) — a sine mode on the cell, inward across the interior, vanishing at the
edges, flipped only when S puts the event outside its cell by more than Φ_n/π.
PRE-REGISTERED
  R1 identity: |LHS − RHS|/|LHS| < 1e−10 for all 1000 zeros.
  R2 the sign exceptions of att650c are exactly the zeros with sin(πS(γ⁺) + Φ) < 0.
  R3 |Φ_n| < 1 for all 1000 zeros (bounded phase from the conduction clock, the Euler product at 5/2, 2/γ).
"""
import math, time, cmath
import mpmath as mp
mp.mp.dps = 20
out = open("tmp/att650d_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
t0 = time.time()
worst = 0.0; exc = []; mismatch = 0; maxphi = 0.0; Svals = []
for n in range(1, 1001):
    r = mp.zetazero(n); g = r.imag
    lhs = complex(mp.altzeta(r - 2) / mp.diff(mp.altzeta, r))
    B = complex((1 - 2 ** (3 - r)) / (1 - 2 ** (1 - r)))
    q = complex((g * g - mp.mpf(3) / 4) + 2j * g)
    z2 = complex(mp.zeta(r + 2))
    Zp = float(mp.diff(mp.siegelz, g))
    S = float(n - 1 - mp.siegeltheta(g) / mp.pi)
    A = abs(q) / (4 * math.pi ** 2) * abs(B) * abs(z2) / abs(Zp)
    Phi = cmath.phase(B) + cmath.phase(q) - cmath.phase(z2)
    rhs = 1j * A * cmath.exp(1j * (math.pi * S + Phi))
    rel = abs(lhs - rhs) / abs(lhs); worst = max(worst, rel)
    maxphi = max(maxphi, abs(Phi)); Svals.append(S)
    pred_neg = math.sin(math.pi * S + Phi) > 0
    if (lhs.real < 0) != pred_neg: mismatch += 1
    if lhs.real >= 0: exc.append((n, float(g), S, Phi, float(math.sin(math.pi * S + Phi))))
say("att650d (%.0fs): identity max relative error over 1000 zeros = %.2e  → R1 %s" % (time.time() - t0, worst, "CONFIRMED" if worst < 1e-10 else "DID NOT HOLD"))
say("sign predicted by sin(πS(γ⁺)+Φ) > 0 disagrees with the measured sign at %d zeros → R2 %s" % (mismatch, "CONFIRMED" if mismatch == 0 else "DID NOT HOLD"))
say("max |Φ_n| over 1000 zeros = %.3f rad → R3 %s" % (maxphi, "CONFIRMED" if maxphi < 1 else "DID NOT HOLD"))
say("S(γ_n⁺) over 1000 zeros: min %.3f max %.3f ; outside (0,1): %d" % (min(Svals), max(Svals), sum(1 for s in Svals if not 0 < s < 1)))
say("the exceptions (positive real part = event displaced OUTSIDE, σ > ½):")
for n, g, S, Phi, sn in exc:
    say("   zero #%d γ=%.3f  S(γ⁺)=%+.3f  Φ=%+.3f  sin(πS+Φ)=%+.3f  %s" % (n, g, S, Phi, sn, "Gram-law violation (S outside (0,1))" if not 0 < S < 1 else "inside its cell; Φ pushed it over"))
