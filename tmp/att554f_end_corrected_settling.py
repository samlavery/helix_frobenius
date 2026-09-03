#!/usr/bin/env python3
"""
att554f — the object-native form WITH THE END TERM CARRIED: does the prime-clock resultant settle
right of balance as the bank grows?

  C_x(s) := Σ_{n≤x} Λ(n) n^{−s}  −  x^{1−s}/(1−s)          (clock resultant minus the pole read at the front)

Truncated explicit formula: C_x(s) = −ζ′/ζ(s) − Σ_ρ x^{ρ−s}/(ρ−s) + Σ_k x^{−2k−s}/(2k+s).  Under RH the
zero-side remainder has modulus ≲ x^{½−σ}·log²x → 0 for σ > ½ (settles); an off-line zero at β > σ
contributes x^{β−σ} (never settles).  The RAW sum Σ_{n≤x} Λ(n) n^{−s} does not settle anywhere in the
strip (the END term grows like x^{1−σ}): the END-term DC law.
PRE-REGISTERED: at σ = 0.6, 0.75, 0.9 and t = 12, 30, 60, |C_x(s) + ζ′/ζ(s)| decreases with x over
x = 10³…10⁶ with fitted slope in log x within ±0.15 of (½ − σ); the RAW sum's error grows with
slope ≈ 1 − σ.  L-values (ζ′/ζ) are used only as the settling target (verification).
"""
import math, numpy as np, mpmath as mp
mp.mp.dps = 20
X = 1_000_000
lam = np.zeros(X + 1)
sieve = np.ones(X + 1, dtype=bool); sieve[:2] = False
for p in range(2, int(X**0.5) + 1):
    if sieve[p]: sieve[p*p::p] = False
for p in np.nonzero(sieve)[0]:
    q = p
    while q <= X: lam[q] = math.log(p); q *= p
nn = np.arange(1, X + 1, dtype=float); logn = np.log(nn)
xs = [1_000, 3_000, 10_000, 30_000, 100_000, 300_000, 1_000_000]
print("END-corrected settling of the prime-clock resultant right of balance (bank grows to front x)")
print(" σ     t    | slope of log|C_x + ζ′/ζ| vs log x   predicted ½−σ | slope RAW   predicted 1−σ |  |err| at x=10^6 (corrected / raw)")
ok = True
for sig in (0.6, 0.75, 0.9):
    for t in (12.0, 30.0, 60.0):
        s = complex(sig, t)
        target = -complex(mp.zeta(s, derivative=1)/mp.zeta(s))
        terms = lam[1:]*np.exp(-s*logn)          # Λ(n) n^{-s}
        cum = np.cumsum(terms)
        errc, errr = [], []
        for x in xs:
            raw = cum[x - 1]
            end = x**(1 - s)/(1 - s)
            errc.append(abs(raw - end - target)); errr.append(abs(raw - target))
        lx = np.log(xs)
        sc = np.polyfit(lx, np.log(errc), 1)[0]; sr = np.polyfit(lx, np.log(errr), 1)[0]
        flag = abs(sc - (0.5 - sig)) <= 0.15
        ok &= flag
        print(" %.2f  %4.0f  |   %+.3f                 %+.3f   %s |  %+.3f         %+.3f      |  %.2e / %.2e"
              % (sig, t, sc, 0.5 - sig, "ok " if flag else "OFF", sr, 1 - sig, errc[-1], errr[-1]))
print("pre-registered slope law (corrected sum settles like x^{½−σ}): %s" % ("CONFIRMED" if ok else "DIED"))
