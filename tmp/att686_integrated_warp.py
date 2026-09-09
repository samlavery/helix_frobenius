#!/usr/bin/env python3
"""att686 — the integrated warp driver. S₁(T) = ∫₀ᵀ S(t)dt with S = N − 1 − ϑ/π (the warp's driver), computed EXACTLY from
   the ledger (∫N = Σ_{γ≤T}(T−γ), ∫ϑ by quadrature), against the radial log-mass at the top height
   R(T) = (1/π)∫_{½}^{∞} log|ζ(σ+iT)| dσ  (Littlewood's identity: S₁(T) = R(T) + O(1)).
   PRE-REGISTERED: S₁(T) − R(T) is a CONSTANT to 1e-3 across T (the O(1) is exact), and |S₁| ≤ 2 at all four heights."""
import mpmath as mp
mp.mp.dps = 20
out = open("tmp/att686_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
zeros = []
j = 1
while True:
    g = float(mp.zetazero(j).imag)
    if g > 420: break
    zeros.append(g); j += 1
for T in (50.5, 100.3, 200.7, 400.2):
    intN = sum(T - g for g in zeros if g <= T)                       # ∫₀ᵀ N(t) dt
    intTheta = mp.quad(mp.siegeltheta, [0, T/4, T/2, 3*T/4, T])       # ∫₀ᵀ ϑ
    S1 = intN - T - intTheta/mp.pi
    R = mp.quad(lambda s: mp.log(abs(mp.zeta(s + 1j*T))), [0.5, 0.75, 1, 1.5, 2, 4, 8, 40]) / mp.pi
    say("T=%6.1f  N(T)=%3d  S₁(T)=∫₀ᵀS = %+.5f   radial log-mass R(T)=(1/π)∫_{½}^{∞}log|ζ(σ+iT)|dσ = %+.5f   S₁−R = %+.5f"
        % (T, sum(1 for g in zeros if g <= T), S1, R, S1 - R))
