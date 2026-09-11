#!/usr/bin/env python3
"""att697 — what the best UNCONDITIONAL tools give against the agreement.
   Needed: ∫₀ᵀ N_off ≤ εT for every ε (⟹ N_off ≡ 0, since N_off is a nondecreasing integer:
   ∫₀ᵀ N_off ≥ N_off(T/2)·T/2).
   Available unconditionally: a positive proportion of zeros on the line — Levinson 1/3, Conrey 0.4058,
   Bui–Conrey–Young 0.4105, Pratt–Robles–Zaharescu–Zeindler 0.4191, Anthropic 2026 > 2/3.
   Then N_off(T) ≤ (1−κ)N(T), N(T) ≈ (T/2π)log(T/2πe), so ∫₀ᵀ N_off ≲ (1−κ)T²log T/(4π)."""
import numpy as np
out = open("tmp/att697_results.txt","w")
def say(*a):
    s=" ".join(str(x) for x in a); print(s); out.write(s+"\n")
def N(T): return T/(2*np.pi)*np.log(T/(2*np.pi*np.e)) + 7/8
for kappa,name in ((1/3,"Levinson 1974"),(0.4058,"Conrey 1989"),(0.4191,"PRZZ 2020"),(2/3,"Anthropic 2026")):
    for T in (1e3, 1e6, 1e12):
        bound = (1-kappa)*np.trapz([N(t) for t in np.linspace(1,T,20001)], np.linspace(1,T,20001))
        say("%-16s κ=%.4f  T=%.0e:  best unconditional ∫₀ᵀN_off ≤ %.3e   needed ≤ εT (ε=0.01: %.3e)   ratio %.2e"
            % (name, kappa, T, bound, 0.01*T, bound/(0.01*T)))
say("")
say("N_off nondecreasing integer ⇒ ∫₀ᵀ N_off ≥ N_off(T/2)·(T/2); so ∫₀ᵀN_off ≤ εT ∀ε ⟺ N_off ≡ 0 ⟺ RH.")
