# AV4: THE CHARGE.  Null (written before running): the excised sum S(T) admits an
# unconditional bound S(T)/N(T) = O(1) with the best known zero-density estimates.
# REJECT the null if sup_sigma [ densityExponent(sigma) + 2S(sigma-1/2) ] > 1,
# because then the bound DIVERGES like a positive power of T.
import numpy as np
S = 1.0   # exponential type of Tsang kernel with band [-1,1]  (BGSTB Lemma 6(b))

def ing(s):  return 3*(1-s)/(2-s)                 # Ingham  1/2<=s<=1
def hux(s):  return 3*(1-s)/(3*s-1)               # Huxley  3/4<=s<=1
def gm(s):   return 30*(1-s)/13                   # Guth-Maynard 2024, 3/4<=s<=1
def dh(s):   return 2*(1-s)                       # Density Hypothesis (Bourgain: known s>=25/32)
def selb(s): return 1 - 0.25*(s-0.5)              # Selberg/Simonic, s in [1/2,0.831]

grid = np.linspace(0.5001, 0.9999, 20001)
best = []
for s in grid:
    cands = [ing(s)]
    if s >= 0.75: cands += [hux(s), gm(s)]
    if s >= 25/32: cands += [dh(s)]
    if s <= 0.831: cands += [selb(s)]
    best.append(min(cands))
best = np.array(best)
tot = best + 2*S*(grid-0.5)
i = int(np.argmax(tot))
print("BEST KNOWN unconditional density exponents, S(T) exponent = dens + 2S(sigma-1/2):")
print(f"  sup = {tot[i]:.4f} at sigma = {grid[i]:.4f}   (need <= 1 for S(T) = O(N(T)))")
print(f"  => S(T)/N(T) >> T^{tot[i]-1:.4f}   DIVERGES")
for s in [0.501,0.51,0.55,0.6,0.7,0.75,0.78125,0.85,0.95]:
    c=[('Ingham',ing(s))]
    if s>=0.75: c+=[('Huxley',hux(s)),('GuthMay',gm(s))]
    if s>=25/32: c+=[('DH/Bourgain',dh(s))]
    if s<=0.831: c+=[('Selberg',selb(s))]
    nm,v = min(c,key=lambda z:z[1])
    print(f"   sigma={s:<8} best={nm:<12}{v:.4f}  +2S(s-1/2)={2*S*(s-0.5):.4f}  total={v+2*S*(s-0.5):.4f}")
print()
print("SELBERG/SIMONIC alone (the only near-line instrument), sup over its range [1/2,0.831]:")
t = selb(grid[grid<=0.831]) + 2*S*(grid[grid<=0.831]-0.5)
print(f"  sup = {t.max():.4f}  => S(T)/N(T) >> T^{t.max()-1:.4f} from the near-line range alone")
print()
print("REQUIREMENT INVERSION: density exponent c with N(sigma,T) << T^{1-c(sigma-1/2)}")
print("  needs c > 2S =", 2*S, "at band S=1;  c > 4 at band S=2 (the CGdL dip band).")
print("  Selberg/Simonic gives c = 1/4.  BGSTB hypothesis (1.6) N=o(T^{2(1-sigma)}) is c = 2 EXACTLY,")
print("  i.e. BGSTB sit exactly at the boundary and need the o(.) to close it.")
print()
print("SIMONIC constant, arithmetic re-derived:")
a = 10395.21
print(f"  N(sigma,T) <= {a} * T^(1-(1/4)(sigma-1/2)) log(T/2) / (2^(1-..)-1),  denom -> 1 at sigma->1/2")
print(f"  N(T) ~ (T/2pi) log T   =>  ratio -> 2*pi*{a} = {2*np.pi*a:.1f} times N(T), one-sided")
print(f"  two-sided (rho <-> 1-conj rho):  {2*2*np.pi*a:.0f}")
import math
print(f"  charge < 1 x N(T) only when e^(-A/4) < 1/{2*2*np.pi*a:.0f}, i.e. A > {4*math.log(2*2*np.pi*a):.2f}")
print(f"  Simonic method floor 3.259 two-sided: {2*2*np.pi*3.259:.2f}; A > {4*math.log(2*2*np.pi*3.259):.2f}")
