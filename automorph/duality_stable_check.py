"""Robust, normalization-free check of the property the carrier's FE weld actually consumes.

The weld is CHANNEL-LOCAL: helix<->anti-helix conjugation pairs channel lambda with lambda^{-1}.
The completed FE closes iff every channel's dual is present -> the local factor prod(1-lambda_j x) is
SELF-INVERSIVE (palindromic): det = prod lambda_j = 1  AND  e_1 = e_{N-1} (tr = tr of inverse), etc.
This is exactly 'the weight multiset is duality-stable', and it is what the audit says the FE needs --
NOT the Chebyshev pattern. Check it for a Chebyshev family, a NON-Chebyshev tensor, and a scramble.
"""
import math, numpy as np
import tate_twist_clock as T

def esym(lams):
    # elementary symmetric polys e_0..e_N of the multiset (coeffs of prod (x - lam))
    p = np.poly(lams)  # [1, -e1, e2, -e3, ..., (-1)^N eN]
    N = len(lams)
    e = [((-1)**k) * p[k] for k in range(N+1)]
    return e  # e[0]=1, e[1]=sum, ..., e[N]=prod

def palindromic(lams, tol=1e-9):
    e = esym(lams)
    N = len(lams)
    detone = abs(e[N] - 1) < tol
    sym = max(abs(e[k] - e[N-k]) for k in range(N+1))   # self-inversive: e_k = e_{N-k}
    return detone, sym

def theta_of(p, A):
    c = T.ap(p, A)/(2*math.sqrt(p)); return math.acos(max(-1.0,min(1.0,c)))

A11, A37 = T.CURVES["E11"][0], T.CURVES["E37"][0]
primes = [int(p) for p in T.sieve(200) if p not in (11,37)][:12]

def chan_A(p):  # Sym^3(E11): Chebyshev string
    t=theta_of(p,A11); return np.exp(1j*np.array([3*t,t,-t,-3*t]))
def chan_B(p):  # tensor E11 x E37: 2-D grid (NON-Chebyshev)
    t,f=theta_of(p,A11),theta_of(p,A37); return np.exp(1j*np.array([t+f,t-f,-t+f,-t-f]))
def chan_C(p):  # scramble: not closed under negation
    return np.exp(1j*np.array([((p*b*2654435761)%9973)/9973.0*2*math.pi for b in (1,2,3,4)]))

def is_chebyshev(p):  # is the tensor multiset actually a Sym^3 string {3a,a,-a,-3a}? (angles ratio 3:1)
    t,f=theta_of(p,A11),theta_of(p,A37)
    ang=sorted([abs(t+f),abs(t-f)])
    return abs(ang[1]-3*ang[0])<1e-6 if ang[0]>1e-6 else False

print("duality-stability (self-inversive local factor) — the property the FE weld consumes")
print("="*84)
for tag, ch, expect in [("(A) Sym^3(E11)  Chebyshev ", chan_A, "palindromic"),
                        ("(B) E11(x)E37   tensor    ", chan_B, "palindromic"),
                        ("(C) scramble              ", chan_C, "NOT")]:
    dets=[]; syms=[]
    for p in primes:
        d,s = palindromic(ch(p)); dets.append(d); syms.append(s)
    alldet=all(dets); maxsym=max(syms)
    verdict = "SELF-INVERSIVE (duality-stable)" if (alldet and maxsym<1e-8) else "NOT self-inversive"
    print(f"{tag}: det=1 all primes={alldet}  max|e_k-e_(N-k)|={maxsym:.2e}  -> {verdict}")
cheb = all(is_chebyshev(p) for p in primes)
print("-"*84)
print(f"Is the tensor (B) secretly a Chebyshev/Sym string?  angles in ratio 3:1 at all primes = {cheb}")
print("  (False => B is a genuinely non-symmetric-power duality-stable multiset.)")
