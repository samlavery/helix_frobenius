#!/usr/bin/env python3
"""
Attempt 029 stage 3 — the unconditional row bound C_BS.

Want: even band-limited k (supp khat in [-1,1] scaled) with k(x) >= f(x) := x^{-2} 1_{|x|>=1}
AND k(x) >= 0 for |x| < 1 (F >= 0 everywhere makes k >= f^+ = max(f,0) the requirement;
inside the band f = 0 so k >= 0 there).  Then, unconditionally (BGSTB F >= 0 + band formula):

    int_1^inf F(x)/x^2 dx  <=  int_R F(x) k(x) dx  =  khat-spike-reading + int_{-1}^{1} k(x)|x|-part
                            =  khat(0)... careful: the ROLES ARE SWAPPED vs the certificate LP:
here k lives in x-space (where F lives) and the band-limitation is on khat (u-side, support
[-1,1] in the SCALED u/l variable => the x-side evaluation uses Montgomery/BGSTB with primes <= T).

Evaluation (T -> inf):  int F k = k(0)*... NO: int F(x)k(x)dx with F = T^{-2|x|}logT-spike + |x| on
band... F's band form holds for |x| <= 1 only — but int_R F k needs F EVERYWHERE.  THE TRICK is the
other way: expand int F k = sum over zero pairs of khat-evaluations: khat supported [-1,1] means the
pair-sum only reads band frequencies: int_R F(x) k(x) dx = (1/N) sum_{rho,rho'} khat-transform-reading
w(...) — the standard Montgomery convolution identity:  sum g((gamma-gamma')L/2pi)w = N int ghat F,
i.e. int khat-hat... Concretely with ghat := k (x-space weight), the identity evaluates int k F from
the prime side iff supp(k-inverse-transform) subset [-1,1]:  k must be BAND-LIMITED IN ITS OWN
TRANSFORM. Then

    int_R k(x) F(x) dx = [prime-side evaluation] = k-transform(0)-spike + int k(x)(T^{-2|x|}logT + |x|)dx
                       -> khat-spike-term + int_{-1}^{1} k(x)|x| dx + k(0)*1   (spike mass 1 at x=0)

Wait — the evaluation of int k F for band-limited k: plug the band FORM of F where it holds (|x|<=1)
— k's mass OUTSIDE the band multiplies F-values we do NOT know. THAT is why the majorant must ALSO
be band-limited... but a band-limited k cannot vanish outside... The resolution (standard in Fourier
optimization): int_R F k IS evaluable for band-limited k BECAUSE the pair-sum identity reads k-hat on
[-1,1] only — F's unknown out-of-band values are not consulted; the identity is
    int_R F(x) k(x) dx  =  (1/N) sum_{rho,rho'} T^{...}-pair-sum with weight khat((gamma-gamma')L/2pi)
and the RIGHT side is evaluated by BGSTB from primes: = khat(0)-density-reading... hmm — precisely:
    N int F k dx = sum_{pairs} khat(scaled diff) w  = N [ k(0)... ]
Montgomery: int_{-inf}^{inf} F(x) r(x) dx = sum-pairs rhat(...)/N for rhat = ... — the pair sum is
evaluated when RHAT... I implement the standard normalization numerically instead of re-deriving:
verify on the Fejer anchor: r(x) = (1-|x|)_+ (band-limited transform? (1-|x|)_+ = Fejer = hat of
sinc^2 — its transform IS nonneg with UNBOUNDED support — the roles: Montgomery evaluated
int F(x)(1-|x|)dx over [-1,1]... M's theorem: int_{-1}^{1} F(x) r(x) dx evaluable for ANY nice r
READ ONLY ON [-1,1] (F's band values known pointwise-in-integral!). So int_{|x|<=1} F k is FREE for
any k; the issue is ONLY |x| > 1. A majorant k >= f with k = 0 outside... impossible band-limited.

=> THE CORRECT unconditional row bound: choose r with RHAT... the pair-sum route:
   sum_{rho,rho'} g(scaled-diff) w = N int ghat F   with supp g subset [-1,1]-scaled (primes <= T).
   If ghat(x) >= f(x) for ALL x (majorant IN x-SPACE, transform-side band-limited!)
   then  int f F <= int ghat F = (1/N) sum-pairs g(...)w  = evaluable prime-side = the S(g)-numbers.
   The prime-side value (BGSTB/zeta23 SS5): = N[ghat-spike + int_{-1..1}ghat|x| ... ] NO —
   S(g)-evaluation = N[ ghat(0)-spike-term + int ghat(x)(T^{-2|x|}logT + |x|)1_{|x|<=1} dx ]?? that
   reads ghat only on the band?! But int ghat F needs ghat everywhere... The identity: S(g) = N int
   ghat F EXACTLY (both sides); the prime side evaluates S(g) DIRECTLY (primes n <= e^{L}) without
   knowing F pointwise. So: C_row-bound = [S(g)-prime-side]/N for the majorant ghat >= f.
   And the prime-side value has the SAME shape as every Z-functional here:
       S(g)/N -> ghat(0) + int_{-1}^{1} ghat(x)|x| dx + [T^{-2|x|}-spike correction -> ghat-near-0]
   because the prime side only involves primes <= X = e^{lambda l}, lambda <= 1 — the evaluation IS
   the band functional even though ghat has full support: the OUT-of-band ghat mass costs NOTHING
   on the prime side?!  CHECK against reality: ghat = f-majorant has mass ~2 beyond the band; if the
   prime side didn't see it, C would be tiny and PCC would be nearly free — IMPOSSIBLE. Resolution:
   supp g subset [-1,1]-scaled  <=>  ghat is an ENTIRE band-limited function — then ghat CANNOT
   majorize f while decaying (Paley-Wiener functions can majorize! Beurling-Selberg: type-2pi
   majorants of e.g. sgn, 1_{[a,b]}, with finite integral!). ghat band-limited, ghat >= f pointwise
   on R: EXISTS (f is even, decays; BS-machinery: Graham-Vaaler). The prime-side evaluation of S(g):
   their SS5 with kernel g (u-side, supp [-1,1]-scaled): D-diagonal + O1 + mu^2-terms: value =
   N[ghat-reading of (spike + |x| on [-1,1]) ... + the ANALYTIC continuation... ] — NO: S(g) =
   N int ghat F and the prime side computes it as: (T/pi) sum_n Lambda^2(n)/n g(log n scaled) etc.
   -> in the limit: N[ ghat(0)?? ...]. The honest normalized limit (Montgomery's theorem in
   Goldston's form):  (1/N) S(g) -> int_{-1}^{1} ghat(x) (T^{-2|x|} log T + |x|) dx + ghat-out-part*??
   Known concrete anchor: ghat = Fejer (1-|x|)_+: S/N -> 1 + 1/3 = 4/3: reads spike(1) + ramp(1/3):
   ghat-out-part ABSENT (Fejer supported in band). For ghat with out-of-band support the g-side
   (u-side) support EXCEEDS [-1,1]-scaled => primes beyond T => NOT evaluable. CONCLUSION:
   band-limited-in-transform == ghat entire, and the prime side reads the FULL int ghat F via
   Montgomery's formula extended... I stop the internal debate: the mathematically clean statement
   (Goldston 1988, Carneiro et al 2310.01913) is: for r with supp rhat subset [-1,1]:
       int_R F(x) r(x) dx  =  rhat-prime-side-value  (evaluable), r entire band-limited.
   Majorant r >= f on R, supp rhat in [-1,1]:  C <= prime-side-value = r(0)... the VALUE in the
   standard normalization:  int F r = spike-term r(0)*?? — the spike at x=0 has mass 1: contributes
   r(0); the ramp part: int_{-1}^{1}|x| r(x) dx?? NO — F(x) ~ |x| holds only on [-1,1]; beyond, F is
   unknown, and int F r genuinely includes it. The identity avoids needing it: int F r =
   (1/N)sum-pairs rhat-hat... — FINAL: I implement the VALUE as the pair-sum prime side using
   MONTGOMERY'S OWN FORMULA in reverse on [-1,1] plus the reflection trick... — NO. Numerical
   pragmatism: this script computes  V(r) := r(0) + int_{-1}^{1} r(x)|x| dx + int_{|x|>1} r(x)*Fbar(x) dx
   under the PCC proxy Fbar = 1 for a sanity target, AND the rigorous evaluable functional
   V_rig(r) := r(0)*1 + int_{-1}^{1} r(x) |x| dx  +  [int_{|x|>1} r(x) F(x) dx]  which is NOT
   separately evaluable — hence THIS SCRIPT ONLY establishes the CONDITIONAL (PCC-proxy) size of the
   majorant cost, flagging that the rigorous unconditional row bound via majorants needs the
   pair-sum identity checked at source (Goldston 1988 / CCLM). See ledger 029 for the honest status.
"""
print("Superseded by design discussion — see att029_majorant2.py")
