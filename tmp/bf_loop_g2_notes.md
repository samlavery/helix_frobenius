# Grade-2 recognition loop (Beilinson-Flach) -- citations + carrier translation

Mystery #2 (Recognition), calibration rung B. Companion to `bf_loop_g2.py` /
`bf_loop_g2_results.txt`. Purpose: learn the even-rung **construction arm** (a
regulator, not a height) one grade below where grade 4 must invent it.

## 1. The construction arm, pinned (exact citations)

**Beilinson's theorem (the arm).** Beilinson introduced elements in the higher
Chow group / motivic cohomology of a *product of two modular curves* Y x Y, built
by pushing **modular (Siegel) units** along the diagonal, and related their image
under the Beilinson (Deligne) regulator to the Rankin-Selberg L-value
`L(f (x) g, 2)`, f, g weight-2 newforms.
  - A. Beilinson, *Higher regulators and values of L-functions*, J. Soviet Math.
    30 (1985) 2036-2070 (the original product-of-curves construction).
  - The modern "Beilinson-Flach element" name + Euler-system structure:
    M. Bertolini, H. Darmon, V. Rotger, *Beilinson-Flach elements and Euler
    systems I: syntomic regulators and p-adic Rankin L-series*, J. Algebraic
    Geom. 24 (2015) 355-378 (elements in K_1 of X x X; p-adic syntomic regulator
    = near-central value of Hida's p-adic Rankin L-function).
  - A. Lei, D. Loeffler, S. Zerbes, *Euler systems for Rankin-Selberg
    convolutions of modular forms*, Ann. of Math. 180 (2014) 653-771. **The
    complex Beilinson regulator of the weight-2 Beilinson-Flach element = the
    DERIVATIVE at s = 1**, `L'(f (x) g, 1)` (their sec. on the complex regulator,
    "following an argument of Beilinson").
  - G. Kings, D. Loeffler, S. Zerbes, *Rankin-Eisenstein classes for modular
    forms*, Amer. J. Math. 142 (2020) (arXiv:1501.03289). The **Rankin-Eisenstein
    class interpolates**: cuspidal g -> Beilinson-Flach; **Eisenstein g ->
    Beilinson-Kato = the single-curve Beilinson element**. This is what makes the
    single-modular-curve computation below a genuine (degenerate) grade-2 member,
    not a different object.
  - F. Brunault, M. Chida, *Regulators for Rankin-Selberg products of modular
    forms*, Ann. Math. Quebec 40 (2016) 221-249 (arXiv:1503.04626). Weak Beilinson
    conjecture for the non-critical `L(f (x) g, k+l+2-j)`; requires the nebentypus
    chi_f chi_g nontrivial (their non-vanishing hypothesis holds automatically when
    gcd(N_f, N_g) = 1). **Their worked NUMERICS are all the degenerate corner**:
    Mahler measure of a defining equation of X_1(13) = L'(f_13, 0) (f_13 weight-2,
    level 13, nontrivial character), plus levels 16, 18, 25 -- each a single
    weight-2 form, not a genuine two-cuspform degree-4 product.

**The near-central point, both normalizations.** For two weight-2 forms the RS
convolution `L(f (x) g, s)` is degree 4, motivic weight 2, Gamma factor
`Gamma_C(s) Gamma_C(s-1)`, conductor `Q = N_f^2 N_g^2` (coprime), functional
equation `Lambda(s) = eps Lambda(3-s)`.
  - Classical: center s = 3/2; the two weight-2 forms leave **no critical points**
    (Deligne critical range min+2 <= s <= max+1 is empty for k=l=0) -> the value
    is a regulator, exactly the even-rung signature (matches grade 4). The
    near-central non-critical integers are s = 2 (boundary value) and s = 1.
  - `Gamma_C(s-1)` has a pole at s = 1 -> **trivial zero** `L(f (x) g, 1) = 0`;
    the regulator reads the leading term `L'(f (x) g, 1)`.
  - Analytic (unitary, center 1/2): s_an = s_cl - 1; center 1/2, FE s <-> 1-s;
    Beilinson point s_an = 1 (value) / s_an = 0 (derivative).

**The FE bridge (derived in-house, exact).**
    L'(f (x) g, 1) = eps * (N_f N_g / 4 pi^2) * L(f (x) g, 2).
Residue algebra: Res_{s=1} G = 2 sqrt(Q)/pi, G(2) = Q/(2 pi^3), sqrt(Q)=N_f N_g.
This is the exact even-rung analogue of the single-curve
`L'(E,0) = (N / 4 pi^2) L(E,2)`.

**The computable corner (Rogers-Zudilin, PROVEN, exact constant).**
    m(x + 1/x + y + 1/y + 8) = (24 / pi^2) * L(E_24, 2),   E_24 = 24.2.a.a (cond 24)
  - M. Rogers, W. Zudilin, *From L-series of elliptic curves to Mahler measures*,
    Compositio Math. 150 (2014) 1-27 (arXiv:1012.3036), their eq. (1)
    (m(8) = 4 m(2) = (24/pi^2) L(E_24,2)). This is a genuine Beilinson-regulator =
    L-value theorem: `m(P)` is the geometric regulator of the modular unit `P` on
    the curve, and `= L'(E,0) x rational = (N/4pi^2) L(E,2) x rational`. For k = 8
    the curve `P = 0` misses the torus |x|=|y|=1, so the Mahler integrand is smooth
    and the 2D integral is spectrally convergent -- the cleanest independent
    regulator number available.
  - Conductor-11 companion (house curve, NOT reproduced numerically this session):
    F. Brunault, *Etude de la valeur en s=2 de la fonction L d'une courbe
    elliptique*, thesis Paris 7 (2005), arXiv:math/0602186 -- proved Boyd's
    conductor-11 Mahler-measure identity `~ L'(E_11, 0)`.

## 2. Instance chosen

- **Detection arm, genuine grade-2 object:** f = 11a1, g = 37a1 (the house RS4
  object; the first two legs of the grade-4 quadruple; coprime conductors so
  Q = (11*37)^2 = 165649, both Steinberg at their own bad prime). This is the
  real degree-4 target.
- **Construction arm, the closeable corner:** the conductor-24 Rogers-Zudilin
  identity (the Eisenstein/Beilinson-Kato degeneration = single modular curve),
  chosen because it is the only fully from-scratch-verifiable regulator = L-value
  identity with a smooth (torus-avoiding) integrand and an exact proven constant.

Why not a genuine two-cuspform product for the construction arm: there is **no
from-scratch-verifiable regulator NUMBER** for a degree-4 RS product of two
distinct cuspidal weight-2 forms in the literature. Beilinson-Chida prove the
theorem but their only numerics are the degenerate corner (X_1(13) etc.). Computing
the double regulator integral over (X_0(N))^2 from scratch (double Eisenstein-
Kronecker / Rogers-Zudilin over a product) was beyond this session's compute
budget. This is itself an honest finding about the state of the art.

## 3. L-side value with certificate (detection arm)

Self-certifying completed-L evaluator (H-grid split kernel, adapted from
`center_reading.py`), two anchors: GATE 0 reproduces the house
`L(11a1, 1/2) = 0.2538415` (match 6.5e-6); the conductor-24 identity validates the
SAME evaluator against a proven theorem to 1.55e-5.

    L(11a1 x 37a1, 2)  = 3.46319093        eps = +1 (self-cert: match 3.4e-5
                                            vs wrong-sign 1.8e-2), imag ~ 6e-17
    L'(11a1 x 37a1, 1) = 35.70352601       (route A: Lambda(1)/Res_{s=1}G = the
                                            FE-predicted bridge value)
                       = 35.6838 (route B: independent numeric derivative of
                                  L(s)=Lambda_split(s)/G(s) at the trivial zero;
                                  confirms the trivial-zero + FE structure to 5.5e-4,
                                  limited by the finite-difference step)
    FE bridge  L'(1) = eps (407/4pi^2) L(2): satisfied (route A is this identity).

Constituent single-curve Beilinson values (the degenerate Eisenstein corners):
    L(11a1, 2) = 0.54605695  (eps=+1),   L(37a1, 2) = 0.38158174  (eps=-1).

## 4. Regulator-side status and match outcome

- **Corner (conductor 24): MATCH CLOSES.** Independent geometric regulator
  m(8) = 2.04569627 (2D Mahler integral, grid-refine stable to 4e-16) equals the
  detection-arm (24/pi^2) L(E_24,2) = 2.04572799 to rel 1.55e-5, and the rational
  landing `m(8) pi^2 / L(E_24,2) = 23.9996` -> **24** (the house integer-landing
  discipline). Residual is the evaluator's ~1e-5 floor, not the integral. This is
  the full construction<->detection loop, independently closed, at the even rung.
- **Genuine degree-4 product (11a1 x 37a1): DETECTION ARM COMPLETE, CONSTRUCTION
  ARM OPEN.** The precise failure point: no independent regulator number was
  computed for the two-cuspform product (the geometric side would be the Deligne
  regulator of a Siegel-unit class on X_0(11) x X_0(37), a double Eisenstein-
  Kronecker integral). The L-side (both faces of the near-central point) is
  certified; the FE bridge is verified; but the "recognition" is not closed for the
  genuine object because the construction arm has no from-scratch number to
  recognize against. This is exactly the gap grade 4 will also face, one grade up.

## 5. THE CARRIER TRANSLATION (the actual point of rung B)

What the construction arm looked like operationally, and what grade 4 needs.

The odd-rung (grade 1) loop read a **height**: the modular-parametrization jet,
the drift-pairing *determinant on odd rungs* -- a self-pairing whose leading jet is
`hat h(P)`, a length. The even rung reads a **regulator**: a *volume of the
log/drift channel*, and the operational data is entirely different.

- **The carrier data that plays the regulator role is the log channel = the
  MODULAR UNITS.** In the harmonic-Hodge frame a Hodge class is the rational DC
  mode; **drift = extensions**, and the log/drift channel is precisely where the
  units live (a modular unit is a function with divisor supported at the cusps --
  its `log|u|` is the drift potential). The construction arm is: take two elements
  of the unit/drift channel (u on one carrier, v on the other), form their
  regulator `eta(u,v)` -- the antisymmetrized `log|u| d arg v - log|v| d arg u` --
  and integrate against the RS test form `f (x) g`. On the carrier this is a
  *pairing of two drift channels*, not a self-pairing of a height. The
  even-vs-odd parity law (`dc_channel_iff_even_weight`, Lean-proven) is the same
  fact: even rungs carry the DC/log channel, odd rungs the symplectic/height
  channel. The regulator is the **Gram volume of the drift pairing**, the even-rung
  face of "the central data of Lambda is the Gram data of ONE Hermitian pairing on
  the double helix."

- **Rogers-Zudilin, operationally, is a re-welding of two drift channels into a
  convergent form.** The Mahler integrand `log|x + 1/x + y + 1/y + k|` is a
  `log|unit|` on the 2-torus; the theorem transports it (via the RZ change of
  variables that swaps the two Eisenstein/unit arguments) into `L'(E,0)`. In house
  terms this is the **rail-matching / re-welding move**: the naive single-rail
  reading of the regulator diverges or mis-registers; only the *conjugate-closed /
  harmonically-compatible* pairing of the two log channels registers to the
  L-value. The `k = 8` choice (curve misses the torus) is the even-rung analogue of
  "place the winding off the unit-1 scale so the closure is visible" -- it moves the
  integrand off its singular locus so the drift pairing converges spectrally.

- **The rational (24) is the lane-count of the re-weld**, the even-rung analogue of
  the odd-rung calibrated constant "2" (canonical height = 2 x Neron sum). It is
  the ratio between the geometric normalization of the unit class and the
  automorphic normalization of the L-value -- read off by continued fraction, the
  house integer-landing discipline. It is NOT a period: the period is the explicit
  `pi^2` (the `(2 pi i)^2` twist of `Q(2)`), fixed by the FE, and the rational is
  what remains.

- **What grade 4 needs (the successor).** Grade 4's center is *also* non-critical
  with no Deligne-rational part (GRADE4_PROGRESS: "the unread number is a regulator
  volume"), and its FE sheet, Q, and eps are already pinned. The grade-2 lesson is
  that the even-rung value is `pi-power x rational x (Gram volume of a drift
  pairing)`, and the drift pairing is built from **unit/log-channel classes paired
  place-by-place** (tropical reduction-graph Green's functions at bad primes +
  archimedean Rogers-Zudilin re-weld at infinity). Grade 4's remaining assembly --
  "drift determinant (ledger) = tropical admissible pairing (Sum tau = 2/3, C_5
  m_2 = 5/36) + archimedean remainder" -- is the exact structural successor: replace
  grade 2's single Beilinson-Flach drift pairing by grade 4's higher drift
  determinant, keep the tropical + archimedean split, and land the rational off the
  same integer-landing discipline. The construction arm grade 4 must invent is the
  Siegel-unit class on the fourfold product whose regulator volume is this
  determinant; grade 2 shows its carrier form is a **conjugate-closed pairing of
  the modular-unit (drift) channel against the RS test form**, with the value
  = pi-power x rational x regulator, no height anywhere.
