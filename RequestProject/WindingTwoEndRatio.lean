import RequestProject.TwoEndedSymmetry

/-!
# The winding brought into the two-ended fiber: the multiplicative face, unwarped and warped

`TwoEndedFiber` balances the ADDITIVE bank `F_Z` against its reflected end.  The constitution's third
field (HP_SKELETON §0a step 3) is the carrier winding, `wind(mn) = wind(m) + wind(n)`: read through the
winding, the fiber is the Euler product.  At a finite front `x` with real coefficients `c` its log-face is
`L_x s = Σ_{1 ≤ n < x} c n · n^{−s}` (Riesz-tapered Euler product: `c n = (1 − log n / log x)₊ · Λ(n) / log n`),
and the fiber WARP of ledgers 554c/560 (closed form clocks + END + anti-end + remainder, never clocks alone)
adds a warp potential `P`: the warped log-face is `L_x + P`.  For the pole's Riesz kernel
`K_R(u) = (x^u − 1)/(L u²)` the warp is `P = Π_x`, `Π_x′(s) = K_R(1 − s)`,
`Π_x(s) = −Ei(L(1 − s)) + (x^{1−s} − 1)/(L(1 − s))` (att707); the exponential integral is not in Mathlib, so
`P` is a parameter here and every identity holds for any `P`.

Everything is stated for a general log-face `Λ`: the face `exp Λ`, the two-ended face
`exp Λ(s) + χ(s) exp Λ(1 − s)` with `χ = feFactor⁻¹` ζ's functional-equation factor (Mathlib's
`riemannZeta_one_sub` normalisation, `ζ(s) = χ(s) ζ(1 − s)`), and the two-end ratio
`R = χ(s) exp Λ(1 − s) / exp Λ(s)`.  Pairing the pure Euler face with ζ's factor is the measured object of
att706/att707; the η-face `(1 − 2^{1−s}) exp Λ` paired with `χ_η` has the same ratio, since `χ_η` absorbs the
conduction factor.  (The first build of this file paired the pure face with `χ_η`; corrected, RH_LEDGER 707.)

Because a face never vanishes, a balanced event is exactly `R = −1` (`twoEndedFace_eq_zero_iff`), and the
modulus of `R` is EXACT and explicit in the windings (`log_norm_faceRatio`):
  `log ‖R s‖ = −log ‖feFactor s‖ + Re Λ(1 − s) − Re Λ s`.
For the unwarped bank the slope across the axis is the bank side of the density register
(`hasDerivAt_re_logEulerBank_diff`):
  `∂_σ [Re L_x(1 − s) − Re L_x s]|_{σ = ½} = 2 Σ_{n<x} c n · log n · n^{−½} cos(t log n)`,
i.e. `2 Σ w_x(n) Λ(n) n^{−½} cos(t log n)` for the Riesz coefficients; with `∂_σ log ‖χ‖ = −2ϑ′` on the axis
this is `−2π (D_{R,x}(t) − END_x(t))` in the notation of RH_LEDGER 568, and the warp `Π_x` supplies exactly
`−2π END_x` (att707: the warped slope equals `−2π D_{R,x}` to `2e−15`).  Far-side domination of the ratio
forces every balanced event onto the axis (`re_eq_half_of_twoEndedFace_eq_zero`).
Measured: unwarped, domination fails only in the pole's shadow (att706); warped, the first-order slope is
negative at every height and front tested, and every balanced event is on the axis (att707).
-/

open Complex Filter Topology Set Finset

namespace CriticalLinePhasor.GrownFiber

/-- ζ's functional-equation factor, `χ = feFactor⁻¹`: `ζ(s) = χ(s) ζ(1 − s)`. -/
noncomputable def chiZeta (s : ℂ) : ℂ := (feFactor s)⁻¹

/-- The det-1 pair of ζ's factor across the axis. -/
theorem chiZeta_mul_chiZeta_one_sub {s : ℂ} (hs : s ∈ strip) : chiZeta s * chiZeta (1 - s) = 1 := by
  unfold chiZeta
  rw [← mul_inv, feFactor_mul_feFactor_one_sub hs, inv_one]

theorem chiZeta_ne_zero {s : ℂ} (hs : s ∈ strip) : chiZeta s ≠ 0 :=
  left_ne_zero_of_mul_eq_one (chiZeta_mul_chiZeta_one_sub hs)

/-- A multiplicative face with log-face `Λ`: `exp Λ`. -/
noncomputable def face (Λ : ℂ → ℂ) (s : ℂ) : ℂ := Complex.exp (Λ s)

/-- The two-ended face `exp Λ(s) + χ(s) exp Λ(1 − s)`. -/
noncomputable def twoEndedFace (Λ : ℂ → ℂ) (s : ℂ) : ℂ := face Λ s + chiZeta s * face Λ (1 - s)

/-- The two-end ratio `χ(s) exp Λ(1 − s) / exp Λ(s)`. -/
noncomputable def faceRatio (Λ : ℂ → ℂ) (s : ℂ) : ℂ := chiZeta s * face Λ (1 - s) / face Λ s

/-- The windowed log-Euler bank at front `x` with real coefficients `c`:
`L_x(s) = Σ_{1 ≤ n < x} c n · exp (−s log n)`. -/
noncomputable def logEulerBank (c : ℕ → ℝ) (x : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 x, (c n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))

/-- The unwarped multiplicative face at front `x`. -/
noncomputable abbrev eulerFace (c : ℕ → ℝ) (x : ℕ) : ℂ → ℂ := face (logEulerBank c x)

/-- The warped multiplicative face at front `x` with warp potential `P`: `exp (L_x + P)`. -/
noncomputable abbrev warpedFace (c : ℕ → ℝ) (x : ℕ) (P : ℂ → ℂ) : ℂ → ℂ :=
  face (fun s => logEulerBank c x s + P s)

theorem face_ne_zero (Λ : ℂ → ℂ) (s : ℂ) : face Λ s ≠ 0 := Complex.exp_ne_zero _

theorem twoEndedFace_eq_mul (Λ : ℂ → ℂ) (s : ℂ) :
    twoEndedFace Λ s = face Λ s * (1 + faceRatio Λ s) := by
  unfold twoEndedFace faceRatio
  have h := face_ne_zero Λ s
  rw [mul_add, mul_one, mul_div_assoc', mul_comm (face Λ s) (chiZeta s * face Λ (1 - s)),
    mul_div_assoc, div_self h, mul_one]

/-- A balanced event of a multiplicative face is exactly a point where the two-end ratio is `−1`. -/
theorem twoEndedFace_eq_zero_iff (Λ : ℂ → ℂ) (s : ℂ) :
    twoEndedFace Λ s = 0 ↔ faceRatio Λ s = -1 := by
  rw [twoEndedFace_eq_mul, mul_eq_zero, or_iff_right (face_ne_zero Λ s)]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- The modulus of the two-end ratio: ζ's factor times the exponential of the difference of the two ends'
real log-faces. -/
theorem norm_faceRatio (Λ : ℂ → ℂ) (s : ℂ) :
    ‖faceRatio Λ s‖ = ‖chiZeta s‖ * Real.exp ((Λ (1 - s)).re - (Λ s).re) := by
  unfold faceRatio face
  rw [norm_div, norm_mul, Complex.norm_exp, Complex.norm_exp, Real.exp_sub, mul_div_assoc]

/-- The exact log-modulus law of the two-end ratio, explicit in the log-face. -/
theorem log_norm_faceRatio (Λ : ℂ → ℂ) {s : ℂ} (hs : s ∈ strip) :
    Real.log ‖faceRatio Λ s‖ = -Real.log ‖feFactor s‖ + ((Λ (1 - s)).re - (Λ s).re) := by
  rw [norm_faceRatio, Real.log_mul (norm_ne_zero_iff.mpr (chiZeta_ne_zero hs)) (Real.exp_pos _).ne',
    Real.log_exp]
  unfold chiZeta
  rw [norm_inv, Real.log_inv]

/-- The unwarped face: the law in the windings alone. -/
theorem log_norm_eulerRatio (c : ℕ → ℝ) (x : ℕ) {s : ℂ} (hs : s ∈ strip) :
    Real.log ‖faceRatio (logEulerBank c x) s‖ =
      -Real.log ‖feFactor s‖ + ((logEulerBank c x (1 - s)).re - (logEulerBank c x s).re) :=
  log_norm_faceRatio _ hs

/-- The warped face: the windings plus the warp potential's own two-end difference. -/
theorem log_norm_warpedRatio (c : ℕ → ℝ) (x : ℕ) (P : ℂ → ℂ) {s : ℂ} (hs : s ∈ strip) :
    Real.log ‖faceRatio (fun s => logEulerBank c x s + P s) s‖ =
      -Real.log ‖feFactor s‖ + ((logEulerBank c x (1 - s)).re - (logEulerBank c x s).re)
        + ((P (1 - s)).re - (P s).re) := by
  rw [log_norm_faceRatio _ hs]
  simp only [Complex.add_re]
  ring

/-- The real log-bank on a horizontal line: the windings' cosines with radial weights `n^{−σ}`. -/
theorem re_logEulerBank (c : ℕ → ℝ) (x : ℕ) (σ t : ℝ) :
    (logEulerBank c x (σ + t * I)).re =
      ∑ n ∈ Finset.Ico 1 x, c n * Real.exp (-σ * Real.log n) * Real.cos (t * Real.log n) := by
  unfold logEulerBank
  rw [Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  have h1 : (-(σ + t * I) * (Real.log n : ℂ)).re = -σ * Real.log n := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have h2 : (-(σ + t * I) * (Real.log n : ℂ)).im = -(t * Real.log n) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [h1, h2, Real.cos_neg, mul_assoc]

/-- The reflected end on the same line: the same cosines with the mirrored radial weights `n^{−(1−σ)}`. -/
theorem re_logEulerBank_reflect (c : ℕ → ℝ) (x : ℕ) (σ t : ℝ) :
    (logEulerBank c x (1 - (σ + t * I))).re =
      ∑ n ∈ Finset.Ico 1 x, c n * Real.exp (-(1 - σ) * Real.log n) * Real.cos (t * Real.log n) := by
  have h : (1 : ℂ) - (σ + t * I) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, re_logEulerBank]
  refine sum_congr rfl fun n _ => ?_
  rw [show (-t) * Real.log (n : ℝ) = -(t * Real.log (n : ℝ)) by ring, Real.cos_neg]

/-- The bank side of the density register at height `t`:
`2 Σ_{n<x} c n · log n · n^{−½} cos(t log n)` (for the Riesz coefficients, `c n · log n = w_x(n) Λ(n)`). -/
noncomputable def windingSlope (c : ℕ → ℝ) (x : ℕ) (t : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Ico 1 x,
    c n * Real.log n * Real.exp (-(1 / 2 : ℝ) * Real.log n) * Real.cos (t * Real.log n)

/-- The first-order law across the axis: the slope of the two ends' log-bank difference at `σ = ½`
is the winding slope — the prime clocks' cosines at the carrier's balanced radius. -/
theorem hasDerivAt_re_logEulerBank_diff (c : ℕ → ℝ) (x : ℕ) (t : ℝ) :
    HasDerivAt
      (fun σ : ℝ => (logEulerBank c x (1 - (σ + t * I))).re - (logEulerBank c x (σ + t * I)).re)
      (windingSlope c x t) (1 / 2 : ℝ) := by
  have hfun :
      (fun σ : ℝ => (logEulerBank c x (1 - (σ + t * I))).re - (logEulerBank c x (σ + t * I)).re)
        = fun σ : ℝ => ∑ n ∈ Finset.Ico 1 x,
            (c n * Real.exp (-(1 - σ) * Real.log n) * Real.cos (t * Real.log n)
              - c n * Real.exp (-σ * Real.log n) * Real.cos (t * Real.log n)) := by
    funext σ
    rw [re_logEulerBank, re_logEulerBank_reflect, sum_sub_distrib]
  rw [hfun]
  have hterm : ∀ n ∈ Finset.Ico 1 x, HasDerivAt
      (fun σ : ℝ => c n * Real.exp (-(1 - σ) * Real.log n) * Real.cos (t * Real.log n)
              - c n * Real.exp (-σ * Real.log n) * Real.cos (t * Real.log n))
      (2 * (c n * Real.log n * Real.exp (-(1 / 2 : ℝ) * Real.log n) * Real.cos (t * Real.log n)))
      (1 / 2 : ℝ) := by
    intro n _
    have h1 : HasDerivAt (fun σ : ℝ => -(1 - σ) * Real.log n) (Real.log n) (1 / 2 : ℝ) := by
      have := ((hasDerivAt_id (1 / 2 : ℝ)).const_sub 1).neg.mul_const (Real.log n)
      simpa using this
    have h2 : HasDerivAt (fun σ : ℝ => -σ * Real.log n) (-Real.log n) (1 / 2 : ℝ) := by
      have := (hasDerivAt_id (1 / 2 : ℝ)).neg.mul_const (Real.log n)
      simpa using this
    have e1 := ((h1.exp).const_mul (c n)).mul_const (Real.cos (t * Real.log n))
    have e2 := ((h2.exp).const_mul (c n)).mul_const (Real.cos (t * Real.log n))
    refine (e1.sub e2).congr_deriv ?_
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    ring
  have hsum := HasDerivAt.sum hterm
  rw [windingSlope, mul_sum]
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun σ => by rw [Finset.sum_apply])

/-- Far-side domination of a multiplicative face: the helix end exceeds the anti-helix end strictly right
of the axis inside the strip.  NOT a theorem for any face built here: for the unwarped face it fails in the
pole's shadow (att706); for the warped face it holds at first order at every height tested and fails at
finite distance from the axis at a few heights (att707).  Recorded as the sufficient condition it is. -/
def FaceDomination (Λ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, s ∈ strip → 1 / 2 < s.re → ‖faceRatio Λ s‖ < 1

/-- The two-end ratio of a multiplicative face is a determinant-one pair across the axis. -/
theorem faceRatio_mul_faceRatio_one_sub (Λ : ℂ → ℂ) {s : ℂ} (hs : s ∈ strip) :
    faceRatio Λ s * faceRatio Λ (1 - s) = 1 := by
  unfold faceRatio
  have h1 := face_ne_zero Λ s
  have h2 := face_ne_zero Λ (1 - s)
  rw [sub_sub_cancel]
  have key : chiZeta s * face Λ (1 - s) / face Λ s * (chiZeta (1 - s) * face Λ s / face Λ (1 - s))
      = (chiZeta s * chiZeta (1 - s)) * ((face Λ (1 - s) / face Λ s) * (face Λ s / face Λ (1 - s))) := by
    ring
  rw [key, div_mul_div_comm, mul_comm (face Λ (1 - s)) (face Λ s), div_self (mul_ne_zero h1 h2), mul_one,
    chiZeta_mul_chiZeta_one_sub hs]

/-- Domination puts every balanced event of a multiplicative face on the axis. -/
theorem re_eq_half_of_twoEndedFace_eq_zero (Λ : ℂ → ℂ) (hdom : FaceDomination Λ) {s : ℂ}
    (hs : s ∈ strip) (h0 : twoEndedFace Λ s = 0) : s.re = 1 / 2 := by
  have hR : faceRatio Λ s = -1 := (twoEndedFace_eq_zero_iff Λ s).mp h0
  have hnorm : ‖faceRatio Λ s‖ = 1 := by rw [hR, norm_neg, norm_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs' : (1 - s) ∈ strip := by
      show 0 < (1 - s).re ∧ (1 - s).re < 1
      rw [sub_re, one_re]
      constructor <;> linarith [hs.1, hs.2]
    have hfar : 1 / 2 < (1 - s).re := by rw [sub_re, one_re]; linarith
    have h1 := hdom (1 - s) hs' hfar
    have hprod := faceRatio_mul_faceRatio_one_sub Λ hs
    have hmul : ‖faceRatio Λ s‖ * ‖faceRatio Λ (1 - s)‖ = 1 := by
      rw [← norm_mul, hprod, norm_one]
    rw [hnorm, one_mul] at hmul
    linarith
  · have h1 := hdom s hs hgt
    linarith

end CriticalLinePhasor.GrownFiber
