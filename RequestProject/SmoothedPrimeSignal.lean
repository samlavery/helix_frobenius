import RequestProject.LandauLaplace
import RequestProject.DVPCarrierContinuation

/-!
# The Gaussian-smoothed prime signal and the one-sided bound (ledger 917)

`W(y) = Σ_n Λ(n) n^{−½} e^{−(y − log n)²}` is the complete prime-power distribution on the log scale, smoothed by
the Gaussian heat kernel.  Its Laplace transform is `K̃(z)·L(Λ, ½ + z)` with `K̃(z) = √π e^{z²/4}` (zero-free),
and its DC mode is `K̃(½) e^{y/2}` (the pole of `ζ` at `1`).

**Main theorem** (`no_zero_right_of_lowerBound`): if for some constant `C` the signal never drops more than `C`
below its DC on `[0, ∞)`,
  `∀ y ≥ 0, K̃(½) e^{y/2} − C ≤ W(y)`,
then `ζ` has no zero with `½ < Re s < 1`.

Ingredients: Landau's theorem (`LandauLaplace.landau`); no real zeros of `ζ` in `(0, 1)` (positivity of the
paired phasors on the real axis, R65's mechanism, restated here); `Z(s) = (s − 1)ζ(s)` entire with `Z(1) = 1`;
the zero-freeness of the Gaussian's transform.

No `sorry`, no `axiom`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Nat NNReal ENNReal ArithmeticFunction.vonMangoldt LSeries.notation

noncomputable section

namespace SmoothedPrimeSignal

open CriticalLinePhasor

/-! ## 1. No real zeros of `ζ` in `(0, 1)` (R65's mechanism) -/

/-- The paired phasor at a real point, as a real number (R65). -/
def realPair (σ : ℝ) (k : ℕ) : ℝ :=
  ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ)

theorem pairTerm_ofReal (σ : ℝ) (k : ℕ) : DVP.pairTerm (σ : ℂ) k = (realPair σ k : ℂ) := by
  rw [DVP.pairTerm_eq, realPair, Complex.ofReal_sub]
  have h1 : (((2 * k + 1 : ℕ) : ℝ) : ℂ) ^ (-(σ : ℂ))
      = ((((2 * k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  have h2 : (((2 * k + 2 : ℕ) : ℝ) : ℂ) ^ (-(σ : ℂ))
      = ((((2 * k + 2 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  rw [h1, h2]

theorem realPair_pos {σ : ℝ} (hσ : 0 < σ) (k : ℕ) : 0 < realPair σ k := by
  unfold realPair
  have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hab : ((2 * k + 1 : ℕ) : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * k + 1 < 2 * k + 2)
  have := Real.rpow_lt_rpow_of_neg ha hab (by linarith : -σ < 0)
  linarith

theorem realPair_summable {σ : ℝ} (hσ : 0 < σ) : Summable (realPair σ) := by
  have h := DVP.pairTerm_summable (s := (σ : ℂ)) (by simpa using hσ)
  have h' : Summable (fun k => (realPair σ k : ℂ)) := h.congr (fun k => pairTerm_ofReal σ k)
  exact Complex.summable_ofReal.mp h'

theorem etaLim_ofReal (σ : ℝ) : DVP.etaLim (σ : ℂ) = ((∑' k, realPair σ k : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold DVP.etaLim
  exact tsum_congr (pairTerm_ofReal σ)

/-- **`ζ` has no zero on the real segment `(0, 1)`.** -/
theorem riemannZeta_ofReal_ne_zero {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have he := DVP.etaLim_eq_zeta (s := (σ : ℂ)) (by simpa using h0) hs1
  rw [hz, mul_zero, etaLim_ofReal] at he
  have hpos : 0 < ∑' k, realPair σ k :=
    (realPair_summable h0).tsum_pos (fun k => (realPair_pos h0 k).le) 0 (realPair_pos h0 0)
  exact (Complex.ofReal_ne_zero.mpr hpos.ne') he

/-! ## 2. `Z(s) = (s − 1) ζ(s)` is entire, `Z(1) = 1` -/

/-- `(s − 1) ζ(s)`, with its removable value `1` at `s = 1`. -/
def Zfun (s : ℂ) : ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1 s

theorem Zfun_of_ne {s : ℂ} (hs : s ≠ 1) : Zfun s = (s - 1) * riemannZeta s := by
  simp [Zfun, Function.update_of_ne hs]

theorem Zfun_one : Zfun 1 = 1 := by simp [Zfun]

theorem Zfun_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    Zfun =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
  filter_upwards [isOpen_ne.mem_nhds hs] with w hw using Zfun_of_ne hw

theorem differentiable_Zfun : Differentiable ℂ Zfun := by
  intro s
  by_cases hs : s = 1
  · subst hs
    have hd : ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ Zfun z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz)).congr_of_eventuallyEq
        (Zfun_eventuallyEq hz)
    have hc : ContinuousAt Zfun 1 := by
      unfold Zfun
      rw [continuousAt_update_same]
      exact riemannZeta_residue_one
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc).differentiableAt
  · exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
      (Zfun_eventuallyEq hs)

/-- `Z` vanishes exactly at the zeros of `ζ` away from `1`. -/
theorem Zfun_eq_zero_iff {s : ℂ} (hs : s ≠ 1) : Zfun s = 0 ↔ riemannZeta s = 0 := by
  rw [Zfun_of_ne hs, mul_eq_zero, sub_eq_zero]
  simp [hs]

/-- **The log-derivative identity**: `−ζ′/ζ = −Z′/Z + 1/(s − 1)` where `ζ(s) ≠ 0`, `s ≠ 1`. -/
theorem neg_logDeriv_zeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s = -deriv Zfun s / Zfun s + 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hZ : Zfun s ≠ 0 := by rw [Zfun_of_ne hs]; exact mul_ne_zero hs1 hz
  -- near `s`, `ζ = Z/(· − 1)`
  have heq : riemannZeta =ᶠ[𝓝 s] fun w => Zfun w / (w - 1) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with w hw
    rw [Zfun_of_ne hw, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hw)]
  have hder : HasDerivAt (fun w => Zfun w / (w - 1))
      ((deriv Zfun s * (s - 1) - Zfun s * 1) / (s - 1) ^ 2) s :=
    (differentiable_Zfun s).hasDerivAt.div ((hasDerivAt_id s).sub_const 1) hs1
  rw [heq.deriv_eq, hder.deriv, heq.eq_of_nhds]
  field_simp
  ring

/-! ## 3. The Gaussian kernel -/

/-- The Gaussian heat kernel on the log scale. -/
def K (x : ℝ) : ℝ := Real.exp (-x ^ 2)

/-- Its two-sided Laplace transform, in closed form. -/
def Kt (z : ℂ) : ℂ := (Real.pi : ℂ) ^ (1 / 2 : ℂ) * cexp (z ^ 2 / 4)

theorem Kt_ne_zero (z : ℂ) : Kt z ≠ 0 := by
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [Ne, Complex.cpow_eq_zero_iff]
  simp [Real.pi_ne_zero]

theorem differentiable_Kt : Differentiable ℂ Kt := by
  intro z
  unfold Kt
  fun_prop

theorem K_mul_cexp (x : ℝ) (z : ℂ) :
    ((K x : ℝ) : ℂ) * cexp (-z * x) = cexp ((-1 : ℂ) * (x : ℂ) ^ 2 + (-z) * x + 0) := by
  rw [K, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_K_mul_cexp (z : ℂ) :
    Integrable (fun x : ℝ => ((K x : ℝ) : ℂ) * cexp (-z * x)) := by
  simp_rw [K_mul_cexp]
  exact integrable_cexp_quadratic' (by simp) _ _

/-- **The Gaussian's Laplace transform**: `∫ e^{−x²} e^{−zx} dx = √π e^{z²/4}`. -/
theorem integral_K_mul_cexp (z : ℂ) :
    ∫ x : ℝ, ((K x : ℝ) : ℂ) * cexp (-z * x) = Kt z := by
  simp_rw [K_mul_cexp]
  rw [integral_cexp_quadratic (by simp), Kt]
  congr 1
  · simp
  · congr 1
    ring

/-- The real kernel against a real exponential is integrable. -/
theorem integrable_K_mul_exp (σ : ℝ) : Integrable (fun x : ℝ => K x * Real.exp (-σ * x)) := by
  have h := (integrable_K_mul_cexp (σ : ℂ)).norm
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ K x by unfold K; positivity),
    LandauLaplace.norm_cexp_neg_mul_ofReal, Complex.ofReal_re]

/-- Translation: `∫ K(y − c) e^{−zy} dy = e^{−zL} K̃(z)`. -/
theorem integral_K_shift (c : ℝ) (z : ℂ) :
    ∫ y : ℝ, ((K (y - c) : ℝ) : ℂ) * cexp (-z * y) = cexp (-z * c) * Kt z := by
  have h : (fun y : ℝ => ((K (y - c) : ℝ) : ℂ) * cexp (-z * y)) =
      fun y => (fun x : ℝ => cexp (-z * c) * (((K x : ℝ) : ℂ) * cexp (-z * x))) (y - c) := by
    funext y
    simp only
    rw [show -z * (y : ℂ) = -z * c + -z * ((y - c : ℝ) : ℂ) by push_cast; ring, Complex.exp_add]
    ring
  rw [h, integral_sub_right_eq_self (fun x : ℝ => cexp (-z * c) * (((K x : ℝ) : ℂ) * cexp (-z * x))) c,
    integral_const_mul, integral_K_mul_cexp]

/-- The real translation identity. -/
theorem integral_K_shift_real (c σ : ℝ) :
    ∫ y : ℝ, K (y - c) * Real.exp (-σ * y) = Real.exp (-σ * c) * ∫ x : ℝ, K x * Real.exp (-σ * x) := by
  have h : (fun y : ℝ => K (y - c) * Real.exp (-σ * y)) =
      fun y => (fun x : ℝ => Real.exp (-σ * c) * (K x * Real.exp (-σ * x))) (y - c) := by
    funext y
    simp only
    rw [show -σ * y = -σ * c + -σ * (y - c) by ring, Real.exp_add]
    ring
  rw [h, integral_sub_right_eq_self (fun x : ℝ => Real.exp (-σ * c) * (K x * Real.exp (-σ * x))) c,
    integral_const_mul]

/-! ## 4. The smoothed prime signal -/

/-- The weights `Λ(n) n^{−½}`. -/
def a (n : ℕ) : ℝ := Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ))

theorem a_nonneg (n : ℕ) : 0 ≤ a n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem a_zero : a 0 = 0 := by simp [a]

theorem a_le (n : ℕ) : a n ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : Λ n ≤ (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn'.le)
  calc a n = Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := rfl
    _ ≤ (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hΛ (by positivity)
    _ = (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hn'.le (by norm_num)]
        norm_num

/-- The Gaussian-smoothed prime signal `W(y) = Σ Λ(n) n^{−½} e^{−(y − log n)²}`. -/
def W (y : ℝ) : ℝ := ∑' n : ℕ, a n * K (y - Real.log n)

/-- `e^{−t²} ≤ e^{9/4} e^{−3t}`. -/
theorem exp_neg_sq_le (t : ℝ) : Real.exp (-t ^ 2) ≤ Real.exp (9 / 4) * Real.exp (-3 * t) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 3 / 2)])

/-- The uniform bound on `y ≤ A`: each term is at most `e^{9/4 + 3A} n^{−5/2}`. -/
theorem term_le (A : ℝ) {y : ℝ} (hy : y ≤ A) (n : ℕ) :
    a n * K (y - Real.log n) ≤ Real.exp (9 / 4 + 3 * A) * (n : ℝ) ^ (-(5 / 2) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_zero]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : K (y - Real.log n) ≤ Real.exp (9 / 4 + 3 * A) * (n : ℝ) ^ (-3 : ℝ) := by
    unfold K
    have h1 := exp_neg_sq_le (Real.log n - y)
    rw [show -(y - Real.log n) ^ 2 = -(Real.log n - y) ^ 2 by ring]
    refine h1.trans ?_
    rw [show -3 * (Real.log n - y) = 3 * y + (-3) * Real.log n by ring, Real.exp_add,
      Real.rpow_def_of_pos hn', show Real.log n * -3 = (-3) * Real.log n by ring,
      show Real.exp (9 / 4 + 3 * A) = Real.exp (9 / 4) * Real.exp (3 * A) by rw [← Real.exp_add]]
    have : Real.exp (3 * y) ≤ Real.exp (3 * A) := Real.exp_le_exp.2 (by linarith)
    have hp := Real.exp_pos ((-3) * Real.log n)
    have hq := Real.exp_pos (9 / 4 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hq.le hp.le)]
  calc a n * K (y - Real.log n)
      ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (Real.exp (9 / 4 + 3 * A) * (n : ℝ) ^ (-3 : ℝ)) :=
        mul_le_mul (a_le n) hK (by unfold K; positivity) (by positivity)
    _ = Real.exp (9 / 4 + 3 * A) * (n : ℝ) ^ (-(5 / 2) : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hn']
        norm_num

theorem summable_bound (A : ℝ) :
    Summable (fun n : ℕ => Real.exp (9 / 4 + 3 * A) * (n : ℝ) ^ (-(5 / 2) : ℝ)) :=
  (Real.summable_nat_rpow.2 (by norm_num)).mul_left _

theorem term_nonneg (y : ℝ) (n : ℕ) : 0 ≤ a n * K (y - Real.log n) :=
  mul_nonneg (a_nonneg n) (by unfold K; positivity)

theorem summable_terms (y : ℝ) : Summable (fun n : ℕ => a n * K (y - Real.log n)) :=
  (summable_bound y).of_nonneg_of_le (term_nonneg y) (term_le y le_rfl)

theorem W_nonneg (y : ℝ) : 0 ≤ W y := tsum_nonneg (term_nonneg y)

theorem continuous_W : Continuous W := by
  rw [continuous_iff_continuousAt]
  intro y
  have hon : ContinuousOn W (Iio (y + 1)) := by
    refine continuousOn_tsum (fun n => ?_) (summable_bound (y + 1)) (fun n x hx => ?_)
    · exact (continuous_const.mul (Real.continuous_exp.comp
        ((continuous_id.sub continuous_const).pow 2).neg)).continuousOn
    · rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg x n)]
      exact term_le (y + 1) (le_of_lt hx) n
  exact hon.continuousAt (Iio_mem_nhds (by linarith))

/-- On `(−∞, 0]` the signal is Gaussian-small: `W(y) ≤ M e^{−y²}`. -/
theorem W_le_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    W y ≤ (∑' n : ℕ, Real.exp (9 / 4 + 3 * 0) * (n : ℝ) ^ (-(5 / 2) : ℝ)) * K y := by
  rw [W, ← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_terms y) ((summable_bound 0).mul_right _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_zero]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hsplit : K (y - Real.log n) ≤ K y * K (Real.log n) := by
    unfold K
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hKneg : K (0 - Real.log n) = K (Real.log n) := by simp [K]
  calc a n * K (y - Real.log n) ≤ a n * (K y * K (Real.log n)) :=
        mul_le_mul_of_nonneg_left hsplit (a_nonneg n)
    _ = (a n * K (0 - Real.log n)) * K y := by rw [hKneg]; ring
    _ ≤ (Real.exp (9 / 4 + 3 * 0) * (n : ℝ) ^ (-(5 / 2) : ℝ)) * K y :=
        mul_le_mul_of_nonneg_right (term_le 0 le_rfl n) (by unfold K; positivity)

/-! ## 5. The Laplace transform of the signal -/

/-- The kernel's real transform `κ(σ) = ∫ K(x) e^{−σx} dx`. -/
def kappa (σ : ℝ) : ℝ := ∫ x : ℝ, K x * Real.exp (-σ * x)

theorem integrable_K_shift_cexp (c : ℝ) (z : ℂ) :
    Integrable (fun y : ℝ => ((K (y - c) : ℝ) : ℂ) * cexp (-z * y)) := by
  have h := ((integrable_K_mul_cexp z).comp_sub_right c).const_mul (cexp (-z * c))
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [show -z * (y : ℂ) = -z * c + -z * ((y - c : ℝ) : ℂ) by push_cast; ring, Complex.exp_add]
  ring

theorem integrable_K_shift_exp (c σ : ℝ) :
    Integrable (fun y : ℝ => K (y - c) * Real.exp (-σ * y)) := by
  have h := ((integrable_K_mul_exp σ).comp_sub_right c).const_mul (Real.exp (-σ * c))
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [show -σ * y = -σ * c + -σ * (y - c) by ring, Real.exp_add]
  ring

/-- For `n ≥ 1`, `Λ(n) n^{−½} e^{−z log n}` is the `n`-th term of `L(Λ, ½ + z)`. -/
theorem a_mul_cexp_eq_term (z : ℂ) (n : ℕ) :
    (a n : ℂ) * cexp (-z * Real.log n) = LSeries.term (fun m => (Λ m : ℂ)) (1 / 2 + z) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_zero]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [LSeries.term_of_ne_zero hn.ne', a, Complex.ofReal_mul, Complex.ofReal_cpow hnr]
  have hlog : cexp (-z * (Real.log n : ℂ)) = (n : ℂ) ^ (-z) := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast, ← Complex.ofReal_log hnr]
    ring_nf
  rw [hlog]
  push_cast
  rw [mul_assoc, ← Complex.cpow_add _ _ hn0, show (-(1 / 2 : ℂ)) + -z = -(1 / 2 + z) by ring,
    Complex.cpow_neg]
  exact (div_eq_mul_inv _ _).symm

/-- Summability of the absolute moments at a real abscissa `σ > ½`. -/
theorem summable_a_exp {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => a n * Real.exp (-σ * Real.log n)) := by
  have hs : 1 < ((1 / 2 + σ : ℝ) : ℂ).re := by simp; linarith
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  have hs' : ((1 / 2 + σ : ℝ) : ℂ) = 1 / 2 + (σ : ℂ) := by push_cast; ring
  rw [hs'] at h
  refine h.congr (fun n => ?_)
  have := a_mul_cexp_eq_term (σ : ℂ) n
  rw [← this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (a_nonneg n),
    LandauLaplace.norm_cexp_neg_mul_ofReal, Complex.ofReal_re]

/-- The real integral of one term. -/
theorem integral_term_real (n : ℕ) (σ : ℝ) :
    ∫ y : ℝ, a n * K (y - Real.log n) * Real.exp (-σ * y)
      = a n * Real.exp (-σ * Real.log n) * kappa σ := by
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_K_shift_real, kappa]

/-- A non-negative series of integrable functions with summable integrals is integrable. -/
theorem integrable_tsum_of_nonneg {F : ℕ → ℝ → ℝ} (hF : ∀ n y, 0 ≤ F n y)
    (hint : ∀ n, Integrable (F n)) (hsum : Summable (fun n => ∫ y, F n y))
    (hmeas : AEStronglyMeasurable (fun y => ∑' n, F n y)) (hpt : ∀ y, Summable (fun n => F n y)) :
    Integrable (fun y => ∑' n, F n y) := by
  have hf0 : 0 ≤ᵐ[volume] fun y => ∑' n, F n y :=
    Eventually.of_forall fun y => tsum_nonneg (fun n => hF n y)
  refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal hf0).2 ?_⟩
  calc ∫⁻ y, ENNReal.ofReal (∑' n, F n y)
      = ∫⁻ y, ∑' n, ENNReal.ofReal (F n y) := by
        congr 1
        funext y
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => hF n y) (hpt y)]
    _ = ∑' n, ∫⁻ y, ENNReal.ofReal (F n y) := by
        rw [lintegral_tsum]
        intro n
        exact (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ = ∑' n, ENNReal.ofReal (∫ y, F n y) := by
        congr 1
        funext n
        rw [ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall (hF n))]
    _ = ENNReal.ofReal (∑' n, ∫ y, F n y) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (hF n)) hsum]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **Convergence**: `W(y) e^{−σy}` is integrable on `ℝ` for every `σ > ½`. -/
theorem integrable_W_mul_exp {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun y => W y * Real.exp (-σ * y)) := by
  have heq : (fun y => W y * Real.exp (-σ * y)) =
      fun y => ∑' n : ℕ, a n * K (y - Real.log n) * Real.exp (-σ * y) := by
    funext y
    rw [W, tsum_mul_right]
  rw [heq]
  refine integrable_tsum_of_nonneg (fun n y => mul_nonneg (term_nonneg y n) (Real.exp_pos _).le)
    (fun n => ?_) ?_ ?_ (fun y => (summable_terms y).mul_right _)
  · simp_rw [mul_assoc]
    exact (integrable_K_shift_exp _ σ).const_mul _
  · simp_rw [integral_term_real]
    exact (summable_a_exp hσ).mul_right _
  · rw [← heq]
    exact (continuous_W.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable

/-- **The Laplace transform of the signal**: `∫ W(y) e^{−zy} dy = K̃(z) L(Λ, ½ + z)` for `Re z > ½`. -/
theorem integral_W_mul_cexp {z : ℂ} (hz : 1 / 2 < z.re) :
    ∫ y : ℝ, (W y : ℂ) * cexp (-z * y) = Kt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) := by
  set F : ℕ → ℝ → ℂ := fun n y => ((a n * K (y - Real.log n) : ℝ) : ℂ) * cexp (-z * y) with hF
  have hW : ∀ y : ℝ, (W y : ℂ) * cexp (-z * y) = ∑' n, F n y := by
    intro y
    rw [W, Complex.ofReal_tsum, tsum_mul_right]
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    have h := (integrable_K_shift_cexp (Real.log n) z).const_mul (a n : ℂ)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [hF]
    push_cast
    ring
  have hFnorm : ∀ n y, ‖F n y‖ = a n * K (y - Real.log n) * Real.exp (-z.re * y) := by
    intro n y
    simp only [hF]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (term_nonneg y n),
      LandauLaplace.norm_cexp_neg_mul_ofReal]
  have hFsum : Summable (fun n => ∫ y, ‖F n y‖) := by
    simp_rw [hFnorm, integral_term_real]
    exact (summable_a_exp hz).mul_right _
  have hFval : ∀ n, ∫ y, F n y = (a n : ℂ) * cexp (-z * Real.log n) * Kt z := by
    intro n
    have h : (fun y => F n y) = fun y => (a n : ℂ) * (((K (y - Real.log n) : ℝ) : ℂ) * cexp (-z * y)) := by
      funext y
      simp only [hF]
      push_cast
      ring
    rw [h, integral_const_mul, integral_K_shift]
    ring
  rw [integral_congr_ae (Eventually.of_forall hW), ← integral_tsum_of_summable_integral_norm hFint hFsum]
  simp_rw [hFval, a_mul_cexp_eq_term]
  rw [tsum_mul_right, LSeries, mul_comm]

theorem integrable_W_mul_cexp {z : ℂ} (hz : 1 / 2 < z.re) :
    Integrable (fun y : ℝ => (W y : ℂ) * cexp (-z * y)) := by
  refine (integrable_W_mul_exp hz).mono
    ((Complex.continuous_ofReal.comp continuous_W).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, LandauLaplace.norm_cexp_neg_mul_ofReal, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-! ## 6. The left tail, the DC constant, and the transform on `[0, ∞)` -/

/-- The left tail `E(z) = ∫_{y < 0} W(y) e^{−zy} dy`. -/
def E (z : ℂ) : ℂ := LandauLaplace.laplace (Iio 0) W z

theorem integrableOn_W_Iio (σ : ℝ) : IntegrableOn (fun y => W y * Real.exp (-σ * y)) (Iio 0) := by
  set M := ∑' n : ℕ, Real.exp (9 / 4 + 3 * 0) * (n : ℝ) ^ (-(5 / 2) : ℝ) with hM
  have hdom : IntegrableOn (fun y => M * (K y * Real.exp (-σ * y))) (Iio 0) :=
    ((integrable_K_mul_exp σ).const_mul M).integrableOn
  refine hdom.mono' ((continuous_W.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (W_nonneg y) (Real.exp_pos _).le)]
  have h := W_le_of_nonpos (le_of_lt hy)
  calc W y * Real.exp (-σ * y) ≤ (M * K y) * Real.exp (-σ * y) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = M * (K y * Real.exp (-σ * y)) := by ring

/-- **The left tail is entire.** -/
theorem differentiable_E : Differentiable ℂ E := by
  intro z
  have h := LandauLaplace.differentiableOn_laplace (Iio 0) W (z.re - 1)
    (fun σ _ => integrableOn_W_Iio σ)
  exact h.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by simp only [mem_ofPred_eq]; linarith))

/-- The DC constant `D = √π e^{1/16} = K̃(½)`. -/
def D : ℝ := Real.sqrt Real.pi * Real.exp (1 / 16)

theorem Kt_half : Kt (1 / 2) = (D : ℂ) := by
  rw [Kt, D, Complex.ofReal_mul, Real.sqrt_eq_rpow,
    Complex.ofReal_cpow Real.pi_pos.le, Complex.ofReal_exp]
  congr 2
  · push_cast
    ring
  · push_cast
    ring

theorem integral_Ici_cexp {w : ℂ} (hw : w.re < 0) :
    ∫ y in Ici (0 : ℝ), cexp (w * y) = -1 / w := by
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi hw 0]
  simp

theorem integrableOn_Ici_cexp {w : ℂ} (hw : w.re < 0) :
    IntegrableOn (fun y : ℝ => cexp (w * y)) (Ici 0) :=
  (integrableOn_exp_mul_complex_Ioi hw 0).congr_set_ae Ioi_ae_eq_Ici.symm

/-- The lower-bound weight `g(y) = W(y) − D e^{y/2} + C`. -/
def g (C : ℝ) (y : ℝ) : ℝ := W y - D * Real.exp (y / 2) + C

/-- **The transform of the weight on `[0, ∞)`**, for `Re z > ½`. -/
theorem laplace_g_eq (C : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    LandauLaplace.laplace (Ici 0) (g C) z
      = Kt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) - E z - (D : ℂ) / (z - 1 / 2) + (C : ℂ) / z := by
  have hz0 : 0 < z.re := by linarith
  have hW := integrable_W_mul_cexp hz
  have h1 : IntegrableOn (fun y : ℝ => (W y : ℂ) * cexp (-z * y)) (Ici 0) := hW.integrableOn
  have h2 : IntegrableOn (fun y : ℝ => cexp ((1 / 2 - z) * y)) (Ici 0) :=
    integrableOn_Ici_cexp (by simp; linarith)
  have h3 : IntegrableOn (fun y : ℝ => cexp (-z * y)) (Ici 0) :=
    integrableOn_Ici_cexp (by simp; linarith)
  have hpt : ∀ y : ℝ, ((g C y : ℝ) : ℂ) * cexp (-z * y)
      = (W y : ℂ) * cexp (-z * y) - (D : ℂ) * cexp ((1 / 2 - z) * y) + (C : ℂ) * cexp (-z * y) := by
    intro y
    rw [g]
    push_cast
    rw [show (1 / 2 - z) * (y : ℂ) = (y : ℂ) / 2 + -z * y by ring, Complex.exp_add]
    ring
  have hA : IntegrableOn (fun y : ℝ => (W y : ℂ) * cexp (-z * y) - (D : ℂ) * cexp ((1 / 2 - z) * y))
      (Ici 0) := h1.sub (h2.const_mul _)
  have hB : IntegrableOn (fun y : ℝ => (D : ℂ) * cexp ((1 / 2 - z) * y)) (Ici 0) := h2.const_mul _
  have hC : IntegrableOn (fun y : ℝ => (C : ℂ) * cexp (-z * y)) (Ici 0) := h3.const_mul _
  rw [LandauLaplace.laplace, integral_congr_ae (Eventually.of_forall hpt), integral_add hA hC,
    integral_sub h1 hB, integral_const_mul, integral_const_mul, integral_Ici_cexp (by simp; linarith),
    integral_Ici_cexp (by simp; linarith)]
  have hsplit := integral_add_compl (measurableSet_Ici (a := (0 : ℝ))) hW
  rw [compl_Ici, integral_W_mul_cexp hz] at hsplit
  have hE : ∫ y in Iio (0 : ℝ), (W y : ℂ) * cexp (-z * y) = E z := rfl
  rw [hE] at hsplit
  have hz1 : z - 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz2 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz0
    exact lt_irrefl _ hz0
  rw [show (∫ y in Ici (0 : ℝ), (W y : ℂ) * cexp (-z * y)) =
      Kt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) - E z by rw [← hsplit]; ring]
  have hh : (1 / 2 : ℂ) - z ≠ 0 := by
    intro h
    exact hz1 (by linear_combination -h)
  rw [show -1 / (1 / 2 - z) = 1 / (z - 1 / 2) by
      rw [show (1 / 2 : ℂ) - z = -(z - 1 / 2) by ring, div_neg, neg_div, neg_neg],
    show -1 / -z = 1 / z by rw [neg_div_neg_eq]]
  ring

/-! ## 7. The continuation `F` and its domain of analyticity -/

theorem re_half_add (z : ℂ) : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by simp

theorem half_add_ne_one {z : ℂ} (h : z.re ≠ 1 / 2) : (1 / 2 : ℂ) + z ≠ 1 := by
  intro hz
  have := congrArg Complex.re hz
  rw [re_half_add, Complex.one_re] at this
  exact h (by linarith)

/-- **A zero-free neighbourhood of the real segment.** -/
theorem exists_zeroFree_strip {σ₀ : ℝ} (h0 : 0 < σ₀) :
    ∃ r > 0, ∀ z : ℂ, σ₀ < z.re → |z.im| < r → Zfun (1 / 2 + z) ≠ 0 := by
  set S : Set ℂ := (fun x : ℝ => ((1 / 2 + x : ℝ) : ℂ)) '' Icc σ₀ (1 / 2) with hS
  have hSc : IsCompact S :=
    isCompact_Icc.image (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
  set O : Set ℂ := {s | Zfun s ≠ 0} with hO
  have hOo : IsOpen O := isOpen_ne_fun differentiable_Zfun.continuous continuous_const
  have hSO : S ⊆ O := by
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    show Zfun ((1 / 2 + x : ℝ) : ℂ) ≠ 0
    rcases eq_or_lt_of_le hx2 with hx | hx
    · rw [hx, show ((1 / 2 + 1 / 2 : ℝ) : ℂ) = 1 by norm_num, Zfun_one]
      exact one_ne_zero
    · have hne : ((1 / 2 + x : ℝ) : ℂ) ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      rw [Ne, Zfun_eq_zero_iff hne]
      exact riemannZeta_ofReal_ne_zero (by linarith) (by linarith)
  obtain ⟨d, hd, hdS⟩ := hSc.exists_thickening_subset_open hOo hSO
  refine ⟨d, hd, fun z hz1 hz2 => ?_⟩
  by_cases hre : z.re ≤ 1 / 2
  · have hmem : ((1 / 2 : ℂ) + z) ∈ Metric.thickening d S := by
      rw [Metric.mem_thickening_iff]
      refine ⟨((1 / 2 + z.re : ℝ) : ℂ), ⟨z.re, ⟨hz1.le, hre⟩, rfl⟩, ?_⟩
      rw [dist_eq_norm]
      have e : ((1 / 2 : ℂ) + z) - ((1 / 2 + z.re : ℝ) : ℂ) = (z.im : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [e, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      exact hz2
    exact hdS hmem
  · push Not at hre
    rw [Ne, Zfun_eq_zero_iff (half_add_ne_one (by linarith))]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [re_half_add]; linarith)

/-- The continuation used in Landau's theorem. -/
def F (C : ℝ) (z : ℂ) : ℂ :=
  Kt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)) + dslope (fun w => Kt w - (D : ℂ)) (1 / 2) z
    - E z + (C : ℂ) / z

/-- **`F` is the transform of the weight on `Re z > 1`.** -/
theorem F_eq_laplace (C : ℝ) {z : ℂ} (hz : 1 < z.re) :
    F C z = LandauLaplace.laplace (Ici 0) (g C) z := by
  rw [laplace_g_eq C (by linarith)]
  have hs : 1 < ((1 / 2 : ℂ) + z).re := by rw [re_half_add]; linarith
  have hs1 : (1 / 2 : ℂ) + z ≠ 1 := half_add_ne_one (by linarith)
  have hzeta : riemannZeta ((1 / 2 : ℂ) + z) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_logDeriv_zeta_eq hs1 hzeta]
  have hz12 : z ≠ 1 / 2 := by
    intro h
    rw [h] at hz
    norm_num at hz
  rw [F, dslope_of_ne _ hz12, slope_def_field, Kt_half,
    show (1 / 2 : ℂ) + z - 1 = z - 1 / 2 by ring]
  ring

/-- **`F` is analytic on Landau's domain.** -/
theorem differentiableOn_F (C : ℝ) {σ₀ r : ℝ} (h0 : 0 < σ₀)
    (hr : ∀ z : ℂ, σ₀ < z.re → |z.im| < r → Zfun (1 / 2 + z) ≠ 0) :
    DifferentiableOn ℂ (F C) (LandauLaplace.domain σ₀ 1 r) := by
  intro z hz
  have hre : 0 < z.re := by
    rcases hz with ⟨h, _⟩ | h
    · linarith
    · have h' : (1 : ℝ) < z.re := h
      linarith
  have hZ : Zfun (1 / 2 + z) ≠ 0 := by
    rcases hz with ⟨h1, h2⟩ | h
    · exact hr z h1 h2
    · have h' : (1 : ℝ) < z.re := h
      rw [Ne, Zfun_eq_zero_iff (half_add_ne_one (by linarith))]
      exact riemannZeta_ne_zero_of_one_le_re (by rw [re_half_add]; linarith)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    linarith
  apply DifferentiableAt.differentiableWithinAt
  have hshift : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    (differentiableAt_const _).add differentiableAt_id
  have hZd : DifferentiableAt ℂ (fun w => Zfun (1 / 2 + w)) z :=
    (differentiable_Zfun _).comp z hshift
  have hdZd : DifferentiableAt ℂ (fun w => deriv Zfun (1 / 2 + w)) z :=
    ((differentiable_Zfun.analyticAt _).deriv.differentiableAt).comp z hshift
  have hdsl : DifferentiableAt ℂ (dslope (fun w => Kt w - (D : ℂ)) (1 / 2)) z := by
    have h := (differentiableOn_dslope (s := univ) (c := (1 / 2 : ℂ)) (f := fun w => Kt w - (D : ℂ))
      Filter.univ_mem).2 (differentiable_Kt.sub_const _).differentiableOn
    exact h.differentiableAt Filter.univ_mem
  unfold F
  exact ((((differentiable_Kt z).mul (hdZd.neg.div hZd hZ)).add hdsl).sub (differentiable_E z)).add
    ((differentiableAt_const _).div differentiableAt_id hz0)

/-! ## 8. The main theorem -/

/-- **The order argument.**  An entire `ψ ≢ 0` with `ψ(p) = 0` cannot satisfy `ψ·Q = −K·ψ′` near `p` with `Q`,
`K` analytic at `p` and `K(p) ≠ 0`: comparing orders of vanishing, the left side vanishes to order `m`, the right
side to order exactly `m − 1`. -/
theorem no_zero_of_multiplied_identity {ψ Q Kf : ℂ → ℂ} {p : ℂ} (hψ : Differentiable ℂ ψ)
    (hψne : ∃ w, ψ w ≠ 0) (hψp : ψ p = 0) (hQ : AnalyticAt ℂ Q p) (hK : AnalyticAt ℂ Kf p)
    (hKp : Kf p ≠ 0) (heq : ∀ᶠ z in 𝓝 p, ψ z * Q z = -(Kf z * deriv ψ z)) : False := by
  have hnot : ¬ ∀ᶠ z in 𝓝 p, ψ z = 0 := by
    intro hz
    obtain ⟨w, hw⟩ := hψne
    exact hw ((hψ.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ p) hz (mem_univ w))
  obtain ⟨m, h, hh_an, hhp, hfac⟩ := (hψ.analyticAt p).exists_eventuallyEq_pow_smul_nonzero_iff.2 hnot
  have hm : m ≠ 0 := by
    rintro rfl
    have h0 := hfac.self_of_nhds
    rw [hψp, pow_zero, one_smul] at h0
    exact hhp h0.symm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hfac' : ψ =ᶠ[𝓝 p] fun z => (z - p) ^ (k + 1) • h z := hfac
  have hh_ev : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ h z :=
    hh_an.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hdψ : ∀ᶠ z in 𝓝 p,
      deriv ψ z = ((k + 1 : ℕ) : ℂ) * (z - p) ^ k * h z + (z - p) ^ (k + 1) * deriv h z := by
    filter_upwards [hfac'.deriv, hh_ev] with z hz1 hz2
    rw [hz1]
    have hpow : HasDerivAt (fun x : ℂ => (x - p) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (z - p) ^ k) z := by
      have := (hasDerivAt_pow (k + 1) (z - p)).comp_sub_const z p
      simpa only [Nat.add_sub_cancel] using this
    rw [(hpow.fun_smul hz2.hasDerivAt).deriv, smul_eq_mul, smul_eq_mul]
    ring
  have hφ : ∀ᶠ z in 𝓝[≠] p,
      (z - p) * h z * Q z + Kf z * (((k + 1 : ℕ) : ℂ) * h z + (z - p) * deriv h z) = 0 := by
    filter_upwards [nhdsWithin_le_nhds heq, nhdsWithin_le_nhds hfac, nhdsWithin_le_nhds hdψ,
      self_mem_nhdsWithin] with z h1 h2 h3 hz
    have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
    rw [h2, h3, smul_eq_mul] at h1
    have hpow : (z - p) ^ k ≠ 0 := pow_ne_zero _ hzp
    apply mul_left_cancel₀ hpow
    rw [mul_zero]
    linear_combination h1
  have hcont : ContinuousAt
      (fun z => (z - p) * h z * Q z + Kf z * (((k + 1 : ℕ) : ℂ) * h z + (z - p) * deriv h z)) p := by
    have c1 := hh_an.continuousAt
    have c2 := hQ.continuousAt
    have c3 := hK.continuousAt
    have c4 := hh_an.deriv.continuousAt
    exact (((continuousAt_id.sub continuousAt_const).mul c1).mul c2).add
      (c3.mul ((continuousAt_const.mul c1).add ((continuousAt_id.sub continuousAt_const).mul c4)))
  have hlim0 : Tendsto
      (fun z => (z - p) * h z * Q z + Kf z * (((k + 1 : ℕ) : ℂ) * h z + (z - p) * deriv h z))
      (𝓝[≠] p) (𝓝 0) :=
    tendsto_const_nhds.congr' (hφ.mono fun z hz => hz.symm)
  have hval := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hlim0
  simp only [sub_self, zero_mul, zero_add, add_zero] at hval
  rcases mul_eq_zero.mp hval with h' | h'
  · exact hKp h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)) h''
    · exact hhp h''

theorem integrableOn_g_Ici (C : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun y => g C y * Real.exp (-σ * y)) (Ici 0) := by
  have hW : IntegrableOn (fun y => W y * Real.exp (-σ * y)) (Ici 0) :=
    (integrable_W_mul_exp hσ).integrableOn
  have hD : IntegrableOn (fun y : ℝ => D * Real.exp (-(σ - 1 / 2) * y)) (Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).congr_set_ae Ioi_ae_eq_Ici.symm).const_mul D
  have hC : IntegrableOn (fun y : ℝ => C * Real.exp (-σ * y)) (Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).congr_set_ae Ioi_ae_eq_Ici.symm).const_mul C
  refine ((hW.sub hD).add hC).congr_fun (fun y _ => ?_) measurableSet_Ici
  simp only [g, Pi.add_apply, Pi.sub_apply]
  rw [show -(σ - 1 / 2) * y = y / 2 + -σ * y by ring, Real.exp_add]
  ring

/-- **Landau applied**: under the one-sided bound, the weight's transform converges on `Re z > σ₀`. -/
theorem integrableOn_g_of_lowerBound (C : ℝ) (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C ≤ W y)
    {σ₀ : ℝ} (h0 : 0 < σ₀) (h01 : σ₀ < 1) :
    ∀ σ, σ₀ < σ → IntegrableOn (fun y => g C y * Real.exp (-σ * y)) (Ici 0) := by
  obtain ⟨r, hr, hrZ⟩ := exists_zeroFree_strip h0
  refine LandauLaplace.landau (g C) 0 le_rfl (fun y hy => ?_) h01 hr
    (fun σ hσ => integrableOn_g_Ici C (by linarith)) (F C) (differentiableOn_F C h0 hrZ)
    (fun z hz => F_eq_laplace C hz)
  have := hC y hy
  unfold g
  linarith

/-- **Main theorem: a one-sided bound on the smoothed prime signal excludes zeros with `Re s > ½`.**
If `W(y) ≥ D e^{y/2} − C` for all `y ≥ 0` (with `D = √π e^{1/16} = K̃(½)`), then `ζ` has no zero with
`½ < Re s < 1`. -/
theorem no_zero_right_of_lowerBound (C : ℝ) (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C ≤ W y)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) : False := by
  set p : ℂ := ρ - 1 / 2 with hp
  have hpre : p.re = ρ.re - 1 / 2 := by simp [hp]
  set σ₀ : ℝ := p.re / 2 with hσ₀
  have h0 : 0 < σ₀ := by rw [hσ₀, hpre]; linarith
  have h01 : σ₀ < 1 := by rw [hσ₀, hpre]; linarith
  have hLd := LandauLaplace.differentiableOn_laplace (Ici 0) (g C) σ₀
    (integrableOn_g_of_lowerBound C hC h0 h01)
  set U : Set ℂ := {z | σ₀ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdsl : Differentiable ℂ (dslope (fun w => Kt w - (D : ℂ)) (1 / 2)) := by
    have h := (differentiableOn_dslope (s := univ) (c := (1 / 2 : ℂ)) (f := fun w => Kt w - (D : ℂ))
      Filter.univ_mem).2 (differentiable_Kt.sub_const _).differentiableOn
    exact fun z => h.differentiableAt Filter.univ_mem
  set Q : ℂ → ℂ := fun z => LandauLaplace.laplace (Ici 0) (g C) z + E z - (C : ℂ) / z
    - dslope (fun w => Kt w - (D : ℂ)) (1 / 2) z with hQ
  set ψ : ℂ → ℂ := fun z => Zfun (1 / 2 + z) with hψ
  have hψd : Differentiable ℂ ψ := fun z =>
    (differentiable_Zfun _).comp z ((differentiableAt_const _).add differentiableAt_id)
  have hQd : DifferentiableOn ℂ Q U := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have : σ₀ < z.re := hz
      rw [h, Complex.zero_re] at this
      linarith
    apply DifferentiableAt.differentiableWithinAt
    exact (((hLd.differentiableAt (hUo.mem_nhds hz)).add (differentiable_E z)).sub
      ((differentiableAt_const _).div differentiableAt_id hz0)).sub (hdsl z)
  have hderiv : ∀ z, deriv ψ z = deriv Zfun (1 / 2 + z) := fun z => deriv_comp_const_add Zfun (1 / 2) z
  have hG1 : AnalyticOnNhd ℂ (fun z => ψ z * Q z) U :=
    (hψd.differentiableOn.mul hQd).analyticOnNhd hUo
  have hG2 : AnalyticOnNhd ℂ (fun z => -(Kt z * deriv ψ z)) U := by
    have hd : Differentiable ℂ (fun z => -(Kt z * deriv ψ z)) := by
      intro z
      simp_rw [hderiv]
      exact ((differentiable_Kt z).mul (((differentiable_Zfun.analyticAt _).deriv.differentiableAt).comp z
        ((differentiableAt_const _).add differentiableAt_id))).neg
    exact hd.differentiableOn.analyticOnNhd hUo
  have hUc : IsPreconnected U := (convex_halfSpace_gt Complex.reLm.isLinear σ₀).isPreconnected
  have h2U : (2 : ℂ) ∈ U := by
    show σ₀ < (2 : ℂ).re
    rw [show (2 : ℂ).re = 2 by norm_num]
    linarith
  have hEq : EqOn (fun z => ψ z * Q z) (fun z => -(Kt z * deriv ψ z)) U := by
    refine hG1.eqOn_of_preconnected_of_eventuallyEq hG2 hUc h2U ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hF := F_eq_laplace C hz'
    have hZ : Zfun (1 / 2 + z) ≠ 0 := by
      rw [Ne, Zfun_eq_zero_iff (half_add_ne_one (by linarith))]
      exact riemannZeta_ne_zero_of_one_le_re (by rw [re_half_add]; linarith)
    have hQz : Q z = Kt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)) := by
      show LandauLaplace.laplace (Ici 0) (g C) z + E z - (C : ℂ) / z
        - dslope (fun w => Kt w - (D : ℂ)) (1 / 2) z = _
      rw [← hF]
      unfold F
      ring
    show ψ z * Q z = -(Kt z * deriv ψ z)
    rw [hQz, hderiv z]
    show Zfun (1 / 2 + z) * (Kt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)))
      = -(Kt z * deriv Zfun (1 / 2 + z))
    rw [mul_div_assoc', mul_div_assoc', div_eq_iff hZ]
    ring
  have hpU : p ∈ U := by
    show σ₀ < p.re
    rw [hσ₀]
    linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h2
    exact lt_irrefl _ h2
  have hψp : ψ p = 0 := by
    simp only [hψ, hp]
    rw [show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring, Zfun_eq_zero_iff hρ1]
    exact hρ
  have hψne : ∃ w, ψ w ≠ 0 := ⟨1 / 2, by
    simp only [hψ]
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Zfun_one]
    exact one_ne_zero⟩
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hpre
    linarith
  exact no_zero_of_multiplied_identity hψd hψne hψp
    (hQd.analyticAt (hUo.mem_nhds hpU)) (differentiable_Kt.analyticAt p) (Kt_ne_zero p)
    (by filter_upwards [hUo.mem_nhds hpU] with z hz using hEq hz)

/-- **The whole strip.**  Under the one-sided bound every zero of `ζ` with `0 < Re ρ < 1` has `Re ρ = ½`.  The
left half is the right half read through the reflection `ρ ↦ 1 − ρ` (`riemannZeta_one_sub`: `ζ(1 − ρ)` is a
multiple of `ζ(ρ)`, so it vanishes; no non-vanishing of the Γ or cosine factors is used). -/
theorem re_eq_half_of_lowerBound (C : ℝ) (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C ≤ W y)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
  · exfalso
    have hn : ∀ n : ℕ, ρ ≠ -n := by
      intro n hn
      have hre := congrArg Complex.re hn
      rw [Complex.neg_re, Complex.natCast_re] at hre
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have hne1 : ρ ≠ 1 := by
      intro h'
      rw [h', Complex.one_re] at h1
      exact lt_irrefl _ h1
    have hz : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_one_sub hn hne1, hρ, mul_zero]
    exact no_zero_right_of_lowerBound C hC (1 - ρ) hz
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (by rw [Complex.sub_re, Complex.one_re]; linarith)
  · exact h
  · exact (no_zero_right_of_lowerBound C hC ρ hρ h h1).elim

end SmoothedPrimeSignal
