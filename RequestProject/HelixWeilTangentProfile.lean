import RequestProject.HelixWeilWitnessDoor

/-!
# The tangent profile: the `d²`-coefficient of the pair family (ledger 1346, W4a)

The pair profile `pairProfile λ (c + d)` with `c = ½ + iγ` on the axis is `e^{−x²/4λ} e^{−iγx} (−2 sinh(dx))`, so
its `d`-derivative at `d = 0` is the Hermite–Gaussian **tangent profile** `x ↦ x·gaussProfile λ c x` (up to the
factor `−2`). This module compiles the tangent profile as an admissible Weil test:

* `integral_mul_cexp_quadratic`: the first moment `∫ x·e^{bx² + ax} = −(a/2b) ∫ e^{bx² + ax}` (integration by
  parts on the whole line, `integral_of_hasDerivAt_of_tendsto`);
* `laplaceTest_tangentProfile`: the transform `2λ·N·(z − c)·e^{λ(z−c)²}`;
* `reflect_tangentProfile`: the reflection is `−` the profile (the centre is on the axis);
* `tangent_autocorr_eq`: the autocorrelation's transform is `−4λ²|N|²·tangentKernel`,
  `tangentKernel λ γ z = (z − c)² e^{2λ(z−c)²}`;
* admissibility for `weil_explicit_formula'` (continuity, integrable line profiles, entire transform, decay of
  order 4), hence `carrierSide_tangent_eq_zeroSide`.

No `sorry`, no `axiom`, no window.
-/

open Complex MeasureTheory Filter Topology
open scoped Real ComplexConjugate Convolution

noncomputable section

namespace CriticalLinePhasor.HelixWeilWitness

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.HelixCarrierWeil CriticalLinePhasor.WeilGauss

/-! ## The first moment of a complex Gaussian -/

/-- `|x| ≤ (1 + 1/α)·e^{αx²}` for `α > 0`. -/
theorem abs_le_exp_mul_sq {α : ℝ} (hα : 0 < α) (x : ℝ) :
    |x| ≤ (1 + 1 / α) * Real.exp (α * x ^ 2) := by
  have h1 : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
  have h2 : 1 + x ^ 2 ≤ (1 + 1 / α) * (1 + α * x ^ 2) := by
    have hinv : 0 < 1 / α := by positivity
    have hprod : (1 / α) * α = 1 := by field_simp
    have : (1 + 1 / α) * (1 + α * x ^ 2) = 1 + α * x ^ 2 + 1 / α + ((1 / α) * α) * x ^ 2 := by ring
    rw [this, hprod]
    nlinarith [sq_nonneg x, mul_nonneg hα.le (sq_nonneg x)]
  have h3 : 1 + α * x ^ 2 ≤ Real.exp (α * x ^ 2) := by
    have := Real.add_one_le_exp (α * x ^ 2); linarith
  calc |x| ≤ 1 + x ^ 2 := h1
    _ ≤ (1 + 1 / α) * (1 + α * x ^ 2) := h2
    _ ≤ (1 + 1 / α) * Real.exp (α * x ^ 2) := by
        apply mul_le_mul_of_nonneg_left h3; positivity

theorem exp_quadratic_re (b a : ℂ) (x : ℝ) :
    (b * (x : ℂ) ^ 2 + a * x).re = b.re * x ^ 2 + a.re * x := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq]

theorem integrable_exp_quadratic {b : ℂ} (hb : b.re < 0) (a : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (b * x ^ 2 + a * x)) := by
  have := integrable_cexp_quadratic' hb a 0
  simpa using this

/-- `x·e^{bx² + ax}` is integrable for `Re b < 0`. -/
theorem integrable_mul_cexp_quadratic {b : ℂ} (hb : b.re < 0) (a : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) * Complex.exp (b * x ^ 2 + a * x)) := by
  set α : ℝ := -b.re / 2 with hα
  have hαpos : 0 < α := by rw [hα]; linarith
  have hb2 : (((1 / 2 : ℝ) : ℂ) * b).re < 0 := by rw [Complex.re_ofReal_mul]; linarith
  have hdom := (integrable_exp_quadratic hb2 a).norm.const_mul (1 + 1 / α)
  refine hdom.mono' ?_ ?_
  · exact (Complex.continuous_ofReal.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.norm_exp,
      exp_quadratic_re, exp_quadratic_re, Complex.re_ofReal_mul]
    have hx := abs_le_exp_mul_sq hαpos x
    calc |x| * Real.exp (b.re * x ^ 2 + a.re * x)
        ≤ (1 + 1 / α) * Real.exp (α * x ^ 2) * Real.exp (b.re * x ^ 2 + a.re * x) :=
          mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)
      _ = (1 + 1 / α) * Real.exp (1 / 2 * b.re * x ^ 2 + a.re * x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hα]; ring

/-- `e^{bx² + ax} → 0` at both ends for `Re b < 0`. -/
theorem tendsto_exp_quadratic_cocompact {b : ℂ} (hb : b.re < 0) (a : ℂ) :
    Tendsto (fun x : ℝ => Complex.exp (b * x ^ 2 + a * x)) (cocompact ℝ) (𝓝 0) := by
  set α : ℝ := -b.re / 2 with hα
  have hαpos : 0 < α := by rw [hα]; linarith
  have hbound : ∀ x : ℝ, ‖Complex.exp (b * x ^ 2 + a * x)‖
      ≤ Real.exp (a.re ^ 2 / (4 * α)) * Real.exp (-α * x ^ 2) := by
    intro x
    rw [Complex.norm_exp, exp_quadratic_re, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hbre : b.re = -2 * α := by rw [hα]; ring
    rw [hbre]
    have h4 : 0 < 4 * α := by positivity
    have key : 0 ≤ α * (x - a.re / (2 * α)) ^ 2 := by positivity
    have : α * (x - a.re / (2 * α)) ^ 2 = α * x ^ 2 - a.re * x + a.re ^ 2 / (4 * α) := by
      field_simp; ring
    nlinarith
  have hgauss : Tendsto (fun x : ℝ => Real.exp (-α * x ^ 2)) (cocompact ℝ) (𝓝 0) := by
    have := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hαpos 0
    simpa using this
  have hC : Tendsto (fun x : ℝ => Real.exp (a.re ^ 2 / (4 * α)) * Real.exp (-α * x ^ 2)) (cocompact ℝ) (𝓝 0) := by
    simpa using hgauss.const_mul (Real.exp (a.re ^ 2 / (4 * α)))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hbound hC)

/-- **The first moment**: `∫ x·e^{bx² + ax} = −(a/(2b))·∫ e^{bx² + ax}` for `Re b < 0`. -/
theorem integral_mul_cexp_quadratic {b : ℂ} (hb : b.re < 0) (a : ℂ) :
    ∫ x : ℝ, (x : ℂ) * Complex.exp (b * x ^ 2 + a * x)
      = -(a / (2 * b)) * ∫ x : ℝ, Complex.exp (b * x ^ 2 + a * x) := by
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (b * x ^ 2 + a * x))
      ((2 * b * x + a) * Complex.exp (b * x ^ 2 + a * x)) x := by
    intro x
    have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h1 : HasDerivAt (fun x : ℝ => b * (x : ℂ) ^ 2 + a * x) (2 * b * x + a) x := by
      have := ((h0.pow 2).const_mul b).add (h0.const_mul a)
      convert this using 1
      simp
      ring
    have := (Complex.hasDerivAt_exp (b * (x : ℂ) ^ 2 + a * x)).comp x h1
    exact this.congr_deriv (by ring)
  have hxint := integrable_mul_cexp_quadratic hb a
  have heint := integrable_exp_quadratic hb a
  have hint : Integrable (fun x : ℝ => (2 * b * x + a) * Complex.exp (b * x ^ 2 + a * x)) := by
    refine ((hxint.const_mul (2 * b)).add (heint.const_mul a)).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  have hlim := tendsto_exp_quadratic_cocompact hb a
  have h0 := integral_of_hasDerivAt_of_tendsto hderiv hint (hlim.mono_left atBot_le_cocompact)
    (hlim.mono_left atTop_le_cocompact)
  rw [sub_zero] at h0
  have hsplit : ∫ x : ℝ, (2 * b * x + a) * Complex.exp (b * x ^ 2 + a * x)
      = 2 * b * (∫ x : ℝ, (x : ℂ) * Complex.exp (b * x ^ 2 + a * x))
        + a * (∫ x : ℝ, Complex.exp (b * x ^ 2 + a * x)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hxint.const_mul _) (heint.const_mul _)]
    congr 1; funext x; ring
  rw [hsplit] at h0
  have h2b : (2 * b) ≠ 0 := mul_ne_zero two_ne_zero hb0
  have h0' : 2 * b * (∫ x : ℝ, (x : ℂ) * Complex.exp (b * x ^ 2 + a * x))
      = -(a * (∫ x : ℝ, Complex.exp (b * x ^ 2 + a * x))) := by
    linear_combination h0
  calc ∫ x : ℝ, (x : ℂ) * Complex.exp (b * x ^ 2 + a * x)
      = (2 * b * (∫ x : ℝ, (x : ℂ) * Complex.exp (b * x ^ 2 + a * x))) / (2 * b) := by
        rw [mul_div_cancel_left₀ _ h2b]
    _ = (-(a * (∫ x : ℝ, Complex.exp (b * x ^ 2 + a * x)))) / (2 * b) := by rw [h0']
    _ = -(a / (2 * b)) * ∫ x : ℝ, Complex.exp (b * x ^ 2 + a * x) := by ring

/-! ## The tangent profile -/

/-- The axis centre `c = ½ + iγ`. -/
def axisPt (γ : ℝ) : ℂ := 1 / 2 + (γ : ℂ) * I

theorem axisPt_re (γ : ℝ) : (axisPt γ).re = 1 / 2 := by simp [axisPt]
theorem axisPt_im (γ : ℝ) : (axisPt γ).im = γ := by simp [axisPt]

theorem one_sub_conj_axisPt (γ : ℝ) : 1 - conj (axisPt γ) = axisPt γ := by
  apply Complex.ext
  · simp [axisPt]; norm_num
  · simp [axisPt]

/-- The tangent profile `x ↦ x·gaussProfile λ c x` at the axis centre `c = ½ + iγ`. -/
def tangentProfile (lam γ : ℝ) (x : ℝ) : ℂ := (x : ℂ) * gaussProfile lam (axisPt γ) x

theorem tangentProfile_mul_exp_integrable {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => tangentProfile lam γ x * Complex.exp ((z - 1 / 2) * x)) := by
  have h := integrable_mul_cexp_quadratic (bcoef_re_neg hlam) (z - axisPt γ)
  refine h.congr ?_
  filter_upwards with x
  unfold tangentProfile gaussProfile
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- **The tangent transform**: `laplaceTest (tangentProfile λ γ) z = 2λ·N·(z − c)·exp(λ(z − c)²)`. -/
theorem laplaceTest_tangentProfile {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (z : ℂ) :
    laplaceTest (tangentProfile lam γ) z
      = 2 * lam * gaussNorm lam * (z - axisPt γ) * Complex.exp (lam * (z - axisPt γ) ^ 2) := by
  have hG := laplaceTest_gaussProfile hlam (axisPt γ) z
  unfold laplaceTest at hG ⊢
  unfold tangentProfile
  have hpt : ∀ x : ℝ, (x : ℂ) * gaussProfile lam (axisPt γ) x * Complex.exp ((z - 1 / 2) * x)
      = (x : ℂ) * Complex.exp (bcoef lam * (x : ℂ) ^ 2 + (z - axisPt γ) * x) := by
    intro x; unfold gaussProfile; rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
  have hpt' : ∀ x : ℝ, gaussProfile lam (axisPt γ) x * Complex.exp ((z - 1 / 2) * x)
      = Complex.exp (bcoef lam * (x : ℂ) ^ 2 + (z - axisPt γ) * x) := by
    intro x; unfold gaussProfile; rw [← Complex.exp_add]; congr 1; ring
  simp_rw [hpt]
  simp_rw [hpt'] at hG
  rw [integral_mul_cexp_quadratic (bcoef_re_neg hlam) (z - axisPt γ), hG, bcoef_eq]
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  field_simp
  ring

theorem conj_gaussProfile_neg (lam : ℝ) (ρ : ℂ) (x : ℝ) :
    conj (gaussProfile lam ρ (-x)) = gaussProfile lam (1 - conj ρ) x := by
  unfold gaussProfile
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, Complex.conj_ofReal, map_div₀, map_one, map_ofNat,
    Complex.ofReal_neg, bcoef]
  ring

/-- The reflection of the tangent profile is its negative (the centre is on the axis). -/
theorem reflect_tangentProfile (lam γ : ℝ) :
    reflect (tangentProfile lam γ) = fun x => -tangentProfile lam γ x := by
  funext x
  unfold reflect tangentProfile
  rw [map_mul, conj_gaussProfile_neg, one_sub_conj_axisPt, Complex.conj_ofReal]
  push_cast
  ring

theorem reflect_tangentProfile_mul_exp_integrable {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => reflect (tangentProfile lam γ) x * Complex.exp ((z - 1 / 2) * x)) := by
  rw [reflect_tangentProfile]
  have := (tangentProfile_mul_exp_integrable hlam γ z).neg
  refine this.congr ?_
  filter_upwards with x
  simp only [Pi.neg_apply]
  ring

/-! ## The autocorrelation's transform -/

/-- The tangent kernel `(z − c)²·exp(2λ(z − c)²)`. -/
def tangentKernel (lam γ : ℝ) (z : ℂ) : ℂ :=
  (z - axisPt γ) ^ 2 * Complex.exp (((2 * lam : ℝ) : ℂ) * (z - axisPt γ) ^ 2)

theorem conj_laplaceTest_tangent_mirror {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (z : ℂ) :
    conj (laplaceTest (tangentProfile lam γ) (1 - conj z))
      = 2 * lam * conj (gaussNorm lam) * (axisPt γ - z) * Complex.exp (lam * (z - axisPt γ) ^ 2) := by
  rw [laplaceTest_tangentProfile hlam]
  have hc : conj (axisPt γ) = 1 - axisPt γ := by
    have := one_sub_conj_axisPt γ; linear_combination -this
  have hm : (1 : ℂ) - conj z - axisPt γ = conj (axisPt γ - z) := by rw [map_sub, hc]; ring
  rw [hm]
  have hX : (2 : ℂ) * lam * gaussNorm lam * conj (axisPt γ - z)
        * Complex.exp (lam * conj (axisPt γ - z) ^ 2)
      = conj (2 * lam * conj (gaussNorm lam) * (axisPt γ - z) * Complex.exp (lam * (axisPt γ - z) ^ 2)) := by
    simp only [map_mul, map_pow, Complex.conj_conj, Complex.conj_ofReal, map_ofNat, ← Complex.exp_conj]
  rw [hX, Complex.conj_conj]
  have : (axisPt γ - z) ^ 2 = (z - axisPt γ) ^ 2 := by ring
  rw [this]

/-- **The autocorrelation's transform is `−4λ²|N|²·tangentKernel`.** -/
theorem tangent_autocorr_eq {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (z : ℂ) :
    laplaceTest (autocorr (tangentProfile lam γ)) z
      = -((4 * lam ^ 2 * Complex.normSq (gaussNorm lam) : ℝ) : ℂ) * tangentKernel lam γ z := by
  unfold autocorr
  rw [laplaceTest_convolution_of_integrable z (tangentProfile_mul_exp_integrable hlam γ z)
    (reflect_tangentProfile_mul_exp_integrable hlam γ z), laplaceTest_reflect,
    conj_laplaceTest_tangent_mirror hlam, laplaceTest_tangentProfile hlam]
  unfold tangentKernel
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  have hexp : Complex.exp (lam * (z - axisPt γ) ^ 2) * Complex.exp (lam * (z - axisPt γ) ^ 2)
      = Complex.exp (2 * (lam : ℂ) * (z - axisPt γ) ^ 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc 2 * (lam : ℂ) * gaussNorm lam * (z - axisPt γ) * Complex.exp (lam * (z - axisPt γ) ^ 2)
        * (2 * (lam : ℂ) * conj (gaussNorm lam) * (axisPt γ - z) * Complex.exp (lam * (z - axisPt γ) ^ 2))
      = (2 * (lam : ℂ) * gaussNorm lam * (z - axisPt γ)) * (2 * (lam : ℂ) * conj (gaussNorm lam) * (axisPt γ - z))
          * (Complex.exp (lam * (z - axisPt γ) ^ 2) * Complex.exp (lam * (z - axisPt γ) ^ 2)) := by ring
    _ = -(4 * (lam : ℂ) ^ 2 * (conj (gaussNorm lam) * gaussNorm lam))
          * ((z - axisPt γ) ^ 2 * Complex.exp (2 * (lam : ℂ) * (z - axisPt γ) ^ 2)) := by
        rw [hexp]; ring

/-! ## Admissibility -/

theorem tangentProfile_continuous (lam γ : ℝ) : Continuous (tangentProfile lam γ) := by
  unfold tangentProfile; exact Complex.continuous_ofReal.mul (gaussProfile_continuous lam _)

/-- `‖tangentProfile λ γ x‖ = |x|e^{−x²/4λ} ≤ 1 + 4λ`. -/
theorem tangentProfile_norm_le {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (x : ℝ) :
    ‖tangentProfile lam γ x‖ ≤ 1 + 4 * lam := by
  unfold tangentProfile gaussProfile
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (bcoef lam * (x : ℂ) ^ 2 + (1 / 2 - axisPt γ) * x).re = -(1 / (4 * lam)) * x ^ 2 := by
    unfold bcoef axisPt
    simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, sq]
  rw [hre]
  set t : ℝ := x ^ 2 / (4 * lam) with ht
  have ht0 : 0 ≤ t := by positivity
  have hexp : Real.exp (-(1 / (4 * lam)) * x ^ 2) = Real.exp (-t) := by rw [ht]; congr 1; ring
  rw [hexp]
  have h1 : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
  have h2 : x ^ 2 = 4 * lam * t := by rw [ht]; field_simp
  have h3 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h4 : t * Real.exp (-t) ≤ 1 := by
    have hle : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
    exact hle
  calc |x| * Real.exp (-t) ≤ (1 + x ^ 2) * Real.exp (-t) := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = Real.exp (-t) + 4 * lam * (t * Real.exp (-t)) := by rw [h2]; ring
    _ ≤ 1 + 4 * lam * 1 := by gcongr
    _ = 1 + 4 * lam := by ring

theorem reflect_tangentProfile_bddAbove {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) :
    BddAbove (Set.range fun x : ℝ => ‖reflect (tangentProfile lam γ) x‖) := by
  refine ⟨1 + 4 * lam, ?_⟩
  rintro _ ⟨x, rfl⟩
  show ‖reflect (tangentProfile lam γ) x‖ ≤ _
  unfold reflect
  rw [Complex.norm_conj]
  exact tangentProfile_norm_le hlam γ (-x)

theorem tangentProfile_integrable {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) : Integrable (tangentProfile lam γ) := by
  have h := tangentProfile_mul_exp_integrable hlam γ (1 / 2)
  refine h.congr ?_
  filter_upwards with x
  simp

theorem autocorr_tangentProfile_continuous {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) :
    Continuous (autocorr (tangentProfile lam γ)) := by
  unfold autocorr
  exact BddAbove.continuous_convolution_right_of_integrable L (reflect_tangentProfile_bddAbove hlam γ)
    (tangentProfile_integrable hlam γ) (reflect_continuous (tangentProfile_continuous lam γ))

theorem lineProfile_autocorr_tangent_integrable {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (σ : ℝ) :
    Integrable (lineProfile (autocorr (tangentProfile lam γ)) σ) := by
  rw [lineProfile_eq]
  have hfe := tangentProfile_mul_exp_integrable hlam γ (σ : ℂ)
  have hge := reflect_tangentProfile_mul_exp_integrable hlam γ (σ : ℂ)
  have hconv := Integrable.integrable_convolution L hfe hge
  refine hconv.congr ?_
  filter_upwards with x
  unfold autocorr
  exact (conv_mul_exp (tangentProfile lam γ) (reflect (tangentProfile lam γ)) (σ : ℂ) x).symm

theorem laplaceTest_autocorr_tangent_eq {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) :
    laplaceTest (autocorr (tangentProfile lam γ))
      = fun z => -((4 * lam ^ 2 * Complex.normSq (gaussNorm lam) : ℝ) : ℂ) * tangentKernel lam γ z :=
  funext fun z => tangent_autocorr_eq hlam γ z

theorem laplaceTest_autocorr_tangent_differentiable {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) :
    Differentiable ℂ (laplaceTest (autocorr (tangentProfile lam γ))) := by
  rw [laplaceTest_autocorr_tangent_eq hlam]
  unfold tangentKernel
  fun_prop

/-- On a strip, `‖tangentKernel(x + iT)‖ ≤ A(1 + (T−γ)²)·exp(2λ(A − (T−γ)²))`, `A = (max |a| |b| + 1)²`. -/
theorem tangentKernel_norm_le_strip {lam : ℝ} (hlam : 0 ≤ lam) (γ : ℝ) {a b x T : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖tangentKernel lam γ (x + T * I)‖
      ≤ (max |a| |b| + 1) ^ 2 * (1 + (T - γ) ^ 2)
          * Real.exp (2 * lam * ((max |a| |b| + 1) ^ 2 - (T - γ) ^ 2)) := by
  unfold tangentKernel
  rw [norm_mul, norm_pow, Complex.norm_exp]
  set A : ℝ := (max |a| |b| + 1) ^ 2 with hA
  have hre_z : (x + T * I : ℂ).re = x := by simp
  have him_z : (x + T * I : ℂ).im = T := by simp
  have hxabs : |x - 1 / 2| ≤ max |a| |b| + 1 := by
    rcases hx with ⟨hxa, hxb⟩
    have h1 := le_max_left |a| |b|; have h2 := le_max_right |a| |b|
    have := neg_abs_le a; have := le_abs_self b
    rw [abs_le]; constructor <;> linarith
  have hm0 : 0 ≤ max |a| |b| := le_trans (abs_nonneg a) (le_max_left _ _)
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  have hsq : (x - 1 / 2) ^ 2 ≤ A := by
    rw [hA]; nlinarith [abs_nonneg (x - 1 / 2), sq_abs (x - 1 / 2)]
  have hw : ‖x + T * I - axisPt γ‖ ^ 2 = (x - 1 / 2) ^ 2 + (T - γ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [axisPt]
    ring
  have hw2 : ‖x + T * I - axisPt γ‖ ^ 2 ≤ A * (1 + (T - γ) ^ 2) := by
    rw [hw]; nlinarith [sq_nonneg (T - γ)]
  have hexp : ((((2 * lam : ℝ)) : ℂ) * (x + T * I - axisPt γ) ^ 2).re
      = 2 * lam * ((x - 1 / 2) ^ 2 - (T - γ) ^ 2) := by
    rw [re_lam_mul_sq, hre_z, him_z, axisPt_re, axisPt_im]
  rw [hexp]
  have hE : Real.exp (2 * lam * ((x - 1 / 2) ^ 2 - (T - γ) ^ 2)) ≤ Real.exp (2 * lam * (A - (T - γ) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have h2l : 0 ≤ 2 * lam := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hsq h2l]
  calc ‖x + T * I - axisPt γ‖ ^ 2 * Real.exp (2 * lam * ((x - 1 / 2) ^ 2 - (T - γ) ^ 2))
      ≤ (A * (1 + (T - γ) ^ 2)) * Real.exp (2 * lam * (A - (T - γ) ^ 2)) :=
        mul_le_mul hw2 hE (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Decay of order 4 on the strip** for the tangent transform. -/
theorem laplaceTest_autocorr_tangent_decay {lam : ℝ} (hlam : 1 ≤ lam) (γ a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b, ∀ T : ℝ,
      ‖laplaceTest (autocorr (tangentProfile lam γ)) (x + T * I)‖ ≤ C / (1 + |T|) ^ 4 := by
  set A : ℝ := (max |a| |b| + 1) ^ 2 with hA
  have hN : 0 ≤ 4 * lam ^ 2 * Complex.normSq (gaussNorm lam) :=
    mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  refine ⟨(4 * lam ^ 2 * Complex.normSq (gaussNorm lam)) * (A * Real.exp (2 * lam * A)) * (64 * (1 + γ ^ 2) ^ 2),
    mul_nonneg (mul_nonneg hN (by positivity)) (by positivity), ?_⟩
  intro x hx T
  rw [laplaceTest_autocorr_tangent_eq (by linarith)]
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
  have hK := tangentKernel_norm_le_strip (by linarith) γ hx (lam := lam) (T := T)
  have hu : 1 + (T - γ) ^ 2 ≤ Real.exp (lam * (T - γ) ^ 2) := by
    have := Real.add_one_le_exp (lam * (T - γ) ^ 2)
    nlinarith [sq_nonneg (T - γ), mul_le_mul_of_nonneg_right hlam (sq_nonneg (T - γ))]
  have hpow := one_add_abs_pow_four_le hlam γ T
  have hpos4 : 0 < (1 + |T|) ^ 4 := by positivity
  have hsplit : Real.exp (2 * lam * (A - (T - γ) ^ 2))
      = Real.exp (2 * lam * A) * Real.exp (-(2 * lam) * (T - γ) ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcore : (1 + (T - γ) ^ 2) * Real.exp (-(2 * lam) * (T - γ) ^ 2) * (1 + |T|) ^ 4
      ≤ 64 * (1 + γ ^ 2) ^ 2 := by
    have hprod : Real.exp (-(2 * lam) * (T - γ) ^ 2)
        * (Real.exp (lam * (T - γ) ^ 2) * Real.exp (lam * (T - γ) ^ 2)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
    have hge : 0 ≤ Real.exp (-(2 * lam) * (T - γ) ^ 2) := Real.exp_nonneg _
    calc (1 + (T - γ) ^ 2) * Real.exp (-(2 * lam) * (T - γ) ^ 2) * (1 + |T|) ^ 4
        ≤ (Real.exp (lam * (T - γ) ^ 2) * Real.exp (-(2 * lam) * (T - γ) ^ 2))
            * (64 * (1 + γ ^ 2) ^ 2 * Real.exp (lam * (T - γ) ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hu hge) hpow (by positivity) (by positivity)
      _ = 64 * (1 + γ ^ 2) ^ 2 * (Real.exp (-(2 * lam) * (T - γ) ^ 2)
            * (Real.exp (lam * (T - γ) ^ 2) * Real.exp (lam * (T - γ) ^ 2))) := by ring
      _ = 64 * (1 + γ ^ 2) ^ 2 := by rw [hprod, mul_one]
  rw [div_eq_mul_one_div]
  calc 4 * lam ^ 2 * Complex.normSq (gaussNorm lam) * ‖tangentKernel lam γ (x + T * I)‖
      ≤ 4 * lam ^ 2 * Complex.normSq (gaussNorm lam)
          * (A * (1 + (T - γ) ^ 2) * Real.exp (2 * lam * (A - (T - γ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hK hN
    _ = 4 * lam ^ 2 * Complex.normSq (gaussNorm lam) * (A * Real.exp (2 * lam * A))
          * ((1 + (T - γ) ^ 2) * Real.exp (-(2 * lam) * (T - γ) ^ 2) * (1 + |T|) ^ 4) * (1 / (1 + |T|) ^ 4) := by
        rw [hsplit]; field_simp
    _ ≤ 4 * lam ^ 2 * Complex.normSq (gaussNorm lam) * (A * Real.exp (2 * lam * A))
          * (64 * (1 + γ ^ 2) ^ 2) * (1 / (1 + |T|) ^ 4) := by
        gcongr

/-! ## The explicit formula at the tangent profile -/

/-- **The explicit formula at the tangent profile**: carrier side = zero side. -/
theorem carrierSide_tangent_eq_zeroSide {lam : ℝ} (hlam : 1 ≤ lam) (γ : ℝ) {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    carrierSide (autocorr (tangentProfile lam γ)) a b = zeroSide (autocorr (tangentProfile lam γ)) := by
  obtain ⟨C, hC, hdec⟩ := laplaceTest_autocorr_tangent_decay hlam γ a b
  exact (weil_explicit_formula' (autocorr_tangentProfile_continuous (by linarith) γ)
    (lineProfile_autocorr_tangent_integrable (by linarith) γ a)
    (lineProfile_autocorr_tangent_integrable (by linarith) γ b)
    (laplaceTest_autocorr_tangent_differentiable (by linarith) γ) (le_refl 4) hC ha hb hdec).symm

end CriticalLinePhasor.HelixWeilWitness

end

#print axioms CriticalLinePhasor.HelixWeilWitness.integral_mul_cexp_quadratic
#print axioms CriticalLinePhasor.HelixWeilWitness.laplaceTest_tangentProfile
#print axioms CriticalLinePhasor.HelixWeilWitness.tangent_autocorr_eq
#print axioms CriticalLinePhasor.HelixWeilWitness.carrierSide_tangent_eq_zeroSide
