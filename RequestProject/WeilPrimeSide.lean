import Mathlib
import RequestProject.WeilStripContour
import RequestProject.WeilZeroSide

/-!
# Track W2 — the prime side of the explicit formula (ledger 534)

The test function is the two-sided Laplace transform of a compactly supported profile `g`,
centred at `½`:  `F(s) = laplaceTest g s = ∫ g(x) e^{(s−½)x} dx`, so that on the critical line
`F(½ + iτ) = ∫ g(x) e^{iτx} dx` is band-limited when `g` is.

* `laplaceTest_eq_fourierInv` — on the line `Re s = σ`, `F(σ + it) = 𝓕⁻ g_σ (t/2π)` with the line
  profile `g_σ(x) = g(x) e^{(σ−½)x}`.
* `laplaceTest_line_fourier` — **the prime integral**: for every real frequency `y`,
  `∫ F(σ + it) e^{−ity} dt = 2π · g(y) e^{(σ−½)y}` (Fourier inversion, Mathlib
  `Integrable.fourier_fourierInv_eq`). At `y = ± log n` this is `2π g(±log n) n^{±(σ−½)}`, and the
  factor `n^{σ−½}` cancels the `n^{−σ}` of the Dirichlet series: the prime side is
  `Λ(n) n^{−½} g(±log n)`, independent of the line, and FINITE for compactly supported `g`.
* `lseries_line_exchange` — `∫ φ(t) · LSeries Λ (θ t) dt = Σ_n ∫ φ(t) · term_n(θ t) dt` on a line
  `Re θ = σ₀ > 1`, dominated by `Λ(n) n^{−σ₀} ∫‖φ‖`.

No `sorry`, no `axiom`.
-/

open Complex MeasureTheory Filter Topology
open scoped FourierTransform Real

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-- The two-sided Laplace transform of `g`, centred at `½`. -/
def laplaceTest (g : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp ((s - 1 / 2) * x)

/-- The line profile `g_σ(x) = g(x) e^{(σ−½)x}`. -/
def lineProfile (g : ℝ → ℂ) (σ : ℝ) (x : ℝ) : ℂ := g x * (Real.exp ((σ - 1 / 2) * x) : ℂ)

theorem lineProfile_continuous {g : ℝ → ℂ} (hg : Continuous g) (σ : ℝ) :
    Continuous (lineProfile g σ) := by
  unfold lineProfile
  fun_prop

theorem lineProfile_hasCompactSupport {g : ℝ → ℂ} (hsupp : HasCompactSupport g) (σ : ℝ) :
    HasCompactSupport (lineProfile g σ) := by
  have h := hsupp.mul_right (f' := fun x : ℝ => (Real.exp ((σ - 1 / 2) * x) : ℂ))
  exact h

theorem lineProfile_integrable {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (σ : ℝ) : Integrable (lineProfile g σ) :=
  (lineProfile_continuous hg σ).integrable_of_hasCompactSupport (lineProfile_hasCompactSupport hsupp σ)

/-- **The line values are an inverse Fourier transform**: `F(σ + it) = 𝓕⁻ g_σ (t/2π)`. -/
theorem laplaceTest_eq_fourierInv (g : ℝ → ℂ) (σ t : ℝ) :
    laplaceTest g (σ + t * I) = 𝓕⁻ (lineProfile g σ) (t / (2 * π)) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  unfold laplaceTest lineProfile
  congr 1
  funext x
  rw [smul_eq_mul, Complex.ofReal_exp, ← mul_assoc, mul_comm (Complex.exp _) (g x), mul_assoc,
    ← Complex.exp_add]
  congr 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- The Fourier transform of the line profile is the test function on the line, read backwards. -/
theorem fourier_lineProfile_eq (g : ℝ → ℂ) (σ w : ℝ) :
    𝓕 (lineProfile g σ) w = laplaceTest g (σ + ((-(2 * π)) * w : ℝ) * I) := by
  rw [laplaceTest_eq_fourierInv, Real.fourierInv_eq_fourier_neg]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

theorem fourier_lineProfile_integrable {g : ℝ → ℂ} (hF : Continuous (laplaceTest g))
    {σ C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C) (hdec : LineDecay (laplaceTest g) σ C k) :
    Integrable (𝓕 (lineProfile g σ)) := by
  have hline : Integrable (fun t : ℝ => laplaceTest g (σ + t * I)) :=
    integrable_line_of_decay hF hk hC hdec
  have hcomp : Integrable (fun w : ℝ => laplaceTest g (σ + ((-(2 * π)) * w : ℝ) * I)) := by
    have := hline.comp_mul_left' (R := -(2 * π)) (by
      have : (0 : ℝ) < 2 * π := by positivity
      linarith)
    exact this
  refine hcomp.congr (Filter.Eventually.of_forall (fun w => ?_))
  exact (fourier_lineProfile_eq g σ w).symm

/-- **The prime integral**: `∫ F(σ + it) e^{−ity} dt = 2π · g_σ(y)`. -/
theorem laplaceTest_line_fourier {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (hF : Continuous (laplaceTest g)) {σ C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
    (hdec : LineDecay (laplaceTest g) σ C k) (y : ℝ) :
    ∫ t : ℝ, laplaceTest g (σ + t * I) * Complex.exp (-(I * t * y))
      = 2 * π * lineProfile g σ y := by
  set G : ℝ → ℂ := fun x : ℝ =>
    Complex.exp (((-2 * π * x * y : ℝ) : ℂ) * I) • 𝓕⁻ (lineProfile g σ) x with hG
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h1 : ∀ t : ℝ, laplaceTest g (σ + t * I) * Complex.exp (-(I * t * y))
      = G ((2 * π)⁻¹ * t) := by
    intro t
    rw [hG]
    simp only [smul_eq_mul]
    rw [laplaceTest_eq_fourierInv, mul_comm]
    congr 1
    · push_cast
      field_simp
    · rw [div_eq_inv_mul]
  have h2 : ∫ t : ℝ, G ((2 * π)⁻¹ * t) = |((2 * π)⁻¹)⁻¹| • ∫ x : ℝ, G x :=
    Measure.integral_comp_mul_left G ((2 * π)⁻¹)
  have h3 : ∫ x : ℝ, G x = lineProfile g σ y := by
    rw [hG]
    have hf : 𝓕 (𝓕⁻ (lineProfile g σ)) y = lineProfile g σ y :=
      (lineProfile_integrable hg hsupp σ).fourier_fourierInv_eq
        (fourier_lineProfile_integrable hF hk hC hdec) (lineProfile_continuous hg σ).continuousAt
    rw [← hf, Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ => laplaceTest g (σ + t * I) * Complex.exp (-(I * t * y)))
      = fun t : ℝ => G ((2 * π)⁻¹ * t) := funext h1
  rw [hfun, h2, h3, inv_inv, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  ring

/-! ## The Dirichlet-series exchange on a line `Re θ = σ₀ > 1` -/

/-- The von Mangoldt coefficients as a complex sequence. -/
abbrev vonMangoldtC : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

theorem norm_term_vonMangoldt_line {θ : ℂ} {σ₀ : ℝ} (hre : θ.re = σ₀) (n : ℕ) :
    ‖LSeries.term vonMangoldtC θ n‖ = ‖LSeries.term vonMangoldtC (σ₀ : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]

theorem summable_norm_term_vonMangoldt {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    Summable (fun n : ℕ => ‖LSeries.term vonMangoldtC (σ₀ : ℂ) n‖) := by
  have h : LSeriesSummable vonMangoldtC (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ₀)
  exact summable_norm_iff.mpr h

theorem term_line_continuous {θ : ℝ → ℂ} (hθ : Continuous θ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term vonMangoldtC (θ t) n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [LSeries.term_zero]
    exact continuous_const
  · have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have : (fun t : ℝ => LSeries.term vonMangoldtC (θ t) n)
        = fun t : ℝ => vonMangoldtC n / (n : ℂ) ^ (θ t) := by
      funext t
      rw [LSeries.term_of_ne_zero hn.ne']
    rw [this]
    have hre : 0 < ((n : ℂ)).re := by
      rw [Complex.natCast_re]
      exact_mod_cast hn
    refine continuous_const.div (continuous_const.cpow hθ (fun _ => Or.inl hre)) ?_
    intro t h
    exact hne ((Complex.cpow_eq_zero_iff _ _).mp h).1

theorem lseries_line_term_integrable {φ : ℝ → ℂ} (hφ : Integrable φ) {θ : ℝ → ℂ}
    (hθ : Continuous θ) {σ₀ : ℝ} (hre : ∀ t, (θ t).re = σ₀) (n : ℕ) :
    Integrable (fun t : ℝ => φ t * LSeries.term vonMangoldtC (θ t) n) := by
  have hb : ∀ t, ‖LSeries.term vonMangoldtC (θ t) n‖
      ≤ ‖LSeries.term vonMangoldtC (σ₀ : ℂ) n‖ :=
    fun t => le_of_eq (norm_term_vonMangoldt_line (hre t) n)
  exact hφ.mul_bdd (term_line_continuous hθ n).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem lseries_line_norm_summable {φ : ℝ → ℂ} {θ : ℝ → ℂ}
    {σ₀ : ℝ} (hre : ∀ t, (θ t).re = σ₀) (hσ₀ : 1 < σ₀) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖φ t * LSeries.term vonMangoldtC (θ t) n‖) := by
  have hnorm : ∀ n : ℕ, ∫ t : ℝ, ‖φ t * LSeries.term vonMangoldtC (θ t) n‖
      = ‖LSeries.term vonMangoldtC (σ₀ : ℂ) n‖ * ∫ t : ℝ, ‖φ t‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [norm_mul, norm_term_vonMangoldt_line (hre t) n]
    ring
  simp_rw [hnorm]
  exact (summable_norm_term_vonMangoldt hσ₀).mul_right _

theorem lseries_line_integrals_summable {φ : ℝ → ℂ} {θ : ℝ → ℂ}
    {σ₀ : ℝ} (hre : ∀ t, (θ t).re = σ₀) (hσ₀ : 1 < σ₀) :
    Summable (fun n : ℕ => ∫ t : ℝ, φ t * LSeries.term vonMangoldtC (θ t) n) :=
  Summable.of_norm_bounded (lseries_line_norm_summable (φ := φ) hre hσ₀)
    (fun _ => norm_integral_le_integral_norm _)

theorem lseries_line_integrable {φ : ℝ → ℂ} (hφ : Integrable φ) {θ : ℝ → ℂ} (hθ : Continuous θ)
    {σ₀ : ℝ} (hre : ∀ t, (θ t).re = σ₀) (hσ₀ : 1 < σ₀) :
    Integrable (fun t : ℝ => φ t * LSeries vonMangoldtC (θ t)) := by
  have hfun : (fun t : ℝ => φ t * LSeries vonMangoldtC (θ t))
      = fun t : ℝ => ∑' n : ℕ, φ t * LSeries.term vonMangoldtC (θ t) n := by
    funext t
    unfold LSeries
    rw [← tsum_mul_left]
  rw [hfun]
  exact integrable_tsum_of_summable_integral_norm (lseries_line_term_integrable hφ hθ hre)
    (lseries_line_norm_summable hre hσ₀)

/-- **The Dirichlet-series exchange**: for integrable `φ` and a continuous path `θ` on the line
`Re θ = σ₀ > 1`, `∫ φ · LSeries Λ (θ t) = Σ_n ∫ φ · term_n (θ t)`. -/
theorem lseries_line_exchange {φ : ℝ → ℂ} (hφ : Integrable φ) {θ : ℝ → ℂ} (hθ : Continuous θ)
    {σ₀ : ℝ} (hre : ∀ t, (θ t).re = σ₀) (hσ₀ : 1 < σ₀) :
    ∫ t : ℝ, φ t * LSeries vonMangoldtC (θ t)
      = ∑' n : ℕ, ∫ t : ℝ, φ t * LSeries.term vonMangoldtC (θ t) n := by
  have h := integral_tsum_of_summable_integral_norm (lseries_line_term_integrable hφ hθ hre)
    (lseries_line_norm_summable hre hσ₀)
  have hfun : (fun t : ℝ => φ t * LSeries vonMangoldtC (θ t))
      = fun t : ℝ => ∑' n : ℕ, φ t * LSeries.term vonMangoldtC (θ t) n := by
    funext t
    unfold LSeries
    rw [← tsum_mul_left]
  rw [hfun]
  exact h.symm

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.laplaceTest_line_fourier
#print axioms CriticalLinePhasor.ContourArgument.lseries_line_exchange
