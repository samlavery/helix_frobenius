import Mathlib

/-!
# C3 batch 10, block A1 — the autocorrelation pairing, evaluated exactly

Batch 9 attacked `0 ≤ ∫_{Ioi s} tailT (cellDensity x)` with **majorants**: bound every mode,
sum the bound, hope the head wins.  That is worst-case analysis, and the batch-9 numerics
showed why it cannot close — on the window the negative lobe is within a factor ~6 of the
positive one, so no crude envelope separates them.

This block does the opposite, and it is the house discipline: **evaluate the common mode
exactly, and only then estimate.**  The cell density
`C(x,u) = ∫_ℝ Φ(u+p)Φ(u−p) cos(2xp) dp` is an autocorrelation in disguise, and its pairing
against the *entire exponential family* has a closed form:

  `∫_ℝ Ψ(u+p)Ψ(u−p)cos(2xp) dp du  =  ½·(cosMom Ψ x)² + ½·(sinMom Ψ x)²`

for **every** integrable weight `Ψ`.  Two squares.  Nothing is estimated, nothing is
truncated, and nonnegativity is immediate.  Taking `Ψ(t) = e^{λt}Φ(t)` gives the whole
family `∫_ℝ e^{2λu}C(x,u)du ≥ 0` at once, because `e^{λ(u+p)}·e^{λ(u−p)} = e^{2λu}` exactly.

## Why this is not the 2D change of variables

The classical route runs `(u,p) ↦ (u+p, u−p)`, a linear map of determinant `−2` on `ℝ²`.
Here every step is **one-dimensional**: a translation (`integral_sub_left_eq_self`), a
dilation (`integral_comp_mul_left`), and the additive shear
`(u,p) ↦ (u+p, p)`, which Mathlib already knows is measure preserving
(`measurePreserving_add_prod`).  The determinant-`2` Jacobian appears exactly once, as the
`|2⁻¹|` of the one-dimensional dilation.

This file is self-contained: it imports only Mathlib, mentions no `Ξ`, no zeros, and no
arithmetic.  `Ψ` is an arbitrary integrable measurable function.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B10

/-- The cosine moment of a weight. -/
def cosMom (Psi : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t : ℝ, Psi t * Real.cos (x * t)

/-- The sine moment of a weight. -/
def sinMom (Psi : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t : ℝ, Psi t * Real.sin (x * t)

/-- The pairing integrand in **sheared** coordinates `(t, p)`. -/
def bilin (Psi : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) : ℝ :=
  Psi z.1 * Psi (z.1 - 2 * z.2) * Real.cos (2 * x * z.2)

/-- The pairing integrand in **carrier** coordinates `(u, p)`: the two phasor legs
`u+p` and `u−p` of the cell, read against the chart clock `cos(2xp)`. -/
def carrierBilin (Psi : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) : ℝ :=
  Psi (z.1 + z.2) * Psi (z.1 - z.2) * Real.cos (2 * x * z.2)

variable {Psi : ℝ → ℝ}

/-! ### 1. Measurability -/

theorem bilin_measurable (hm : Measurable Psi) (x : ℝ) : Measurable (bilin Psi x) := by
  unfold bilin
  refine Measurable.mul (Measurable.mul (hm.comp measurable_fst) ?_) ?_
  · exact hm.comp (measurable_fst.sub (measurable_const.mul measurable_snd))
  · exact Real.continuous_cos.measurable.comp (measurable_const.mul measurable_snd)

/-! ### 2. The one-dimensional dilation identities -/

/-- `∫_p ‖Ψ(t − 2p)‖ dp = ½‖Ψ‖₁`: the determinant-2 Jacobian, as a 1D dilation. -/
theorem integral_norm_shift_dilate (Psi : ℝ → ℝ) (t : ℝ) :
    (∫ p : ℝ, ‖Psi (t - 2 * p)‖) = 2⁻¹ * ∫ q : ℝ, ‖Psi q‖ := by
  have hdil := MeasureTheory.Measure.integral_comp_mul_left
    (fun q : ℝ => ‖Psi (t - q)‖) 2
  have hshift := MeasureTheory.integral_sub_left_eq_self
    (fun q : ℝ => ‖Psi q‖) volume t
  simp only [smul_eq_mul] at hdil
  rw [hdil, hshift]
  norm_num

/-! ### 3. Slice integrability -/

theorem bilin_slice_integrable (hI : Integrable Psi) (x t : ℝ) :
    Integrable (fun p : ℝ => bilin Psi x (t, p)) := by
  have h1 : Integrable (fun q : ℝ => Psi (t - q)) := hI.comp_sub_left t
  have h2 : Integrable (fun p : ℝ => Psi (t - 2 * p)) :=
    h1.comp_mul_left' (R := (2 : ℝ)) two_ne_zero
  have h3 : Integrable (fun p : ℝ => Psi t * Psi (t - 2 * p)) := h2.const_mul (Psi t)
  refine h3.mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with p
    simpa using Real.abs_cos_le_one (2 * x * p)

/-- The slice `L¹` bound: `∫_p ‖bilin(t,p)‖ ≤ ‖Ψ(t)‖ · ½‖Ψ‖₁`. -/
theorem bilin_slice_norm_le (hI : Integrable Psi) (x t : ℝ) :
    (∫ p : ℝ, ‖bilin Psi x (t, p)‖) ≤ ‖Psi t‖ * (2⁻¹ * ∫ q : ℝ, ‖Psi q‖) := by
  have h1 : Integrable (fun q : ℝ => Psi (t - q)) := hI.comp_sub_left t
  have h2 : Integrable (fun p : ℝ => Psi (t - 2 * p)) :=
    h1.comp_mul_left' (R := (2 : ℝ)) two_ne_zero
  have hmaj : Integrable (fun p : ℝ => ‖Psi t‖ * ‖Psi (t - 2 * p)‖) :=
    (h2.norm).const_mul _
  have hlhs : Integrable (fun p : ℝ => ‖bilin Psi x (t, p)‖) :=
    (bilin_slice_integrable hI x t).norm
  have hpt : ∀ p : ℝ, ‖bilin Psi x (t, p)‖ ≤ ‖Psi t‖ * ‖Psi (t - 2 * p)‖ := by
    intro p
    unfold bilin
    simp only [norm_mul]
    have hc : ‖Real.cos (2 * x * p)‖ ≤ 1 := by
      simpa using Real.abs_cos_le_one (2 * x * p)
    have h0 : (0 : ℝ) ≤ ‖Psi t‖ * ‖Psi (t - 2 * p)‖ := by positivity
    nlinarith [hc, norm_nonneg (Real.cos (2 * x * p)), h0]
  calc (∫ p : ℝ, ‖bilin Psi x (t, p)‖)
      ≤ ∫ p : ℝ, ‖Psi t‖ * ‖Psi (t - 2 * p)‖ := integral_mono hlhs hmaj hpt
    _ = ‖Psi t‖ * ∫ p : ℝ, ‖Psi (t - 2 * p)‖ := integral_const_mul _ _
    _ = ‖Psi t‖ * (2⁻¹ * ∫ q : ℝ, ‖Psi q‖) := by rw [integral_norm_shift_dilate]

/-! ### 4. Product integrability, both charts -/

theorem bilin_prod_integrable (hI : Integrable Psi) (hm : Measurable Psi) (x : ℝ) :
    Integrable (bilin Psi x) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (bilin Psi x) (volume.prod volume) :=
    (bilin_measurable hm x).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun t => bilin_slice_integrable hI x t, ?_⟩
  have hgm : AEStronglyMeasurable (fun t : ℝ => ∫ p : ℝ, ‖bilin Psi x (t, p)‖) volume :=
    ((bilin_measurable hm x).stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
  have hmaj : Integrable (fun t : ℝ => ‖Psi t‖ * (2⁻¹ * ∫ q : ℝ, ‖Psi q‖)) :=
    (hI.norm).mul_const _
  refine Integrable.mono hmaj hgm ?_
  filter_upwards with t
  have hnn : (0 : ℝ) ≤ ∫ p : ℝ, ‖bilin Psi x (t, p)‖ :=
    integral_nonneg fun p => norm_nonneg _
  have hN : (0 : ℝ) ≤ ∫ q : ℝ, ‖Psi q‖ := integral_nonneg fun q => norm_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖Psi t‖ * (2⁻¹ * ∫ q : ℝ, ‖Psi q‖))]
  exact bilin_slice_norm_le hI x t

/-- The carrier chart is the sheared chart: `(u,p) ↦ (u+p, p)` carries one to the other. -/
theorem carrierBilin_eq_bilin_shear (Psi : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) :
    carrierBilin Psi x z = bilin Psi x (z.1 + z.2, z.2) := by
  unfold carrierBilin bilin
  rw [show z.1 + z.2 - 2 * z.2 = z.1 - z.2 by ring]

theorem carrierBilin_prod_integrable (hI : Integrable Psi) (hm : Measurable Psi) (x : ℝ) :
    Integrable (carrierBilin Psi x) (volume.prod volume) := by
  have hS := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hb := bilin_prod_integrable hI hm x
  have hcomp : Integrable (fun z : ℝ × ℝ => bilin Psi x (z.1 + z.2, z.2))
      (volume.prod volume) := by
    have := (integrable_map_measure
      ((bilin_measurable hm x).aestronglyMeasurable.mono_ac
        (by rw [hS.map_eq]))
      hS.measurable.aemeasurable).mp (by rwa [hS.map_eq])
    exact this
  refine hcomp.congr ?_
  filter_upwards with z
  exact (carrierBilin_eq_bilin_shear Psi x z).symm

/-! ### 5. THE EXACT EVALUATION -/

/-- The inner slice, evaluated exactly: no estimate, no truncation. -/
theorem bilin_slice_integral (hI : Integrable Psi) (x t : ℝ) :
    (∫ p : ℝ, bilin Psi x (t, p))
      = 2⁻¹ * (Psi t * Real.cos (x * t) * cosMom Psi x
          + Psi t * Real.sin (x * t) * sinMom Psi x) := by
  have hcos : Integrable (fun t' : ℝ => Psi t' * Real.cos (x * t')) := by
    refine hI.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_cos_le_one (x * t')
  have hsin : Integrable (fun t' : ℝ => Psi t' * Real.sin (x * t')) := by
    refine hI.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_sin_le_one (x * t')
  -- the shifted-and-dilated slice
  have hstep1 : (∫ p : ℝ, bilin Psi x (t, p))
      = Psi t * ∫ p : ℝ, (fun q : ℝ => Psi (t - q) * Real.cos (x * q)) (2 * p) := by
    unfold bilin
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show Psi t * Psi (t - 2 * p) * Real.cos (2 * x * p)
        = Psi t * (Psi (t - 2 * p) * Real.cos (x * (2 * p)))
    rw [show x * (2 * p) = 2 * x * p by ring]
    ring
  have hstep2 : (∫ p : ℝ, (fun q : ℝ => Psi (t - q) * Real.cos (x * q)) (2 * p))
      = 2⁻¹ * ∫ q : ℝ, Psi (t - q) * Real.cos (x * q) := by
    have := MeasureTheory.Measure.integral_comp_mul_left
      (fun q : ℝ => Psi (t - q) * Real.cos (x * q)) 2
    simp only [smul_eq_mul] at this
    rw [this]
    norm_num
  have hstep3 : (∫ q : ℝ, Psi (t - q) * Real.cos (x * q))
      = ∫ t' : ℝ, Psi t' * Real.cos (x * (t - t')) := by
    have := MeasureTheory.integral_sub_left_eq_self
      (fun t' : ℝ => Psi t' * Real.cos (x * (t - t'))) volume t
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    show Psi (t - q) * Real.cos (x * q)
        = Psi (t - q) * Real.cos (x * (t - (t - q)))
    rw [show x * (t - (t - q)) = x * q by ring]
  have hstep4 : (∫ t' : ℝ, Psi t' * Real.cos (x * (t - t')))
      = Real.cos (x * t) * cosMom Psi x + Real.sin (x * t) * sinMom Psi x := by
    have hexp : ∀ t' : ℝ, Psi t' * Real.cos (x * (t - t'))
        = Real.cos (x * t) * (Psi t' * Real.cos (x * t'))
          + Real.sin (x * t) * (Psi t' * Real.sin (x * t')) := by
      intro t'
      rw [show x * (t - t') = x * t - x * t' by ring, Real.cos_sub]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_add (hcos.const_mul _) (hsin.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  rw [hstep1, hstep2, hstep3, hstep4]
  ring

/-- **THE PAIRING, EXACTLY.**  For every integrable measurable weight, the autocorrelation
pairing against the chart clock `cos(2xp)` is exactly one half the sum of two squares. -/
theorem bilin_integral (hI : Integrable Psi) (hm : Measurable Psi) (x : ℝ) :
    (∫ z : ℝ × ℝ, bilin Psi x z ∂(volume.prod volume))
      = 2⁻¹ * (cosMom Psi x ^ 2 + sinMom Psi x ^ 2) := by
  have hcos : Integrable (fun t' : ℝ => Psi t' * Real.cos (x * t')) := by
    refine hI.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_cos_le_one (x * t')
  have hsin : Integrable (fun t' : ℝ => Psi t' * Real.sin (x * t')) := by
    refine hI.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_sin_le_one (x * t')
  rw [integral_prod _ (bilin_prod_integrable hI hm x)]
  rw [integral_congr_ae (Filter.Eventually.of_forall (bilin_slice_integral hI x))]
  rw [integral_const_mul]
  have hsplit : (∫ t : ℝ, (Psi t * Real.cos (x * t) * cosMom Psi x
        + Psi t * Real.sin (x * t) * sinMom Psi x))
      = cosMom Psi x ^ 2 + sinMom Psi x ^ 2 := by
    rw [integral_add (hcos.mul_const _) (hsin.mul_const _),
      integral_mul_const, integral_mul_const]
    unfold cosMom sinMom
    ring
  rw [hsplit]

/-- **THE CARRIER FORM.**  The same evaluation, read in the carrier chart `(u,p)` where the
two phasor legs are `u+p` and `u−p`. -/
theorem autocorrelation_pairing (hI : Integrable Psi) (hm : Measurable Psi) (x : ℝ) :
    (∫ u : ℝ, ∫ p : ℝ, Psi (u + p) * Psi (u - p) * Real.cos (2 * x * p))
      = 2⁻¹ * (cosMom Psi x ^ 2 + sinMom Psi x ^ 2) := by
  have hS := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hshear : (∫ z : ℝ × ℝ, carrierBilin Psi x z ∂(volume.prod volume))
      = ∫ z : ℝ × ℝ, bilin Psi x z ∂(volume.prod volume) := by
    have hmap : (∫ z : ℝ × ℝ, bilin Psi x z ∂(volume.prod volume))
        = ∫ z : ℝ × ℝ, bilin Psi x (z.1 + z.2, z.2) ∂(volume.prod volume) := by
      conv_lhs => rw [← hS.map_eq]
      exact integral_map hS.measurable.aemeasurable
        ((bilin_measurable hm x).aestronglyMeasurable.mono_ac (by rw [hS.map_eq]))
    rw [hmap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact carrierBilin_eq_bilin_shear Psi x z
  rw [← bilin_integral hI hm x, ← hshear,
    integral_prod _ (carrierBilin_prod_integrable hI hm x)]
  rfl

/-- **THE POSITIVITY.**  Immediate, because the exact value is a sum of squares.  No
majorant, no head-versus-tail comparison, no threshold on `x`. -/
theorem autocorrelation_pairing_nonneg (hI : Integrable Psi) (hm : Measurable Psi) (x : ℝ) :
    0 ≤ ∫ u : ℝ, ∫ p : ℝ, Psi (u + p) * Psi (u - p) * Real.cos (2 * x * p) := by
  rw [autocorrelation_pairing hI hm x]
  positivity

end C3B10

section AxiomAudit
#print axioms C3B10.bilin_measurable
#print axioms C3B10.integral_norm_shift_dilate
#print axioms C3B10.bilin_slice_integrable
#print axioms C3B10.bilin_slice_norm_le
#print axioms C3B10.bilin_prod_integrable
#print axioms C3B10.carrierBilin_eq_bilin_shear
#print axioms C3B10.carrierBilin_prod_integrable
#print axioms C3B10.bilin_slice_integral
#print axioms C3B10.bilin_integral
#print axioms C3B10.autocorrelation_pairing
#print axioms C3B10.autocorrelation_pairing_nonneg
end AxiomAudit
