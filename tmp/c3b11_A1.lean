import c3b10_A1

/-!
# C3 batch 11, block A1 — the **two-weight** carrier pairing

`c3b10_A1` evaluates the autocorrelation pairing of a single weight against itself:

  `∫_u ∫_p Ψ(u+p)Ψ(u−p)cos(2xp) dp du = ½(cosMom Ψ x)² + ½(sinMom Ψ x)²`

— two squares, hence nonnegative.  That single-weight form is exactly what makes the
`cosh` family of batch 10 unconditional, and exactly what stops at the *value*: the
`λ`-derivative of the family is **not** a single-weight pairing, because
`∂_λ[e^{λ(u+p)}e^{λ(u−p)}]` splits the two legs of the cell apart.

This block removes that obstacle by generalising the shear engine to **two independent
legs**:

  `∫_u ∫_p P(u+p)Q(u−p)cos(2xp) dp du = ½(cosMom P x · cosMom Q x + sinMom P x · sinMom Q x)`

The proof is A1's, verbatim in structure: a translation, a dilation, and the additive
shear `(u,p) ↦ (u+p, p)`.  The determinant-2 Jacobian still appears exactly once, as the
`|2⁻¹|` of a one-dimensional dilation.  Nothing here is estimated.

Why the generalisation is the whole point: the cell centre's weight `u·sinh(2yu)` does not
factor across the two legs, but it is a **sum of four** two-leg products (block A2), so a
two-weight engine evaluates it exactly while a one-weight engine cannot see it at all.

This file is self-contained analysis: `P` and `Q` are arbitrary integrable measurable
functions.  It mentions no `Ξ`, no zeros, no arithmetic.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B11

open C3B10

/-- The two-weight pairing integrand in **sheared** coordinates `(t, p)`. -/
def bilin2 (P Q : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) : ℝ :=
  P z.1 * Q (z.1 - 2 * z.2) * Real.cos (2 * x * z.2)

/-- The two-weight pairing integrand in **carrier** coordinates `(u, p)`: the leading leg
`u+p` carries `P`, the trailing leg `u−p` carries `Q`. -/
def carrierBilin2 (P Q : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) : ℝ :=
  P (z.1 + z.2) * Q (z.1 - z.2) * Real.cos (2 * x * z.2)

variable {P Q : ℝ → ℝ}

/-! ### 1. Measurability -/

theorem bilin2_measurable (hmP : Measurable P) (hmQ : Measurable Q) (x : ℝ) :
    Measurable (bilin2 P Q x) := by
  unfold bilin2
  refine Measurable.mul (Measurable.mul (hmP.comp measurable_fst) ?_) ?_
  · exact hmQ.comp (measurable_fst.sub (measurable_const.mul measurable_snd))
  · exact Real.continuous_cos.measurable.comp (measurable_const.mul measurable_snd)

/-! ### 2. Slice integrability and the slice `L¹` bound -/

theorem bilin2_slice_integrable (hIQ : Integrable Q) (x t : ℝ) :
    Integrable (fun p : ℝ => bilin2 P Q x (t, p)) := by
  have h1 : Integrable (fun q : ℝ => Q (t - q)) := hIQ.comp_sub_left t
  have h2 : Integrable (fun p : ℝ => Q (t - 2 * p)) :=
    h1.comp_mul_left' (R := (2 : ℝ)) two_ne_zero
  have h3 : Integrable (fun p : ℝ => P t * Q (t - 2 * p)) := h2.const_mul (P t)
  refine h3.mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with p
    simpa using Real.abs_cos_le_one (2 * x * p)

theorem bilin2_slice_norm_le (hIQ : Integrable Q) (x t : ℝ) :
    (∫ p : ℝ, ‖bilin2 P Q x (t, p)‖) ≤ ‖P t‖ * (2⁻¹ * ∫ q : ℝ, ‖Q q‖) := by
  have h1 : Integrable (fun q : ℝ => Q (t - q)) := hIQ.comp_sub_left t
  have h2 : Integrable (fun p : ℝ => Q (t - 2 * p)) :=
    h1.comp_mul_left' (R := (2 : ℝ)) two_ne_zero
  have hmaj : Integrable (fun p : ℝ => ‖P t‖ * ‖Q (t - 2 * p)‖) :=
    (h2.norm).const_mul _
  have hlhs : Integrable (fun p : ℝ => ‖bilin2 P Q x (t, p)‖) :=
    (bilin2_slice_integrable hIQ x t).norm
  have hpt : ∀ p : ℝ, ‖bilin2 P Q x (t, p)‖ ≤ ‖P t‖ * ‖Q (t - 2 * p)‖ := by
    intro p
    unfold bilin2
    simp only [norm_mul]
    have hc : ‖Real.cos (2 * x * p)‖ ≤ 1 := by
      simpa using Real.abs_cos_le_one (2 * x * p)
    have h0 : (0 : ℝ) ≤ ‖P t‖ * ‖Q (t - 2 * p)‖ := by positivity
    nlinarith [hc, norm_nonneg (Real.cos (2 * x * p)), h0]
  calc (∫ p : ℝ, ‖bilin2 P Q x (t, p)‖)
      ≤ ∫ p : ℝ, ‖P t‖ * ‖Q (t - 2 * p)‖ := integral_mono hlhs hmaj hpt
    _ = ‖P t‖ * ∫ p : ℝ, ‖Q (t - 2 * p)‖ := integral_const_mul _ _
    _ = ‖P t‖ * (2⁻¹ * ∫ q : ℝ, ‖Q q‖) := by rw [integral_norm_shift_dilate]

/-! ### 3. Product integrability, both charts -/

theorem bilin2_prod_integrable (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    Integrable (bilin2 P Q x) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (bilin2 P Q x) (volume.prod volume) :=
    (bilin2_measurable hmP hmQ x).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun t => bilin2_slice_integrable hIQ x t, ?_⟩
  have hgm : AEStronglyMeasurable (fun t : ℝ => ∫ p : ℝ, ‖bilin2 P Q x (t, p)‖) volume :=
    ((bilin2_measurable hmP hmQ x).stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
  have hmaj : Integrable (fun t : ℝ => ‖P t‖ * (2⁻¹ * ∫ q : ℝ, ‖Q q‖)) :=
    (hIP.norm).mul_const _
  refine Integrable.mono hmaj hgm ?_
  filter_upwards with t
  have hnn : (0 : ℝ) ≤ ∫ p : ℝ, ‖bilin2 P Q x (t, p)‖ :=
    integral_nonneg fun p => norm_nonneg _
  have hN : (0 : ℝ) ≤ ∫ q : ℝ, ‖Q q‖ := integral_nonneg fun q => norm_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖P t‖ * (2⁻¹ * ∫ q : ℝ, ‖Q q‖))]
  exact bilin2_slice_norm_le hIQ x t

theorem carrierBilin2_eq_bilin2_shear (P Q : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) :
    carrierBilin2 P Q x z = bilin2 P Q x (z.1 + z.2, z.2) := by
  unfold carrierBilin2 bilin2
  rw [show z.1 + z.2 - 2 * z.2 = z.1 - z.2 by ring]

theorem carrierBilin2_prod_integrable (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    Integrable (carrierBilin2 P Q x) (volume.prod volume) := by
  have hS := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hb := bilin2_prod_integrable hIP hmP hIQ hmQ x
  have hcomp : Integrable (fun z : ℝ × ℝ => bilin2 P Q x (z.1 + z.2, z.2))
      (volume.prod volume) := by
    have := (integrable_map_measure
      ((bilin2_measurable hmP hmQ x).aestronglyMeasurable.mono_ac
        (by rw [hS.map_eq]))
      hS.measurable.aemeasurable).mp (by rwa [hS.map_eq])
    exact this
  refine hcomp.congr ?_
  filter_upwards with z
  exact (carrierBilin2_eq_bilin2_shear P Q x z).symm

/-! ### 4. THE EXACT EVALUATION -/

theorem bilin2_slice_integral (hIQ : Integrable Q) (x t : ℝ) :
    (∫ p : ℝ, bilin2 P Q x (t, p))
      = 2⁻¹ * (P t * Real.cos (x * t) * cosMom Q x
          + P t * Real.sin (x * t) * sinMom Q x) := by
  have hcos : Integrable (fun t' : ℝ => Q t' * Real.cos (x * t')) := by
    refine hIQ.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_cos_le_one (x * t')
  have hsin : Integrable (fun t' : ℝ => Q t' * Real.sin (x * t')) := by
    refine hIQ.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_sin_le_one (x * t')
  have hstep1 : (∫ p : ℝ, bilin2 P Q x (t, p))
      = P t * ∫ p : ℝ, (fun q : ℝ => Q (t - q) * Real.cos (x * q)) (2 * p) := by
    unfold bilin2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show P t * Q (t - 2 * p) * Real.cos (2 * x * p)
        = P t * (Q (t - 2 * p) * Real.cos (x * (2 * p)))
    rw [show x * (2 * p) = 2 * x * p by ring]
    ring
  have hstep2 : (∫ p : ℝ, (fun q : ℝ => Q (t - q) * Real.cos (x * q)) (2 * p))
      = 2⁻¹ * ∫ q : ℝ, Q (t - q) * Real.cos (x * q) := by
    have := MeasureTheory.Measure.integral_comp_mul_left
      (fun q : ℝ => Q (t - q) * Real.cos (x * q)) 2
    simp only [smul_eq_mul] at this
    rw [this]
    norm_num
  have hstep3 : (∫ q : ℝ, Q (t - q) * Real.cos (x * q))
      = ∫ t' : ℝ, Q t' * Real.cos (x * (t - t')) := by
    have := MeasureTheory.integral_sub_left_eq_self
      (fun t' : ℝ => Q t' * Real.cos (x * (t - t'))) volume t
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    show Q (t - q) * Real.cos (x * q)
        = Q (t - q) * Real.cos (x * (t - (t - q)))
    rw [show x * (t - (t - q)) = x * q by ring]
  have hstep4 : (∫ t' : ℝ, Q t' * Real.cos (x * (t - t')))
      = Real.cos (x * t) * cosMom Q x + Real.sin (x * t) * sinMom Q x := by
    have hexp : ∀ t' : ℝ, Q t' * Real.cos (x * (t - t'))
        = Real.cos (x * t) * (Q t' * Real.cos (x * t'))
          + Real.sin (x * t) * (Q t' * Real.sin (x * t')) := by
      intro t'
      rw [show x * (t - t') = x * t - x * t' by ring, Real.cos_sub]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_add (hcos.const_mul _) (hsin.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  rw [hstep1, hstep2, hstep3, hstep4]
  ring

/-- **THE TWO-WEIGHT PAIRING, EXACTLY.**  One closed form; no estimate, no truncation.
Specialising `P = Q` recovers `C3B10.bilin_integral`. -/
theorem bilin2_integral (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    (∫ z : ℝ × ℝ, bilin2 P Q x z ∂(volume.prod volume))
      = 2⁻¹ * (cosMom P x * cosMom Q x + sinMom P x * sinMom Q x) := by
  have hcos : Integrable (fun t' : ℝ => P t' * Real.cos (x * t')) := by
    refine hIP.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_cos_le_one (x * t')
  have hsin : Integrable (fun t' : ℝ => P t' * Real.sin (x * t')) := by
    refine hIP.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_sin_le_one (x * t')
  rw [integral_prod _ (bilin2_prod_integrable hIP hmP hIQ hmQ x)]
  rw [integral_congr_ae (Filter.Eventually.of_forall (bilin2_slice_integral hIQ x))]
  rw [integral_const_mul]
  have hsplit : (∫ t : ℝ, (P t * Real.cos (x * t) * cosMom Q x
        + P t * Real.sin (x * t) * sinMom Q x))
      = cosMom P x * cosMom Q x + sinMom P x * sinMom Q x := by
    rw [integral_add (hcos.mul_const _) (hsin.mul_const _),
      integral_mul_const, integral_mul_const]
    unfold cosMom sinMom
    ring
  rw [hsplit]

/-- **THE CARRIER FORM.**  The leading leg carries `P`, the trailing leg carries `Q`. -/
theorem carrier_pairing2 (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    (∫ u : ℝ, ∫ p : ℝ, P (u + p) * Q (u - p) * Real.cos (2 * x * p))
      = 2⁻¹ * (cosMom P x * cosMom Q x + sinMom P x * sinMom Q x) := by
  have hS := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hshear : (∫ z : ℝ × ℝ, carrierBilin2 P Q x z ∂(volume.prod volume))
      = ∫ z : ℝ × ℝ, bilin2 P Q x z ∂(volume.prod volume) := by
    have hmap : (∫ z : ℝ × ℝ, bilin2 P Q x z ∂(volume.prod volume))
        = ∫ z : ℝ × ℝ, bilin2 P Q x (z.1 + z.2, z.2) ∂(volume.prod volume) := by
      conv_lhs => rw [← hS.map_eq]
      exact integral_map hS.measurable.aemeasurable
        ((bilin2_measurable hmP hmQ x).aestronglyMeasurable.mono_ac (by rw [hS.map_eq]))
    rw [hmap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact carrierBilin2_eq_bilin2_shear P Q x z
  rw [← bilin2_integral hIP hmP hIQ hmQ x, ← hshear,
    integral_prod _ (carrierBilin2_prod_integrable hIP hmP hIQ hmQ x)]
  rfl

/-- The `u`-marginal of the two-weight pairing is integrable. -/
theorem carrier_pairing2_integrable (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    Integrable (fun u : ℝ => ∫ p : ℝ, P (u + p) * Q (u - p) * Real.cos (2 * x * p)) := by
  have hprod := carrierBilin2_prod_integrable hIP hmP hIQ hmQ x
  exact hprod.integral_prod_left

/-! ### 5. Parity of the moments -/

/-- Reflection invariance of Lebesgue measure, in the one-dimensional dilation form
already used for the shear: `∫ f(−t) dt = ∫ f(t) dt`. -/
theorem integral_comp_neg_self (f : ℝ → ℝ) : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
  have h := MeasureTheory.Measure.integral_comp_mul_left f (-1)
  simp only [smul_eq_mul, neg_one_mul] at h
  norm_num at h
  exact h

/-- The cosine moment of an **odd** weight vanishes. -/
theorem cosMom_of_odd {W : ℝ → ℝ} (hW : ∀ t : ℝ, W (-t) = -W t) (x : ℝ) :
    cosMom W x = 0 := by
  have h : (∫ t : ℝ, W t * Real.cos (x * t)) = -∫ t : ℝ, W t * Real.cos (x * t) := by
    conv_lhs => rw [← integral_comp_neg_self (fun t : ℝ => W t * Real.cos (x * t))]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show W (-t) * Real.cos (x * -t) = -(W t * Real.cos (x * t))
    rw [hW t, show x * -t = -(x * t) by ring, Real.cos_neg]
    ring
  unfold cosMom
  linarith [h]

/-- The sine moment of an **even** weight vanishes. -/
theorem sinMom_of_even {W : ℝ → ℝ} (hW : ∀ t : ℝ, W (-t) = W t) (x : ℝ) :
    sinMom W x = 0 := by
  have h : (∫ t : ℝ, W t * Real.sin (x * t)) = -∫ t : ℝ, W t * Real.sin (x * t) := by
    conv_lhs => rw [← integral_comp_neg_self (fun t : ℝ => W t * Real.sin (x * t))]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show W (-t) * Real.sin (x * -t) = -(W t * Real.sin (x * t))
    rw [hW t, show x * -t = -(x * t) by ring, Real.sin_neg]
    ring
  unfold sinMom
  linarith [h]

end C3B11

section AxiomAudit
#print axioms C3B11.bilin2_measurable
#print axioms C3B11.bilin2_slice_integrable
#print axioms C3B11.bilin2_slice_norm_le
#print axioms C3B11.bilin2_prod_integrable
#print axioms C3B11.carrierBilin2_eq_bilin2_shear
#print axioms C3B11.carrierBilin2_prod_integrable
#print axioms C3B11.bilin2_slice_integral
#print axioms C3B11.bilin2_integral
#print axioms C3B11.carrier_pairing2
#print axioms C3B11.carrier_pairing2_integrable
#print axioms C3B11.integral_comp_neg_self
#print axioms C3B11.cosMom_of_odd
#print axioms C3B11.sinMom_of_even
end AxiomAudit
