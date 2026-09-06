import RequestProject.RegistrationWeightBound

/-!
# Fejér tails and the gap weights in zero–station distances (ledger 610)

The Fejér kernel `F_L(u) = (1 − cos Lu)/(L u²)` is at most `2/(L u²)`, so its tails are at most
`2/(L x)` beyond `x`. For an on-line zero `ρ = ½ + iγ` this bounds the boundary-term contributions
of 609 by the distances from `γ` to the stations:

* inside the gap, `a < γ < b`:  `1 − w_ρ ≤ (2/(πL)) (1/(γ − a) + 1/(b − γ))`;
* outside, say `b < γ`:  `w_ρ ≤ (2/(πL)) · 1/(γ − b)`  and  `w_ρ ≤ (2(b − a)/(πL)) · 1/(γ − b)²`.

A zero deep inside its gap has weight near one; a zero far from the gap has weight near zero. The
boundary term is the flux imbalance between what the gap's own zeros leak out and what the outside
zeros leak in, each measured against a station at Fejér scale `1/L`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real

namespace CriticalLinePhasor.ContourArgument

theorem fejer_le {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : u ≠ 0) : fejer L u ≤ 2 / (L * u ^ 2) := by
  unfold fejer
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [Real.neg_one_le_cos (L * u)]

/-- `∫_{c}^{∞} 2/(L (x + d)²) dx = 2/(L (c + d))` for `c + d > 0`, with integrability. -/
theorem invsq_tail {L c d : ℝ} (hL : 0 < L) (hc : 0 < c + d) :
    IntegrableOn (fun x : ℝ => 2 / (L * (x + d) ^ 2)) (Ioi c) ∧
    ∫ x in Ioi c, 2 / (L * (x + d) ^ 2) = 2 / (L * (c + d)) := by
  have hderiv : ∀ x ∈ Ioi c,
      HasDerivAt (fun x : ℝ => -2 * (L * (x + d))⁻¹) (2 / (L * (x + d) ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x + d := by rw [Set.mem_Ioi] at hx; linarith
    have h1 : HasDerivAt (fun x : ℝ => L * (x + d)) L x := by
      simpa using ((hasDerivAt_id x).add_const d).const_mul L
    have h2 := (h1.inv (by positivity)).const_mul (-2)
    refine h2.congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt (fun x : ℝ => -2 * (L * (x + d))⁻¹) (Ici c) c := by
    apply ContinuousAt.continuousWithinAt
    have : L * (c + d) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have hpos : ∀ x ∈ Ioi c, 0 ≤ 2 / (L * (x + d) ^ 2) := fun x _ => by positivity
  have hlim : Tendsto (fun x : ℝ => -2 * (L * (x + d))⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => L * (x + d)) atTop atTop :=
      (tendsto_atTop_add_const_right _ d tendsto_id).const_mul_atTop hL
    have := h.inv_tendsto_atTop.const_mul (-2)
    simpa using this
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  field_simp
  ring

/-- Right tail: for `γ < b`, `∫_{b}^{∞} F_L(γ − t) dt ≤ 2/(L (b − γ))`. -/
theorem fejer_tail_right {L γ b : ℝ} (hL : 0 < L) (h : γ < b) :
    ∫ t in Ioi b, fejer L (γ - t) ≤ 2 / (L * (b - γ)) := by
  obtain ⟨hint, heq⟩ := invsq_tail hL (c := b) (d := -γ) (by linarith)
  calc ∫ t in Ioi b, fejer L (γ - t) ≤ ∫ t in Ioi b, 2 / (L * (t + -γ) ^ 2) := by
        apply setIntegral_mono_on ((fejer_integrable hL).comp_sub_left γ).integrableOn hint
          measurableSet_Ioi
        intro t ht
        have hne : γ - t ≠ 0 := by rw [Set.mem_Ioi] at ht; linarith
        calc fejer L (γ - t) ≤ 2 / (L * (γ - t) ^ 2) := fejer_le hL hne
          _ = 2 / (L * (t + -γ) ^ 2) := by ring_nf
    _ = 2 / (L * (b + -γ)) := heq
    _ = 2 / (L * (b - γ)) := by ring_nf

/-- Left tail: for `a < γ`, `∫_{−∞}^{a} F_L(γ − t) dt ≤ 2/(L (γ − a))`. -/
theorem fejer_tail_left {L γ a : ℝ} (hL : 0 < L) (h : a < γ) :
    ∫ t in Iic a, fejer L (γ - t) ≤ 2 / (L * (γ - a)) := by
  obtain ⟨hint, heq⟩ := invsq_tail hL (c := -a) (d := γ) (by linarith)
  have hrefl : ∫ t in Iic a, fejer L (γ - t) = ∫ x in Ioi (-a), fejer L (γ + x) := by
    rw [← integral_comp_neg_Iic a (fun x => fejer L (γ + x))]
    refine setIntegral_congr_fun measurableSet_Iic (fun t _ => ?_)
    show fejer L (γ - t) = fejer L (γ + -t)
    ring_nf
  rw [hrefl]
  calc ∫ x in Ioi (-a), fejer L (γ + x) ≤ ∫ x in Ioi (-a), 2 / (L * (x + γ) ^ 2) := by
        apply setIntegral_mono_on ((fejer_integrable hL).comp_add_left γ).integrableOn hint
          measurableSet_Ioi
        intro x hx
        have hne : γ + x ≠ 0 := by rw [Set.mem_Ioi] at hx; linarith
        calc fejer L (γ + x) ≤ 2 / (L * (γ + x) ^ 2) := fejer_le hL hne
          _ = 2 / (L * (x + γ) ^ 2) := by ring_nf
    _ = 2 / (L * (-a + γ)) := heq
    _ = 2 / (L * (γ - a)) := by ring_nf

/-! ## Gap weights of on-line zeros -/

/-- On the line the gap weight is the Fejér mass of the gap. -/
theorem gapWeight_eq_fejer {L : ℝ} (hL : 0 < L) (a b : ℝ) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    gapWeight L a b ρ = (1 / π) * ∫ t in a..b, fejer L (ρ.im - t) := by
  unfold gapWeight
  congr 1
  apply intervalIntegral.integral_congr_ae
  have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ ρ.im := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [h0] with t ht _
  rw [online_shift hρ t, rieszKernel_re_line_eq_fejer hL (sub_ne_zero.2 (Ne.symm ht))]

/-- The complement of the gap carries the missing mass. -/
theorem one_sub_gapWeight_eq {L : ℝ} (hL : 0 < L) (a b : ℝ) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) :
    1 - gapWeight L a b ρ
      = (1 / π) * ((∫ t in Iic a, fejer L (ρ.im - t)) + ∫ t in Ioi b, fejer L (ρ.im - t)) := by
  rw [gapWeight_eq_fejer hL a b hρ]
  have hπ := Real.pi_pos
  have hint : Integrable (fun t : ℝ => fejer L (ρ.im - t)) := (fejer_integrable hL).comp_sub_left ρ.im
  have htot : ∫ t, fejer L (ρ.im - t) = π := by
    rw [integral_sub_left_eq_self (fejer L) volume ρ.im, integral_fejer hL]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := b)
  have hsub := intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn (a := a) (b := b)
  rw [htot] at hsplit
  set X := ∫ t in Iic a, fejer L (ρ.im - t) with hX
  set Y := ∫ t in Iic b, fejer L (ρ.im - t) with hY
  set Z := ∫ t in Ioi b, fejer L (ρ.im - t) with hZ
  rw [← hsub]
  have h1 : (1 / π) * π = 1 := by field_simp
  calc 1 - (1 / π) * (Y - X) = (1 / π) * (π - (Y - X)) := by rw [mul_sub (1 / π) π (Y - X), h1]
    _ = (1 / π) * (X + Z) := by congr 1; linarith [hsplit]

/-- **Inside zero: the missing weight is at most `(2/(πL))(1/(γ − a) + 1/(b − γ))`.** -/
theorem one_sub_gapWeight_le_of_inside {L : ℝ} (hL : 0 < L) {a b : ℝ} {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (ha : a < ρ.im) (hb : ρ.im < b) :
    1 - gapWeight L a b ρ ≤ (2 / (π * L)) * (1 / (ρ.im - a) + 1 / (b - ρ.im)) := by
  rw [one_sub_gapWeight_eq hL a b hρ]
  have hπ := Real.pi_pos
  have h1 := fejer_tail_left hL ha
  have h2 := fejer_tail_right hL hb
  calc (1 / π) * ((∫ t in Iic a, fejer L (ρ.im - t)) + ∫ t in Ioi b, fejer L (ρ.im - t))
      ≤ (1 / π) * (2 / (L * (ρ.im - a)) + 2 / (L * (b - ρ.im))) := by
        apply mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = (2 / (π * L)) * (1 / (ρ.im - a) + 1 / (b - ρ.im)) := by
        have h3 : ρ.im - a ≠ 0 := by linarith
        have h4 : b - ρ.im ≠ 0 := by linarith
        field_simp

/-- **Outside zero to the right: `w_ρ ≤ (2/(πL)) · 1/(γ − b)`.** -/
theorem gapWeight_le_of_right {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (hb : b < ρ.im) :
    gapWeight L a b ρ ≤ (2 / (π * L)) * (1 / (ρ.im - b)) := by
  rw [gapWeight_eq_fejer hL a b hρ, intervalIntegral.integral_of_le hab]
  have hπ := Real.pi_pos
  have hint : Integrable (fun t : ℝ => fejer L (ρ.im - t)) := (fejer_integrable hL).comp_sub_left ρ.im
  have hsub : ∫ t in Ioc a b, fejer L (ρ.im - t) ≤ ∫ t in Iic b, fejer L (ρ.im - t) := by
    apply setIntegral_mono_set hint.integrableOn
      (Filter.Eventually.of_forall (fun t => fejer_nonneg hL _))
    exact Filter.Eventually.of_forall (fun t ht => ht.2)
  have htail := fejer_tail_left hL hb
  calc (1 / π) * ∫ t in Ioc a b, fejer L (ρ.im - t)
      ≤ (1 / π) * (2 / (L * (ρ.im - b))) :=
        mul_le_mul_of_nonneg_left (hsub.trans htail) (by positivity)
    _ = (2 / (π * L)) * (1 / (ρ.im - b)) := by
        have : ρ.im - b ≠ 0 := by linarith
        field_simp

/-- **Outside zero to the left: `w_ρ ≤ (2/(πL)) · 1/(a − γ)`.** -/
theorem gapWeight_le_of_left {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (ha : ρ.im < a) :
    gapWeight L a b ρ ≤ (2 / (π * L)) * (1 / (a - ρ.im)) := by
  rw [gapWeight_eq_fejer hL a b hρ, intervalIntegral.integral_of_le hab]
  have hπ := Real.pi_pos
  have hint : Integrable (fun t : ℝ => fejer L (ρ.im - t)) := (fejer_integrable hL).comp_sub_left ρ.im
  have hsub : ∫ t in Ioc a b, fejer L (ρ.im - t) ≤ ∫ t in Ioi a, fejer L (ρ.im - t) := by
    apply setIntegral_mono_set hint.integrableOn
      (Filter.Eventually.of_forall (fun t => fejer_nonneg hL _))
    exact Filter.Eventually.of_forall (fun t ht => ht.1)
  have htail := fejer_tail_right hL ha
  calc (1 / π) * ∫ t in Ioc a b, fejer L (ρ.im - t)
      ≤ (1 / π) * (2 / (L * (a - ρ.im))) :=
        mul_le_mul_of_nonneg_left (hsub.trans htail) (by positivity)
    _ = (2 / (π * L)) * (1 / (a - ρ.im)) := by
        have : a - ρ.im ≠ 0 := by linarith
        field_simp

/-- **Outside zero, second-moment form: `w_ρ ≤ (2(b − a)/(πL)) · 1/dist²`**, the form summable over
the zeros. -/
theorem gapWeight_le_of_right_sq {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (hb : b < ρ.im) :
    gapWeight L a b ρ ≤ (2 * (b - a) / (π * L)) * (1 / (ρ.im - b) ^ 2) := by
  rw [gapWeight_eq_fejer hL a b hρ]
  have hπ := Real.pi_pos
  have hpt : ∀ t ∈ Set.Icc a b, fejer L (ρ.im - t) ≤ 2 / (L * (ρ.im - b) ^ 2) := by
    intro t ht
    have hne : ρ.im - t ≠ 0 := by linarith [ht.2]
    calc fejer L (ρ.im - t) ≤ 2 / (L * (ρ.im - t) ^ 2) := fejer_le hL hne
      _ ≤ 2 / (L * (ρ.im - b) ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hL.le
          apply pow_le_pow_left₀ (by linarith) (by linarith [ht.2])
  have hmono := intervalIntegral.integral_mono_on hab
    ((fejer_integrable hL).comp_sub_left ρ.im).intervalIntegrable
    intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  calc (1 / π) * ∫ t in a..b, fejer L (ρ.im - t)
      ≤ (1 / π) * ((b - a) * (2 / (L * (ρ.im - b) ^ 2))) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (2 * (b - a) / (π * L)) * (1 / (ρ.im - b) ^ 2) := by
        have : ρ.im - b ≠ 0 := by linarith
        field_simp

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.one_sub_gapWeight_le_of_inside
#print axioms CriticalLinePhasor.ContourArgument.gapWeight_le_of_right
#print axioms CriticalLinePhasor.ContourArgument.gapWeight_le_of_right_sq
