import c3b13_A4

/-!
# C3 batch 14, block A1 — the **convolution pairing**

Batch 13's "smallest next Lean theorem", proved here.  `C3B11.carrier_pairing2` evaluates

  `∫_u ∫_p P(u+p)Q(u−p)cos(2xp) dp du = ½(c_P c_Q + s_P s_Q)`,

with the chart clock on the **half-gap** `p`.  This block does the same with the clock on
the **cell centre** `v`:

  `∫_v [∫_p A(v+p)B(v−p) dp] cos(xv) dv = ½(c_A(x/2)·c_B(x/2) − s_A(x/2)·s_B(x/2))`.

Two things change and both are audited numerically before formalisation
(`tmp/c3b14_num1_out.txt` Part I, on kernels with **no** symmetry, so all four moment slots
are exercised):

* the moments are evaluated at **`x/2`**, not `x` — the clock now rides the centre, whose
  Jacobian against the two legs is the other one;
* the sign is a **MINUS**, not the plus of `carrier_pairing2`.  The audit prints the plus
  form alongside; it is wrong at every `x ≠ 0` (e.g. `0.7387` vs `0.9491` at `x = 1.3`).
  Worst relative error of the minus form over five ordinates: `4.6e-15`.

The mechanism behind the sign: after the shear `(v,p) ↦ (t,p) = (v+p, p)` and the dilation
`q = 2p`, the clock becomes `cos(x(t+t')/2)` on the **sum** of the two leg variables, and
`cos` of a sum carries the minus.  In `carrier_pairing2` the clock lands on the *difference*
and carries a plus.  That is the whole of it.

Proof structure is `c3b11_A1`'s, verbatim: measurability, slice integrability, the slice
`L¹` bound, product integrability, the slice integral, then the shear.  The determinant-`2`
Jacobian appears exactly once, as the `2⁻¹` of a one-dimensional dilation.

This file is self-contained analysis: `A` and `B` are arbitrary integrable measurable
functions.  It mentions no `Ξ`, no zeros, no arithmetic.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B14

open C3B10
open C3B11

/-- The convolution-pairing integrand in **sheared** coordinates `(t, p)`, `t = v + p`. -/
def convBilin (A B : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) : ℝ :=
  A z.1 * B (z.1 - 2 * z.2) * Real.cos (x * (z.1 - z.2))

/-- The convolution-pairing integrand in **carrier** coordinates `(v, p)`: the clock rides
the cell centre `v`, and the two legs `v±p` carry `A` and `B`. -/
def carrierConvBilin (A B : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) : ℝ :=
  A (z.1 + z.2) * B (z.1 - z.2) * Real.cos (x * z.1)

variable {A B : ℝ → ℝ}

/-! ### 1. Measurability -/

theorem convBilin_measurable (hmA : Measurable A) (hmB : Measurable B) (x : ℝ) :
    Measurable (convBilin A B x) := by
  unfold convBilin
  refine Measurable.mul (Measurable.mul (hmA.comp measurable_fst) ?_) ?_
  · exact hmB.comp (measurable_fst.sub (measurable_const.mul measurable_snd))
  · exact Real.continuous_cos.measurable.comp
      (measurable_const.mul (measurable_fst.sub measurable_snd))

/-! ### 2. Slice integrability and the slice `L¹` bound -/

theorem convBilin_slice_integrable (hIB : Integrable B) (x t : ℝ) :
    Integrable (fun p : ℝ => convBilin A B x (t, p)) := by
  have h1 : Integrable (fun q : ℝ => B (t - q)) := hIB.comp_sub_left t
  have h2 : Integrable (fun p : ℝ => B (t - 2 * p)) :=
    h1.comp_mul_left' (R := (2 : ℝ)) two_ne_zero
  have h3 : Integrable (fun p : ℝ => A t * B (t - 2 * p)) := h2.const_mul (A t)
  refine h3.mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_cos.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards with p
    simpa using Real.abs_cos_le_one (x * (t - p))

theorem convBilin_slice_norm_le (hIB : Integrable B) (x t : ℝ) :
    (∫ p : ℝ, ‖convBilin A B x (t, p)‖) ≤ ‖A t‖ * (2⁻¹ * ∫ q : ℝ, ‖B q‖) := by
  have h1 : Integrable (fun q : ℝ => B (t - q)) := hIB.comp_sub_left t
  have h2 : Integrable (fun p : ℝ => B (t - 2 * p)) :=
    h1.comp_mul_left' (R := (2 : ℝ)) two_ne_zero
  have hmaj : Integrable (fun p : ℝ => ‖A t‖ * ‖B (t - 2 * p)‖) := (h2.norm).const_mul _
  have hlhs : Integrable (fun p : ℝ => ‖convBilin A B x (t, p)‖) :=
    (convBilin_slice_integrable hIB x t).norm
  have hpt : ∀ p : ℝ, ‖convBilin A B x (t, p)‖ ≤ ‖A t‖ * ‖B (t - 2 * p)‖ := by
    intro p
    unfold convBilin
    simp only [norm_mul]
    have hc : ‖Real.cos (x * (t - p))‖ ≤ 1 := by
      simpa using Real.abs_cos_le_one (x * (t - p))
    have h0 : (0 : ℝ) ≤ ‖A t‖ * ‖B (t - 2 * p)‖ := by positivity
    nlinarith [hc, norm_nonneg (Real.cos (x * (t - p))), h0]
  calc (∫ p : ℝ, ‖convBilin A B x (t, p)‖)
      ≤ ∫ p : ℝ, ‖A t‖ * ‖B (t - 2 * p)‖ := integral_mono hlhs hmaj hpt
    _ = ‖A t‖ * ∫ p : ℝ, ‖B (t - 2 * p)‖ := integral_const_mul _ _
    _ = ‖A t‖ * (2⁻¹ * ∫ q : ℝ, ‖B q‖) := by rw [integral_norm_shift_dilate]

/-! ### 3. Product integrability, both charts -/

theorem convBilin_prod_integrable (hIA : Integrable A) (hmA : Measurable A)
    (hIB : Integrable B) (hmB : Measurable B) (x : ℝ) :
    Integrable (convBilin A B x) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (convBilin A B x) (volume.prod volume) :=
    (convBilin_measurable hmA hmB x).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun t => convBilin_slice_integrable hIB x t, ?_⟩
  have hgm : AEStronglyMeasurable (fun t : ℝ => ∫ p : ℝ, ‖convBilin A B x (t, p)‖) volume :=
    ((convBilin_measurable hmA hmB x).stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
  have hmaj : Integrable (fun t : ℝ => ‖A t‖ * (2⁻¹ * ∫ q : ℝ, ‖B q‖)) :=
    (hIA.norm).mul_const _
  refine Integrable.mono hmaj hgm ?_
  filter_upwards with t
  have hnn : (0 : ℝ) ≤ ∫ p : ℝ, ‖convBilin A B x (t, p)‖ :=
    integral_nonneg fun p => norm_nonneg _
  have hN : (0 : ℝ) ≤ ∫ q : ℝ, ‖B q‖ := integral_nonneg fun q => norm_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖A t‖ * (2⁻¹ * ∫ q : ℝ, ‖B q‖))]
  exact convBilin_slice_norm_le hIB x t

theorem carrierConvBilin_eq_convBilin_shear (A B : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) :
    carrierConvBilin A B x z = convBilin A B x (z.1 + z.2, z.2) := by
  unfold carrierConvBilin convBilin
  rw [show z.1 + z.2 - 2 * z.2 = z.1 - z.2 by ring, show z.1 + z.2 - z.2 = z.1 by ring]

theorem carrierConvBilin_prod_integrable (hIA : Integrable A) (hmA : Measurable A)
    (hIB : Integrable B) (hmB : Measurable B) (x : ℝ) :
    Integrable (carrierConvBilin A B x) (volume.prod volume) := by
  have hS := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hb := convBilin_prod_integrable hIA hmA hIB hmB x
  have hcomp : Integrable (fun z : ℝ × ℝ => convBilin A B x (z.1 + z.2, z.2))
      (volume.prod volume) := by
    have := (integrable_map_measure
      ((convBilin_measurable hmA hmB x).aestronglyMeasurable.mono_ac (by rw [hS.map_eq]))
      hS.measurable.aemeasurable).mp (by rwa [hS.map_eq])
    exact this
  refine hcomp.congr ?_
  filter_upwards with z
  exact (carrierConvBilin_eq_convBilin_shear A B x z).symm

/-! ### 4. THE SLICE INTEGRAL

The clock lands on the **sum** `(t + t')/2` of the two leg variables, which is where the
minus sign comes from: `cos(α+β) = cos α cos β − sin α sin β`. -/

theorem convBilin_slice_integral (hIB : Integrable B) (x t : ℝ) :
    (∫ p : ℝ, convBilin A B x (t, p))
      = A t * (2⁻¹ * (Real.cos (x / 2 * t) * cosMom B (x / 2)
          - Real.sin (x / 2 * t) * sinMom B (x / 2))) := by
  have hcos : Integrable (fun t' : ℝ => B t' * Real.cos (x / 2 * t')) := by
    refine hIB.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_cos_le_one (x / 2 * t')
  have hsin : Integrable (fun t' : ℝ => B t' * Real.sin (x / 2 * t')) := by
    refine hIB.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t'; simpa using Real.abs_sin_le_one (x / 2 * t')
  -- pull `A t` out
  have hstep1 : (∫ p : ℝ, convBilin A B x (t, p))
      = A t * ∫ p : ℝ, (fun q : ℝ => B (t - q) * Real.cos (x * (t - q / 2))) (2 * p) := by
    unfold convBilin
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show A t * B (t - 2 * p) * Real.cos (x * (t - p))
        = A t * (B (t - 2 * p) * Real.cos (x * (t - 2 * p / 2)))
    rw [show (2 : ℝ) * p / 2 = p by ring]
    ring
  -- the dilation `q = 2p`
  have hstep2 : (∫ p : ℝ, (fun q : ℝ => B (t - q) * Real.cos (x * (t - q / 2))) (2 * p))
      = 2⁻¹ * ∫ q : ℝ, B (t - q) * Real.cos (x * (t - q / 2)) := by
    have := MeasureTheory.Measure.integral_comp_mul_left
      (fun q : ℝ => B (t - q) * Real.cos (x * (t - q / 2))) 2
    simp only [smul_eq_mul] at this
    rw [this]
    norm_num
  -- the shift `t' = t − q`, which turns the clock into `cos(x(t+t')/2)`
  have hstep3 : (∫ q : ℝ, B (t - q) * Real.cos (x * (t - q / 2)))
      = ∫ t' : ℝ, B t' * Real.cos (x * (t + t') / 2) := by
    have := MeasureTheory.integral_sub_left_eq_self
      (fun t' : ℝ => B t' * Real.cos (x * (t + t') / 2)) volume t
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    show B (t - q) * Real.cos (x * (t - q / 2))
        = B (t - q) * Real.cos (x * (t + (t - q)) / 2)
    rw [show x * (t + (t - q)) / 2 = x * (t - q / 2) by ring]
  -- `cos` of a sum: THE MINUS
  have hstep4 : (∫ t' : ℝ, B t' * Real.cos (x * (t + t') / 2))
      = Real.cos (x / 2 * t) * cosMom B (x / 2)
        - Real.sin (x / 2 * t) * sinMom B (x / 2) := by
    have hexp : ∀ t' : ℝ, B t' * Real.cos (x * (t + t') / 2)
        = Real.cos (x / 2 * t) * (B t' * Real.cos (x / 2 * t'))
          - Real.sin (x / 2 * t) * (B t' * Real.sin (x / 2 * t')) := by
      intro t'
      rw [show x * (t + t') / 2 = x / 2 * t + x / 2 * t' by ring, Real.cos_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_sub (hcos.const_mul _) (hsin.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  rw [hstep1, hstep2, hstep3, hstep4]

/-! ### 5. THE EXACT EVALUATION -/

theorem convBilin_integral (hIA : Integrable A) (hmA : Measurable A)
    (hIB : Integrable B) (hmB : Measurable B) (x : ℝ) :
    (∫ z : ℝ × ℝ, convBilin A B x z ∂(volume.prod volume))
      = 2⁻¹ * (cosMom A (x / 2) * cosMom B (x / 2)
          - sinMom A (x / 2) * sinMom B (x / 2)) := by
  have hcos : Integrable (fun t : ℝ => A t * Real.cos (x / 2 * t)) := by
    refine hIA.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t; simpa using Real.abs_cos_le_one (x / 2 * t)
  have hsin : Integrable (fun t : ℝ => A t * Real.sin (x / 2 * t)) := by
    refine hIA.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t; simpa using Real.abs_sin_le_one (x / 2 * t)
  rw [integral_prod _ (convBilin_prod_integrable hIA hmA hIB hmB x)]
  rw [integral_congr_ae (Filter.Eventually.of_forall (convBilin_slice_integral hIB x))]
  have hsplit : (∫ t : ℝ, A t * (2⁻¹ * (Real.cos (x / 2 * t) * cosMom B (x / 2)
        - Real.sin (x / 2 * t) * sinMom B (x / 2))))
      = 2⁻¹ * (cosMom A (x / 2) * cosMom B (x / 2)
          - sinMom A (x / 2) * sinMom B (x / 2)) := by
    have hre : ∀ t : ℝ, A t * (2⁻¹ * (Real.cos (x / 2 * t) * cosMom B (x / 2)
          - Real.sin (x / 2 * t) * sinMom B (x / 2)))
        = 2⁻¹ * ((A t * Real.cos (x / 2 * t)) * cosMom B (x / 2))
          - 2⁻¹ * ((A t * Real.sin (x / 2 * t)) * sinMom B (x / 2)) := by
      intro t; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hre),
      integral_sub ((hcos.mul_const _).const_mul _) ((hsin.mul_const _).const_mul _),
      integral_const_mul, integral_const_mul, integral_mul_const, integral_mul_const]
    unfold cosMom sinMom
    ring
  rw [hsplit]

/-- **THE CONVOLUTION PAIRING.**  The chart clock rides the **cell centre**; the moments are
read at **half** the clock rate, and the two channels enter with a **minus**.

Contrast `C3B11.carrier_pairing2`, where the clock rides the half-gap, the moments are read
at the full rate, and the channels enter with a plus.  Both are exact; neither is an
estimate. -/
theorem carrier_conv_pairing (hIA : Integrable A) (hmA : Measurable A)
    (hIB : Integrable B) (hmB : Measurable B) (x : ℝ) :
    (∫ v : ℝ, (∫ p : ℝ, A (v + p) * B (v - p)) * Real.cos (x * v))
      = 2⁻¹ * (cosMom A (x / 2) * cosMom B (x / 2)
          - sinMom A (x / 2) * sinMom B (x / 2)) := by
  have hS := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hshear : (∫ z : ℝ × ℝ, carrierConvBilin A B x z ∂(volume.prod volume))
      = ∫ z : ℝ × ℝ, convBilin A B x z ∂(volume.prod volume) := by
    have hmap : (∫ z : ℝ × ℝ, convBilin A B x z ∂(volume.prod volume))
        = ∫ z : ℝ × ℝ, convBilin A B x (z.1 + z.2, z.2) ∂(volume.prod volume) := by
      conv_lhs => rw [← hS.map_eq]
      exact integral_map hS.measurable.aemeasurable
        ((convBilin_measurable hmA hmB x).aestronglyMeasurable.mono_ac (by rw [hS.map_eq]))
    rw [hmap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact carrierConvBilin_eq_convBilin_shear A B x z
  rw [← convBilin_integral hIA hmA hIB hmB x, ← hshear,
    integral_prod _ (carrierConvBilin_prod_integrable hIA hmA hIB hmB x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show (∫ p : ℝ, A (v + p) * B (v - p)) * Real.cos (x * v)
      = ∫ p : ℝ, carrierConvBilin A B x (v, p)
  unfold carrierConvBilin
  rw [← integral_mul_const]

/-- The `v`-marginal of the convolution pairing is integrable. -/
theorem carrier_conv_pairing_integrable (hIA : Integrable A) (hmA : Measurable A)
    (hIB : Integrable B) (hmB : Measurable B) (x : ℝ) :
    Integrable (fun v : ℝ => (∫ p : ℝ, A (v + p) * B (v - p)) * Real.cos (x * v)) := by
  have hprod := carrierConvBilin_prod_integrable hIA hmA hIB hmB x
  have h := hprod.integral_prod_left
  refine h.congr ?_
  filter_upwards with v
  show (∫ p : ℝ, carrierConvBilin A B x (v, p))
      = (∫ p : ℝ, A (v + p) * B (v - p)) * Real.cos (x * v)
  unfold carrierConvBilin
  rw [← integral_mul_const]

end C3B14

section AxiomAudit
#print axioms C3B14.convBilin_measurable
#print axioms C3B14.convBilin_slice_integrable
#print axioms C3B14.convBilin_slice_norm_le
#print axioms C3B14.convBilin_prod_integrable
#print axioms C3B14.carrierConvBilin_eq_convBilin_shear
#print axioms C3B14.carrierConvBilin_prod_integrable
#print axioms C3B14.convBilin_slice_integral
#print axioms C3B14.convBilin_integral
#print axioms C3B14.carrier_conv_pairing
#print axioms C3B14.carrier_conv_pairing_integrable
end AxiomAudit
