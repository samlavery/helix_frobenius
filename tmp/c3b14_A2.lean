import c3b14_A1

/-!
# C3 batch 14, block A2 — the **R kernel** and the exact `cosMom_Rker` identity

`R(v) := ∫ p² Φ(v+p)Φ(v−p) dp` — the second half-gap moment of the carrier product at cell
centre `v`.  Its integrand is a product of three nonnegative factors, so `R ≥ 0` **pointwise
and by inspection**.  This block proves

  `cosMom R (2x) = ¼ ( cosMom Φ x · cosMom kM2 x + sinMom kM1 x ² )`,

i.e. **the first Laguerre expression of the readout is the cosine transform of one explicit
nonnegative even function.**  With batch 12's `momentTwo_eq` this also says
`cosMom R (2x) = 2·∫_{(0,∞)} u²C(x,u)du`.

## The mechanism, and where the `−2` goes

Transposing batch 12's quadratic split from the centre to the gap,
`4p² = ((v+p) − (v−p))²` gives

  `4p²Φ(v+p)Φ(v−p) = kM2(v+p)Φ(v−p) − 2·kM1(v+p)kM1(v−p) + Φ(v+p)kM2(v−p)`

— note the **minus** on the cross term, where batch 12's centre split
(`(2u)² = ((u+p)+(u−p))²`) has a plus.  Each leg is then evaluated by `carrier_conv_pairing`
at clock `2x`, which reads the moments at `(2x)/2 = x` and contributes its own **minus**
between the cosine and sine channels.  The two minuses multiply on the cross term:

  `−2 · ½(cosMom kM1 x ² − sinMom kM1 x ²) = −2 · ½(0 − s₁²) = + s₁²`,

which is exactly how the manifest **square** `sinMom kM1 x ²` appears with a plus sign in a
formula every one of whose ingredients carries a minus.  Parity does the rest:
`cosMom kM1 = 0`, `sinMom Φ = 0`, `sinMom kM2 = 0`.

## Factor audit

Every constant was checked by direct quadrature **before** this file was written
(`tmp/c3b14_num1_out.txt` Part II): the `¼` form matches to `5.9e-16` at six ordinates, and
the competing `½` and `⅛` forms are printed alongside and are wrong by exactly a factor `2`.
`R ≥ 0` and `R` even were checked on the same grid (`max |R(v)−R(−v)| = 6.2e-17`).

SCOPE: one definition, its parity/sign/integrability, and one exact identity.  Nothing here
decides the sign of `cosMom R (2x)`, which is the OPEN target.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B14

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B6.Theta
open C3B10
open C3B11
open C3B12
open C3B13

/-! ### 1. Slice integrability of a bare two-leg product -/

/-- The clock-free specialisation of batch 11's `slice_ae`: for a.e. cell centre the bare
two-leg product is integrable in the half-gap. -/
theorem pair_slice_ae {P Q : ℝ → ℝ} (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) :
    ∀ᵐ v : ℝ, Integrable (fun p : ℝ => P (v + p) * Q (v - p)) := by
  filter_upwards [slice_ae hIP hmP hIQ hmQ 0] with v hv
  refine hv.congr ?_
  filter_upwards with p
  rw [show (2 : ℝ) * 0 * p = 0 by ring, Real.cos_zero, mul_one]

/-! ### 2. The kernel -/

/-- **THE `R` KERNEL.**  The second half-gap moment of the carrier product. -/
def Rker (v : ℝ) : ℝ := ∫ p : ℝ, p ^ 2 * (riemannXiKernel (v + p) * riemannXiKernel (v - p))

/-- **NONNEGATIVE, POINTWISE AND BY INSPECTION.**  Three nonnegative factors. -/
theorem Rker_nonneg (v : ℝ) : 0 ≤ Rker v := by
  refine integral_nonneg fun p => ?_
  have h1 := xiKernel_nonneg (v + p)
  have h2 := xiKernel_nonneg (v - p)
  positivity

/-- **EVEN**, directly from `riemannXiKernel_neg` — no change of variables needed: the two
legs simply exchange. -/
theorem Rker_even (v : ℝ) : Rker (-v) = Rker v := by
  unfold Rker
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show p ^ 2 * (riemannXiKernel (-v + p) * riemannXiKernel (-v - p))
      = p ^ 2 * (riemannXiKernel (v + p) * riemannXiKernel (v - p))
  have h1 : riemannXiKernel (-v + p) = riemannXiKernel (v - p) := by
    rw [show -v + p = -(v - p) by ring, riemannXiKernel_neg]
  have h2 : riemannXiKernel (-v - p) = riemannXiKernel (v + p) := by
    rw [show -v - p = -(v + p) by ring, riemannXiKernel_neg]
  rw [h1, h2]
  ring

/-! ### 3. The gap split — the transpose of batch 12's centre split -/

/-- `4p² = ((v+p) − (v−p))²`, read on the two legs.  **Minus** on the cross term. -/
theorem cell_p2_split (v p : ℝ) :
    kM2 (v + p) * riemannXiKernel (v - p) - 2 * (kM1 (v + p) * kM1 (v - p))
      + riemannXiKernel (v + p) * kM2 (v - p)
      = 4 * (p ^ 2 * (riemannXiKernel (v + p) * riemannXiKernel (v - p))) := by
  unfold kM1 kM2
  ring

/-- The three legs, each in the exact shape `carrier_conv_pairing` consumes. -/
def rleg (P Q : ℝ → ℝ) (x v : ℝ) : ℝ :=
  (∫ p : ℝ, P (v + p) * Q (v - p)) * Real.cos (2 * x * v)

theorem rleg_integrable {P Q : ℝ → ℝ} (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) : Integrable (rleg P Q x) :=
  carrier_conv_pairing_integrable hIP hmP hIQ hmQ (2 * x)

theorem rleg_value {P Q : ℝ → ℝ} (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    (∫ v : ℝ, rleg P Q x v)
      = 2⁻¹ * (cosMom P x * cosMom Q x - sinMom P x * sinMom Q x) := by
  have h := carrier_conv_pairing hIP hmP hIQ hmQ (2 * x)
  rw [show (2 : ℝ) * x / 2 = x by ring] at h
  exact h

/-! ### 4. The a.e. decomposition of the clocked kernel -/

theorem Rker_ae (x : ℝ) :
    (fun v : ℝ => Rker v * Real.cos (2 * x * v))
      =ᵐ[volume] fun v : ℝ => 4⁻¹ * (rleg kM2 riemannXiKernel x v
          - 2 * rleg kM1 kM1 x v + rleg riemannXiKernel kM2 x v) := by
  filter_upwards [pair_slice_ae kM2_integrable kM2_measurable
      xiKernel_integrable riemannXiKernel_measurable,
    pair_slice_ae kM1_integrable kM1_measurable kM1_integrable kM1_measurable,
    pair_slice_ae xiKernel_integrable riemannXiKernel_measurable
      kM2_integrable kM2_measurable] with v h1 h2 h3
  have hsplit : Rker v
      = 4⁻¹ * ((∫ p : ℝ, kM2 (v + p) * riemannXiKernel (v - p))
          - 2 * (∫ p : ℝ, kM1 (v + p) * kM1 (v - p))
          + ∫ p : ℝ, riemannXiKernel (v + p) * kM2 (v - p)) := by
    unfold Rker
    have hA : (∫ p : ℝ, p ^ 2 * (riemannXiKernel (v + p) * riemannXiKernel (v - p)))
        = ∫ p : ℝ, 4⁻¹ * (kM2 (v + p) * riemannXiKernel (v - p)
            - 2 * (kM1 (v + p) * kM1 (v - p))
            + riemannXiKernel (v + p) * kM2 (v - p)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      have h := cell_p2_split v p
      linear_combination (-(1 : ℝ) / 4) * h
    have h2' : Integrable (fun p : ℝ => 2 * (kM1 (v + p) * kM1 (v - p))) := h2.const_mul 2
    have hsub : (∫ p : ℝ, kM2 (v + p) * riemannXiKernel (v - p)
          - 2 * (kM1 (v + p) * kM1 (v - p)))
        = (∫ p : ℝ, kM2 (v + p) * riemannXiKernel (v - p))
          - ∫ p : ℝ, 2 * (kM1 (v + p) * kM1 (v - p)) := integral_sub h1 h2'
    have hadd : (∫ p : ℝ, (kM2 (v + p) * riemannXiKernel (v - p)
            - 2 * (kM1 (v + p) * kM1 (v - p)))
          + riemannXiKernel (v + p) * kM2 (v - p))
        = (∫ p : ℝ, kM2 (v + p) * riemannXiKernel (v - p)
            - 2 * (kM1 (v + p) * kM1 (v - p)))
          + ∫ p : ℝ, riemannXiKernel (v + p) * kM2 (v - p) := integral_add (h1.sub h2') h3
    have hc : (∫ p : ℝ, 2 * (kM1 (v + p) * kM1 (v - p)))
        = 2 * ∫ p : ℝ, kM1 (v + p) * kM1 (v - p) := integral_const_mul _ _
    rw [hA, integral_const_mul, hadd, hsub, hc]
  show Rker v * Real.cos (2 * x * v)
      = 4⁻¹ * (rleg kM2 riemannXiKernel x v
          - 2 * rleg kM1 kM1 x v + rleg riemannXiKernel kM2 x v)
  unfold rleg
  rw [hsplit]
  ring

/-- `R` is genuinely integrable — so `cosMom Rker` is a real evaluation, not Lean's
zero-convention on a non-integrable function. -/
theorem Rker_integrable : Integrable Rker := by
  have h := Rker_ae 0
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one] at h
  have hj1 := rleg_integrable kM2_integrable kM2_measurable
    xiKernel_integrable riemannXiKernel_measurable 0
  have hj2 := rleg_integrable kM1_integrable kM1_measurable kM1_integrable kM1_measurable 0
  have hj3 := rleg_integrable xiKernel_integrable riemannXiKernel_measurable
    kM2_integrable kM2_measurable 0
  have : Integrable (fun v : ℝ => 4⁻¹ * (rleg kM2 riemannXiKernel 0 v
      - 2 * rleg kM1 kM1 0 v + rleg riemannXiKernel kM2 0 v)) :=
    (((hj1.sub (hj2.const_mul 2)).add hj3).const_mul _)
  exact this.congr h.symm

/-! ### 5. THE IDENTITY -/

/-- **THE FIRST LAGUERRE EXPRESSION IS THE COSINE TRANSFORM OF A NONNEGATIVE FUNCTION.**
Hypotheses: none.  Every constant audited numerically before formalisation. -/
theorem cosMom_Rker (x : ℝ) :
    cosMom Rker (2 * x)
      = 4⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2) := by
  have hj1 := rleg_integrable kM2_integrable kM2_measurable
    xiKernel_integrable riemannXiKernel_measurable x
  have hj2 := rleg_integrable kM1_integrable kM1_measurable kM1_integrable kM1_measurable x
  have hj3 := rleg_integrable xiKernel_integrable riemannXiKernel_measurable
    kM2_integrable kM2_measurable x
  have v1 := rleg_value kM2_integrable kM2_measurable
    xiKernel_integrable riemannXiKernel_measurable x
  have v2 := rleg_value kM1_integrable kM1_measurable kM1_integrable kM1_measurable x
  have v3 := rleg_value xiKernel_integrable riemannXiKernel_measurable
    kM2_integrable kM2_measurable x
  have hcos : cosMom Rker (2 * x) = ∫ v : ℝ, Rker v * Real.cos (2 * x * v) := rfl
  have b12 : (∫ v : ℝ, rleg kM2 riemannXiKernel x v - 2 * rleg kM1 kM1 x v)
      = (∫ v : ℝ, rleg kM2 riemannXiKernel x v) - ∫ v : ℝ, 2 * rleg kM1 kM1 x v :=
    integral_sub hj1 (hj2.const_mul 2)
  have b123 : (∫ v : ℝ, (rleg kM2 riemannXiKernel x v - 2 * rleg kM1 kM1 x v)
        + rleg riemannXiKernel kM2 x v)
      = (∫ v : ℝ, rleg kM2 riemannXiKernel x v - 2 * rleg kM1 kM1 x v)
        + ∫ v : ℝ, rleg riemannXiKernel kM2 x v :=
    integral_add (hj1.sub (hj2.const_mul 2)) hj3
  have bc : (∫ v : ℝ, 2 * rleg kM1 kM1 x v) = 2 * ∫ v : ℝ, rleg kM1 kM1 x v :=
    integral_const_mul _ _
  rw [hcos, integral_congr_ae (Rker_ae x), integral_const_mul, b123, b12, bc,
    v1, v2, v3, cosMom_kM1 x, sinMom_xiKernel x, sinMom_kM2 x]
  ring

/-- The bridge to batch 12: `cosMom R (2x)` is twice the compiled second moment. -/
theorem cosMom_Rker_eq_two_momentTwo (x : ℝ) :
    cosMom Rker (2 * x) = 2 * ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  rw [cosMom_Rker x, momentTwo_eq x]
  ring

/-! ### 6. The normal form, and the two facts it makes free -/

/-- **THE TARGET, IN NORMAL FORM.**  The OPEN inequality is *exactly* the statement that the
explicit nonnegative even function `R` is positive definite at the frequency `2x`. -/
theorem target_iff_cosMom_Rker_nonneg (x : ℝ) :
    (0 ≤ cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2)
      ↔ 0 ≤ cosMom Rker (2 * x) := by
  rw [cosMom_Rker x]
  constructor <;> intro h <;> linarith

/-- At `x = 0` the transform is the mass, so the `x = 0` fibre is immediate from `R ≥ 0`
alone — recovering `C3B12.momentTwo_zero_nonneg` with no positivity computation. -/
theorem cosMom_Rker_zero_nonneg : 0 ≤ cosMom Rker 0 := by
  have h : cosMom Rker 0 = ∫ v : ℝ, Rker v := by
    unfold cosMom
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show Rker v * Real.cos (0 * v) = Rker v
    rw [zero_mul, Real.cos_zero, mul_one]
  rw [h]
  exact integral_nonneg fun v => Rker_nonneg v

/-- **THE SHARP TWO-SIDED BOUND, RE-DERIVED FROM `R ≥ 0`.**  `|∫R cos| ≤ ∫R`.  Batch 13
reached this constant by cell-density domination; here it is the one-line consequence of the
normal form, which is an independent second route to the same sharp constant. -/
theorem cosMom_Rker_abs_le (x : ℝ) : |cosMom Rker (2 * x)| ≤ cosMom Rker 0 := by
  have hb : |cosMom Rker (2 * x)| ≤ cosMom Rker 0 :=
    cosMom_abs_le_mass Rker_integrable Rker_nonneg (2 * x)
  exact hb

end C3B14

section AxiomAudit
#print axioms C3B14.pair_slice_ae
#print axioms C3B14.Rker_nonneg
#print axioms C3B14.Rker_even
#print axioms C3B14.cell_p2_split
#print axioms C3B14.rleg_integrable
#print axioms C3B14.rleg_value
#print axioms C3B14.Rker_ae
#print axioms C3B14.Rker_integrable
#print axioms C3B14.cosMom_Rker
#print axioms C3B14.cosMom_Rker_eq_two_momentTwo
#print axioms C3B14.target_iff_cosMom_Rker_nonneg
#print axioms C3B14.cosMom_Rker_zero_nonneg
#print axioms C3B14.cosMom_Rker_abs_le
end AxiomAudit
