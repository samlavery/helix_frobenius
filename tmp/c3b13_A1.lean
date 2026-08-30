import c3b12_A2

/-!
# C3 batch 13, block A1 — unconditional moment bounds, and the **thickened zero fibre**

TARGET, unfolded to plain mathematics.  With `Ξ(x) := ∫ Φ(t) cos(xt) dt` the readout of
the Riemann theta kernel, the batch-12 dictionary (`c₀ = Ξ`, `s₁ = −Ξ′`, `c₂ = −Ξ″`, verified
this batch to `6.7e-53` at five ordinates, and `cosMom riemannXiKernel x = 2·ξ(½+ix)`
**exactly**, measured to `1e-61`) turns

  `0 ≤ cosMom Φ x * cosMom kM2 x + sinMom kM1 x ^ 2`

into `0 ≤ Ξ′(x)² − Ξ(x)Ξ″(x)`: the **first Laguerre inequality** for the Riemann Ξ-function.

Batch 12 discharged it on the *exact* fibre `{Ξ = 0}` (`momentTwo_eq_sq_of_cosMom_zero`).
This block weakens that *equality* hypothesis to an **inequality** hypothesis, using two
unconditional sup bounds that cost nothing:

* `|cosMom W x| ≤ cosMom W 0` for every nonnegative integrable `W` — because `|cos| ≤ 1`;
* applied to `Φ ≥ 0` and to `kM2 = t²Φ ≥ 0`, and to `|kM1| = |t|Φ ≥ 0` for the sine channel.

> **SCOPE, CORRECTED (OpenAI adjudication, 2026-08-25).**  What is compiled below is a
> **conditional criterion**: an unconditional *implication* whose hypothesis
> `c₂(0)·|c₀(x)| ≤ s₁(x)²` is a real inequality that is **not proved to hold at any `x`**
> anywhere in this repository.  An earlier version of this header said the criterion "holds
> on a genuine neighbourhood" of each real zero.  **That is withdrawn as stated**: deducing
> a *neighbourhood* additionally requires **continuity** of `x ↦ cosMom Φ x` and
> `x ↦ sinMom kM1 x`, and **`Ξ′(γ) ≠ 0`** (simplicity of the zero).  Neither is formalised
> here, so the interval reading is **numerical and unformalised**.

Measured (not proved) half-widths, §B6 of `tmp/c3b13_num1_out.txt`: `6.0e-2` at
`γ₁ = 14.1347`, `7.7e-4` at `γ₂`, `5.5e-5` at `γ₃`, falling to `6.7e-20` at `γ₁₂`; the
hypothesis is verifiable at `2/1201` points of a uniform grid on `[0,60]`.  **That reach is
small and is reported as small.**  What is genuinely new here is that the two sup bounds
`|c₀(x)| ≤ c₀(0)` and `|c₂(x)| ≤ c₂(0)` are unconditional, and that the criterion's
hypothesis is an inequality rather than an equation.

SCOPE: three sup bounds, one two-sided bound on the moment, one thickened fibre.  Nothing
here decides the general sign, and nothing here mentions zeros of `ζ`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B13

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B6.Theta
open C3B10
open C3B11
open C3B12

/-! ### 1. The sup bound for a nonnegative weight -/

/-- If `W ≥ 0` is integrable then every cosine moment is dominated by the mass.
`|cos| ≤ 1`, nothing else. -/
theorem cosMom_abs_le_mass {W : ℝ → ℝ} (hW : Integrable W) (hpos : ∀ t : ℝ, 0 ≤ W t) (x : ℝ) :
    |cosMom W x| ≤ cosMom W 0 := by
  have hprod : Integrable (fun t : ℝ => W t * Real.cos (x * t)) := by
    refine hW.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t; simpa using Real.abs_cos_le_one (x * t)
  rw [cosMom_at_zero W]
  have h1 : |∫ t : ℝ, W t * Real.cos (x * t)| ≤ ∫ t : ℝ, |W t * Real.cos (x * t)| :=
    abs_integral_le_integral_abs
  have h2 : (∫ t : ℝ, |W t * Real.cos (x * t)|) ≤ ∫ t : ℝ, W t := by
    refine integral_mono hprod.abs hW fun t => ?_
    rw [abs_mul, abs_of_nonneg (hpos t)]
    nlinarith [Real.abs_cos_le_one (x * t), hpos t, abs_nonneg (Real.cos (x * t))]
  exact le_trans h1 h2

/-- Same statement for the sine channel. -/
theorem sinMom_abs_le_mass {W : ℝ → ℝ} (hW : Integrable W) (hpos : ∀ t : ℝ, 0 ≤ W t) (x : ℝ) :
    |sinMom W x| ≤ cosMom W 0 := by
  have hprod : Integrable (fun t : ℝ => W t * Real.sin (x * t)) := by
    refine hW.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t; simpa using Real.abs_sin_le_one (x * t)
  rw [cosMom_at_zero W]
  have h1 : |∫ t : ℝ, W t * Real.sin (x * t)| ≤ ∫ t : ℝ, |W t * Real.sin (x * t)| :=
    abs_integral_le_integral_abs
  have h2 : (∫ t : ℝ, |W t * Real.sin (x * t)|) ≤ ∫ t : ℝ, W t := by
    refine integral_mono hprod.abs hW fun t => ?_
    rw [abs_mul, abs_of_nonneg (hpos t)]
    nlinarith [Real.abs_sin_le_one (x * t), hpos t, abs_nonneg (Real.sin (x * t))]
  exact le_trans h1 h2

/-! ### 2. The three instances at the Riemann kernel -/

theorem xiKernel_nonneg (t : ℝ) : 0 ≤ riemannXiKernel t :=
  (C3B5.A1.riemannXiKernel_pos_all t).le

theorem kM2_nonneg (t : ℝ) : 0 ≤ kM2 t := by
  unfold kM2
  have := xiKernel_nonneg t
  positivity

/-- `|Ξ(x)| ≤ Ξ(0)`. -/
theorem cosMom_xiKernel_abs_le (x : ℝ) :
    |cosMom riemannXiKernel x| ≤ cosMom riemannXiKernel 0 :=
  cosMom_abs_le_mass xiKernel_integrable xiKernel_nonneg x

/-- `|Ξ″(x)| ≤ |Ξ″(0)|`. -/
theorem cosMom_kM2_abs_le (x : ℝ) : |cosMom kM2 x| ≤ cosMom kM2 0 :=
  cosMom_abs_le_mass kM2_integrable kM2_nonneg x

theorem cosMom_kM2_zero_nonneg : 0 ≤ cosMom kM2 0 :=
  le_trans (abs_nonneg _) (cosMom_kM2_abs_le 0)

theorem cosMom_xiKernel_zero_nonneg : 0 ≤ cosMom riemannXiKernel 0 :=
  le_trans (abs_nonneg _) (cosMom_xiKernel_abs_le 0)

/-- The absolute first weight `|t|Φ`, nonnegative, integrable, and equal to `|kM1|`. -/
def kA1 (t : ℝ) : ℝ := |t| * riemannXiKernel t

theorem kA1_nonneg (t : ℝ) : 0 ≤ kA1 t := by
  unfold kA1
  have := xiKernel_nonneg t
  positivity

theorem kA1_eq_abs_kM1 (t : ℝ) : kA1 t = |kM1 t| := by
  unfold kA1 kM1
  rw [abs_mul, abs_of_nonneg (xiKernel_nonneg t)]

theorem kA1_integrable : Integrable kA1 := by
  refine kM1_integrable.abs.congr ?_
  filter_upwards with t
  exact (kA1_eq_abs_kM1 t).symm

/-- `|Ξ′(x)| ≤ ∫|t|Φ`. -/
theorem sinMom_kM1_abs_le (x : ℝ) : |sinMom kM1 x| ≤ cosMom kA1 0 := by
  have hb : |sinMom kA1 x| ≤ cosMom kA1 0 := sinMom_abs_le_mass kA1_integrable kA1_nonneg x
  -- `|sinMom kM1 x| ≤ ∫|kM1| = ∫ kA1 = cosMom kA1 0`, directly.
  have hprod : Integrable (fun t : ℝ => kM1 t * Real.sin (x * t)) := by
    refine kM1_integrable.mul_bdd (c := 1) ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with t; simpa using Real.abs_sin_le_one (x * t)
  rw [cosMom_at_zero kA1]
  have h1 : |∫ t : ℝ, kM1 t * Real.sin (x * t)| ≤ ∫ t : ℝ, |kM1 t * Real.sin (x * t)| :=
    abs_integral_le_integral_abs
  have h2 : (∫ t : ℝ, |kM1 t * Real.sin (x * t)|) ≤ ∫ t : ℝ, kA1 t := by
    refine integral_mono hprod.abs kA1_integrable fun t => ?_
    rw [abs_mul, kA1_eq_abs_kM1 t]
    nlinarith [Real.abs_sin_le_one (x * t), abs_nonneg (kM1 t), abs_nonneg (Real.sin (x * t))]
  exact le_trans h1 h2

/-! ### 3. The two-sided bound on the second moment -/

/-- **AN UNCONDITIONAL TWO-SIDED BOUND.**  The second moment of the cell density is
sandwiched by explicit `x = 0` data:  `−⅛·c₀(0)c₂(0) ≤ ∫ u²C ≤ ⅛(c₀(0)c₂(0) + (∫|t|Φ)²)`.
Every constant is a mass of a nonnegative weight; no zero location enters. -/
theorem momentTwo_abs_bound (x : ℝ) :
    |∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u|
      ≤ 8⁻¹ * (cosMom riemannXiKernel 0 * cosMom kM2 0 + cosMom kA1 0 ^ 2) := by
  rw [momentTwo_eq x]
  have h0 := cosMom_xiKernel_abs_le x
  have h2 := cosMom_kM2_abs_le x
  have h1 := sinMom_kM1_abs_le x
  have hp0 : (0 : ℝ) ≤ cosMom riemannXiKernel 0 := cosMom_xiKernel_zero_nonneg
  have hp2 : (0 : ℝ) ≤ cosMom kM2 0 := cosMom_kM2_zero_nonneg
  have hprod : |cosMom riemannXiKernel x * cosMom kM2 x|
      ≤ cosMom riemannXiKernel 0 * cosMom kM2 0 := by
    rw [abs_mul]
    exact mul_le_mul h0 h2 (abs_nonneg _) hp0
  have hsq : sinMom kM1 x ^ 2 ≤ cosMom kA1 0 ^ 2 := by
    have habs : |sinMom kM1 x| ≤ cosMom kA1 0 := h1
    nlinarith [abs_nonneg (sinMom kM1 x), sq_abs (sinMom kM1 x), habs]
  have hnn : (0 : ℝ) ≤ sinMom kM1 x ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor
  · have := abs_le.mp hprod
    nlinarith [this.1, hnn, sq_nonneg (cosMom kA1 0)]
  · have := abs_le.mp hprod
    nlinarith [this.2, hsq]

/-! ### 4. THE ZERO CRITERION, WITH AN INEQUALITY HYPOTHESIS -/

/-- **THE ZERO CRITERION.**  Batch 12 proved nonnegativity under the *equality*
`cosMom Φ x = 0`; here the hypothesis is an *inequality*, which is logically weaker, so the
implication is logically stronger.

The bound `|c₂(x)| ≤ c₂(0)` is what makes the implication unconditional — it uses only
`t²Φ ≥ 0` and `|cos| ≤ 1`.

**This is a criterion, not a discharged region.**  No theorem here asserts that the
hypothesis holds at any `x`.  Reading it as covering a *neighbourhood* of a real zero `γ`
additionally needs continuity of `x ↦ cosMom Φ x` and `x ↦ sinMom kM1 x`, and `Ξ′(γ) ≠ 0`;
neither is formalised here, so that reading is numerical only. -/
theorem momentTwo_nonneg_of_thickened {x : ℝ}
    (h : cosMom kM2 0 * |cosMom riemannXiKernel x| ≤ sinMom kM1 x ^ 2) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  rw [momentTwo_eq x]
  have h2 := cosMom_kM2_abs_le x
  have hp2 : (0 : ℝ) ≤ cosMom kM2 0 := cosMom_kM2_zero_nonneg
  have hkey : -(cosMom kM2 0 * |cosMom riemannXiKernel x|)
      ≤ cosMom riemannXiKernel x * cosMom kM2 x := by
    have hb : |cosMom riemannXiKernel x * cosMom kM2 x|
        ≤ |cosMom riemannXiKernel x| * cosMom kM2 0 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have := (abs_le.mp hb).1
    nlinarith [this]
  nlinarith [hkey, h]

/-- Batch 12's exact fibre is the `|c₀(x)| = 0` corner of the thickened one — recorded so
the strengthening is visible, and proved *through* the new criterion. -/
theorem momentTwo_nonneg_of_cosMom_zero' {x : ℝ} (hx : cosMom riemannXiKernel x = 0) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  refine momentTwo_nonneg_of_thickened ?_
  rw [hx, abs_zero, mul_zero]
  exact sq_nonneg _

/-- The criterion in the form actually used numerically: a bound on `|Ξ(x)|` alone. -/
theorem momentTwo_nonneg_of_small_readout {x : ℝ} (hpos : 0 < cosMom kM2 0)
    (h : |cosMom riemannXiKernel x| ≤ sinMom kM1 x ^ 2 / cosMom kM2 0) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  refine momentTwo_nonneg_of_thickened ?_
  rw [← le_div_iff₀' hpos]
  exact h

end C3B13

section AxiomAudit
#print axioms C3B13.cosMom_abs_le_mass
#print axioms C3B13.sinMom_abs_le_mass
#print axioms C3B13.xiKernel_nonneg
#print axioms C3B13.kM2_nonneg
#print axioms C3B13.cosMom_xiKernel_abs_le
#print axioms C3B13.cosMom_kM2_abs_le
#print axioms C3B13.cosMom_kM2_zero_nonneg
#print axioms C3B13.cosMom_xiKernel_zero_nonneg
#print axioms C3B13.kA1_nonneg
#print axioms C3B13.kA1_eq_abs_kM1
#print axioms C3B13.kA1_integrable
#print axioms C3B13.sinMom_kM1_abs_le
#print axioms C3B13.momentTwo_abs_bound
#print axioms C3B13.momentTwo_nonneg_of_thickened
#print axioms C3B13.momentTwo_nonneg_of_cosMom_zero'
#print axioms C3B13.momentTwo_nonneg_of_small_readout
end AxiomAudit
