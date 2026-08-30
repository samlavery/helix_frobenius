import c3b8_A2
import c3b4_A4

/-!
# C3 batch 8, block A3 — TARGET C: the `WeightedTail` connection at `W = cellDensity x`

The batch-4 quadratic-ramp bridge is
`CriticalLinePhasor.C3B4B.sinh_pairing_nonneg_of_quadratic_ramp`, whose hypotheses are

  `hy      : 0 ≤ y`
  `hW      : Measurable W`
  `hint    : IntegrableOn (fun u => gY y u * |W u|) (Ioi 0)`
  `hprodG` , `hTint` , `hqTint` , `hprodH`      (tail-primitive integrability)
  `hramp   : ∀ s ≥ 0, 0 ≤ ∫ u in Ioi s, (u−s)²/2 · W u`

(The `RequestProject/WeightedTailSinhBridge.sinh_pairing_nonneg` variant is **not** usable:
its `hT` is the *linear* ramp tail, refuted in batch 4 at `T(0,60) = −2.4411…e−36`.)

This file discharges the two hypotheses that are about `cellDensity` itself:

* `cellDensity_measurable`  — from block A1's `cellDensity_stronglyMeasurable`;
* `gY_abs_cellDensity_integrableOn` — from block A2's **half-line** bound
  `|C(u,x)| ≤ 33280π⁴e^{9u}e^{−A₁(u)}` (valid for every `u ≥ 0`, not just `A₁ ≥ 20`),
  together with `A₁(u) = 2πe^{2u} ≥ 2π(1+2u+2u²)`, which converts the bound into a
  Gaussian-damped exponential `K·exp(cu − 4πu²)` that `C3B6.Theta.integrable_exp_lin_quad`
  integrates.  The `sinh` weight costs only `e^{2yu}` and `u ≤ e^u` one more, and the
  `e^{−4πu²}` factor absorbs both for every `y`.

What is NOT discharged here is `hramp` — the `U_x(s) ≥ 0` leaf — and the three
tail-primitive integrability side conditions.  `hramp` is exactly target B, whose window
part is open (`tmp/c3b8_window_out.txt` shows `cellDensity` genuinely changes sign inside
`[0, u₁(x)]`, so no pointwise-positivity argument can cover the window).

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B8

open C3B6.Bessel
open C3B6.Theta
open C3B7
open CriticalLinePhasor.WeightedTail
open CriticalLinePhasor.C3B4B

/-! ### 1. Elementary envelopes -/

theorem sinh_le_half_exp (t : ℝ) : Real.sinh t ≤ Real.exp t / 2 := by
  rw [Real.sinh_eq]
  have := Real.exp_pos (-t)
  linarith

theorem self_le_exp {u : ℝ} (hu : 0 ≤ u) : u ≤ Real.exp u := by
  have := Real.add_one_le_exp u
  linarith

/-- `A₁(u) = 2πe^{2u} ≥ 2π(1 + 2u + 2u²)` — the Gaussian floor under the head. -/
theorem modeA_head_quad_lower {u : ℝ} (hu : 0 ≤ u) :
    2 * Real.pi * (1 + 2 * u + 2 * u ^ 2) ≤ modeA 0 0 u := by
  have hpi := Real.pi_pos
  have hq : 1 + 2 * u + (2 * u) ^ 2 / 2 ≤ Real.exp (2 * u) :=
    Real.quadratic_le_exp_of_nonneg (by linarith)
  have hq' : 1 + 2 * u + 2 * u ^ 2 ≤ Real.exp (2 * u) := by nlinarith [hq]
  rw [modeA_head]
  nlinarith [hq', hpi]

/-! ### 2. The `sinh`-weighted envelope -/

/-- On `u ≥ 0` the `sinh`-weighted cell density is dominated by a Gaussian-damped
exponential, uniformly in `x` and for every `y ≥ 0`. -/
theorem gY_abs_cellDensity_le (x : ℝ) {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) :
    gY y u * |cellDensity x u|
      ≤ (33280 * Real.pi ^ 4 / 2 * Real.exp (-(2 * Real.pi)))
        * Real.exp ((2 * y + 10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2) := by
  have hpi := Real.pi_pos
  have hC := cellDensity_abs_le_simple6 x hu
  have habs : (0 : ℝ) ≤ |cellDensity x u| := abs_nonneg _
  -- gY y u ≤ e^u · e^{2yu} / 2
  have hgY : gY y u ≤ Real.exp u * Real.exp (2 * y * u) / 2 := by
    unfold gY
    have h1 : Real.sinh (2 * y * u) ≤ Real.exp (2 * y * u) / 2 := sinh_le_half_exp _
    have h2 : u ≤ Real.exp u := self_le_exp hu
    have h3 : (0 : ℝ) ≤ Real.exp (2 * y * u) / 2 := by positivity
    have h4 : (0 : ℝ) ≤ Real.sinh (2 * y * u) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr (by positivity)
    calc u * Real.sinh (2 * y * u)
        ≤ Real.exp u * Real.sinh (2 * y * u) := mul_le_mul_of_nonneg_right h2 h4
      _ ≤ Real.exp u * (Real.exp (2 * y * u) / 2) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos u).le
      _ = Real.exp u * Real.exp (2 * y * u) / 2 := by ring
  have hgY0 : (0 : ℝ) ≤ gY y u := by
    unfold gY
    have h4 : (0 : ℝ) ≤ Real.sinh (2 * y * u) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr (by positivity)
    exact mul_nonneg hu h4
  -- e^{-A₁} ≤ e^{-2π} e^{-4πu} e^{-4πu²}
  have hA : Real.exp (-modeA 0 0 u)
      ≤ Real.exp (-(2 * Real.pi)) * Real.exp (-(4 * Real.pi * u))
        * Real.exp (-(4 * Real.pi * u ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := modeA_head_quad_lower hu
    nlinarith [this, hpi]
  calc gY y u * |cellDensity x u|
      ≤ (Real.exp u * Real.exp (2 * y * u) / 2)
        * (33280 * Real.pi ^ 4 * Real.exp (9 * u) * Real.exp (-modeA 0 0 u)) := by
        refine mul_le_mul hgY hC habs ?_
        positivity
    _ ≤ (Real.exp u * Real.exp (2 * y * u) / 2)
        * (33280 * Real.pi ^ 4 * Real.exp (9 * u)
          * (Real.exp (-(2 * Real.pi)) * Real.exp (-(4 * Real.pi * u))
            * Real.exp (-(4 * Real.pi * u ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left hA ?_
        positivity
    _ = (33280 * Real.pi ^ 4 / 2 * Real.exp (-(2 * Real.pi)))
        * (Real.exp u * Real.exp (2 * y * u) * Real.exp (9 * u)
          * Real.exp (-(4 * Real.pi * u)) * Real.exp (-(4 * Real.pi * u ^ 2))) := by
        ring
    _ = (33280 * Real.pi ^ 4 / 2 * Real.exp (-(2 * Real.pi)))
        * Real.exp ((2 * y + 10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2) := by
        congr 1
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-! ### 3. The two discharged `WeightedTail` inputs -/

theorem cellDensity_measurable (x : ℝ) : Measurable (cellDensity x) :=
  (cellDensity_stronglyMeasurable x).measurable

/-- **TARGET C, input 2.**  The `sinh`-weighted cell density is integrable on the whole
half-line, for every `x` and every `y ≥ 0`. -/
theorem gY_abs_cellDensity_integrableOn (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun u => gY y u * |cellDensity x u|) (Ioi (0 : ℝ)) := by
  have hpi := Real.pi_pos
  have hb : (0 : ℝ) < 4 * Real.pi := by linarith
  have hmaj0 : Integrable
      (fun u : ℝ => Real.exp ((2 * y + 10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2)) :=
    integrable_exp_lin_quad hb
  have hmaj : IntegrableOn
      (fun u : ℝ => (33280 * Real.pi ^ 4 / 2 * Real.exp (-(2 * Real.pi)))
        * Real.exp ((2 * y + 10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2)) (Ioi (0 : ℝ)) :=
    (hmaj0.integrableOn).const_mul _
  refine Integrable.mono hmaj ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · have hg : Continuous (gY y) := by
        unfold gY
        exact continuous_id.mul
          (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
      exact hg.aestronglyMeasurable
    · exact ((cellDensity_measurable x).abs).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hle := gY_abs_cellDensity_le x hy hu0
    have hgY0 : (0 : ℝ) ≤ gY y u := by
      unfold gY
      have h4 : (0 : ℝ) ≤ Real.sinh (2 * y * u) := by
        rw [← Real.sinh_zero]
        exact Real.sinh_le_sinh.mpr (by positivity)
      exact mul_nonneg hu0 h4
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hgY0 (abs_nonneg _)),
      abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (33280 * Real.pi ^ 4 / 2 * Real.exp (-(2 * Real.pi)))
          * Real.exp ((2 * y + 10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2))]
    exact hle

/-! ### 4. TARGET C — the composition, with the remaining inputs named -/

/-- **TARGET C.**  With `W = cellDensity x`, the batch-4 quadratic-ramp bridge applies as
soon as its four tail-primitive integrability side conditions and the `U_x` leaf `hramp`
are supplied: measurability and the `sinh`-weighted integrability are now theorems.

`hramp` is the open leaf; the window part of it is genuinely open, since `cellDensity`
changes sign inside `[0, u₁(x)]` (numerically, `tmp/c3b8_window_out.txt`). -/
theorem sinh_pairing_from_cellDensity (x : ℝ) {y : ℝ} (hy : 0 ≤ y)
    (hprodG : Integrable
      (Function.uncurry (triG (tailT (cellDensity x)) (gY'' y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hTint : IntegrableOn (tailT (cellDensity x)) (Ioi (0 : ℝ)))
    (hqTint : IntegrableOn (fun r => gY'' y r * tailT (cellDensity x) r) (Ioi (0 : ℝ)))
    (hprodH : ∀ s : ℝ, 0 ≤ s → Integrable (Function.uncurry (triH (cellDensity x)))
      ((volume.restrict (Ioi s)).prod (volume.restrict (Ioi s))))
    (hramp : ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ u in Ioi s, (u - s) ^ 2 / 2 * cellDensity x u) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u :=
  sinh_pairing_nonneg_of_quadratic_ramp hy (cellDensity_measurable x)
    (gY_abs_cellDensity_integrableOn x hy) hprodG hTint hqTint hprodH hramp

end C3B8

section AxiomAudit
#print axioms C3B8.sinh_le_half_exp
#print axioms C3B8.self_le_exp
#print axioms C3B8.modeA_head_quad_lower
#print axioms C3B8.gY_abs_cellDensity_le
#print axioms C3B8.cellDensity_measurable
#print axioms C3B8.gY_abs_cellDensity_integrableOn
#print axioms C3B8.sinh_pairing_from_cellDensity
end AxiomAudit
