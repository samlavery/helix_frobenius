import c3b8_A3

/-!
# C3 batch 9, block A1 — the exact set-integral split of the quadratic ramp at `w`

Batch 8 left `hramp : ∀ s ≥ 0, 0 ≤ ∫ u in Ioi s, (u−s)²/2 · C(u,x)` as the leaf, and showed
(numerically, `tmp/c3b8_window_out.txt`) that `C(·,x)` genuinely changes sign below the
certified height, so the window must be handled by compensation, not pointwise positivity.

This file does two things.

**1.  Half-line integrability, without the `20 ≤ A₁(s)` hypothesis.**  Batch 8's
`C3B8.cellDensity_ramp_integrableOn` needs `20 ≤ modeA 0 0 s`, which **fails at `s = 0`**
(`modeA 0 0 0 = 2π ≈ 6.283`).  Using instead the half-line bound `C3B8.cellDensity_abs_le_simple6`
together with the Gaussian floor `A₁(u) ≥ 2π(1+2u+2u²)` (`C3B8.modeA_head_quad_lower`), the
ramp integrand is dominated by `K·exp((10−4π)u − 4πu²)` for **every** `0 ≤ s ≤ u`, which
`C3B6.Theta.integrable_exp_lin_quad` integrates.  So `cellDensity_ramp_integrableOn_all`
holds on the whole half-line — this is what `hramp` at `s = 0` actually needs.

**2.  The split.**  `Ioc s w ∪ Ioi w = Ioi s` (`Set.Ioc_union_Ioi_eq_Ioi`, orientation
checked: it needs `s ≤ w`, and the pieces are disjoint), so

  `∫_{Ioi s} = ∫_{Ioc s w} + ∫_{Ioi w}`,

the second summand is nonnegative by `C3B7.cellDensity_pos_uncond` once `w` clears the
certified height, and the leaf reduces to a **compact** integral over `Ioc s w` whose
integrand has both signs.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B9

open C3B6.Bessel
open C3B6.Theta
open C3B7
open C3B8

/-! ### 1. The half-line ramp envelope -/

theorem sq_half_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 2 / 2 ≤ Real.exp u := by
  have h := Real.quadratic_le_exp_of_nonneg hu
  linarith

/-- **The ramp envelope on the whole half-line.**  For `0 ≤ s ≤ u`,
`(u−s)²/2 · |C(u,x)| ≤ 33280π⁴e^{−2π}·exp((10−4π)u − 4πu²)`. -/
theorem ramp_abs_le (x : ℝ) {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    (u - s) ^ 2 / 2 * |cellDensity x u|
      ≤ (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)))
        * Real.exp ((10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2) := by
  have hpi := Real.pi_pos
  have hu : (0 : ℝ) ≤ u := le_trans hs hsu
  have hC := cellDensity_abs_le_simple6 x hu
  have habs : (0 : ℝ) ≤ |cellDensity x u| := abs_nonneg _
  have hramp : (u - s) ^ 2 / 2 ≤ Real.exp u := by
    have hle : (u - s) ^ 2 ≤ u ^ 2 := by nlinarith [hs, hsu, hu]
    have := sq_half_le_exp hu
    linarith
  have hramp0 : (0 : ℝ) ≤ (u - s) ^ 2 / 2 := by positivity
  have hA : Real.exp (-modeA 0 0 u)
      ≤ Real.exp (-(2 * Real.pi)) * Real.exp (-(4 * Real.pi * u))
        * Real.exp (-(4 * Real.pi * u ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := modeA_head_quad_lower hu
    nlinarith [this, hpi]
  calc (u - s) ^ 2 / 2 * |cellDensity x u|
      ≤ Real.exp u * (33280 * Real.pi ^ 4 * Real.exp (9 * u) * Real.exp (-modeA 0 0 u)) := by
        refine mul_le_mul hramp hC habs (Real.exp_pos u).le
    _ ≤ Real.exp u * (33280 * Real.pi ^ 4 * Real.exp (9 * u)
          * (Real.exp (-(2 * Real.pi)) * Real.exp (-(4 * Real.pi * u))
            * Real.exp (-(4 * Real.pi * u ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos u).le
        refine mul_le_mul_of_nonneg_left hA ?_
        positivity
    _ = (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)))
          * (Real.exp u * Real.exp (9 * u) * Real.exp (-(4 * Real.pi * u))
            * Real.exp (-(4 * Real.pi * u ^ 2))) := by ring
    _ = (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)))
          * Real.exp ((10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2) := by
        congr 1
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- **Half-line integrability of the ramp**, with no threshold hypothesis on `s`.
This is what `hramp` at `s = 0` needs and what `C3B8.cellDensity_ramp_integrableOn`
(which assumes `20 ≤ modeA 0 0 s`, false at `s = 0`) cannot supply. -/
theorem cellDensity_ramp_integrableOn_all (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun u => (u - s) ^ 2 / 2 * cellDensity x u) (Ioi s) := by
  have hpi := Real.pi_pos
  have hb : (0 : ℝ) < 4 * Real.pi := by linarith
  have hmaj0 : Integrable
      (fun u : ℝ => Real.exp ((10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2)) :=
    integrable_exp_lin_quad hb
  have hmaj : IntegrableOn
      (fun u : ℝ => (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)))
        * Real.exp ((10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2)) (Ioi s) :=
    (hmaj0.integrableOn).const_mul _
  refine Integrable.mono hmaj ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (cellDensity_aestronglyMeasurable x _)
    exact (((continuous_id.sub continuous_const).pow 2).div_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := s))] with u hu
    have hsu : s ≤ u := le_of_lt hu
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u - s) ^ 2 / 2),
      abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)))
          * Real.exp ((10 - 4 * Real.pi) * u - 4 * Real.pi * u ^ 2))]
    exact ramp_abs_le x hs hsu

/-! ### 2. The exact split -/

/-- **THE SPLIT.**  `Ioc s w ∪ Ioi w = Ioi s` for `s ≤ w`; the pieces are disjoint and both
integrable, so the set integral splits exactly. -/
theorem ramp_split (x : ℝ) {s w : ℝ} (hs : 0 ≤ s) (hsw : s ≤ w) :
    (∫ u in Ioi s, (u - s) ^ 2 / 2 * cellDensity x u)
      = (∫ u in Ioc s w, (u - s) ^ 2 / 2 * cellDensity x u)
        + ∫ u in Ioi w, (u - s) ^ 2 / 2 * cellDensity x u := by
  have hint := cellDensity_ramp_integrableOn_all x hs
  have hdisj : Disjoint (Ioc s w) (Ioi w) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact absurd hb (by simpa using ha.2)
  have hi1 : IntegrableOn (fun u => (u - s) ^ 2 / 2 * cellDensity x u) (Ioc s w) :=
    hint.mono_set Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (fun u => (u - s) ^ 2 / 2 * cellDensity x u) (Ioi w) :=
    hint.mono_set (Ioi_subset_Ioi hsw)
  rw [← Set.Ioc_union_Ioi_eq_Ioi hsw,
    setIntegral_union hdisj measurableSet_Ioi hi1 hi2]

/-- **The high tail is nonnegative.**  Above the certified height every value of the
integrand is nonnegative, by `C3B7.cellDensity_pos_uncond`. -/
theorem ramp_high_nonneg (x : ℝ) {s w : ℝ}
    (hw : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w) :
    0 ≤ ∫ u in Ioi w, (u - s) ^ 2 / 2 * cellDensity x u := by
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hwu : w ≤ u := le_of_lt hu
  have hAu : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 u :=
    le_trans hw (modeA_head_mono hwu)
  have hC : 0 < cellDensity x u := cellDensity_pos_uncond x hAu
  have hr : (0 : ℝ) ≤ (u - s) ^ 2 / 2 := by positivity
  exact mul_nonneg hr hC.le

/-- **THE REDUCTION.**  The leaf `hramp` at base point `s` follows from nonnegativity of a
single **compact** integral over `Ioc s w`, once `w` clears the certified height. -/
theorem ramp_nonneg_of_window (x : ℝ) {s w : ℝ} (hs : 0 ≤ s) (hsw : s ≤ w)
    (hw : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w)
    (hwin : 0 ≤ ∫ u in Ioc s w, (u - s) ^ 2 / 2 * cellDensity x u) :
    0 ≤ ∫ u in Ioi s, (u - s) ^ 2 / 2 * cellDensity x u := by
  rw [ramp_split x hs hsw]
  have := ramp_high_nonneg (x := x) (s := s) hw
  linarith

/-- Existence of an admissible `w`: the certified height is always reached, because
`modeA 0 0` is an unbounded increasing exponential. -/
theorem exists_certified_height (x : ℝ) (s : ℝ) :
    ∃ w : ℝ, s ≤ w ∧ 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w := by
  have hpi := Real.pi_pos
  obtain ⟨w, hw⟩ := exists_gt (max s (Real.log (20 * (|x| + 1) ^ 2) / 2))
  refine ⟨w, le_of_lt (lt_of_le_of_lt (le_max_left _ _) hw), ?_⟩
  have hlog : Real.log (20 * (|x| + 1) ^ 2) / 2 < w :=
    lt_of_le_of_lt (le_max_right _ _) hw
  have hpos : (0 : ℝ) < 20 * (|x| + 1) ^ 2 := by positivity
  have hexp : 20 * (|x| + 1) ^ 2 < Real.exp (2 * w) := by
    have h2 : Real.log (20 * (|x| + 1) ^ 2) < 2 * w := by linarith
    calc 20 * (|x| + 1) ^ 2 = Real.exp (Real.log (20 * (|x| + 1) ^ 2)) :=
          (Real.exp_log hpos).symm
      _ < Real.exp (2 * w) := Real.exp_lt_exp.mpr h2
  rw [modeA_head]
  have h3 := Real.pi_gt_three
  nlinarith [hexp, h3, Real.exp_pos (2 * w),
    mul_pos (by linarith : (0 : ℝ) < Real.pi - 3) (Real.exp_pos (2 * w))]

end C3B9

section AxiomAudit
#print axioms C3B9.sq_half_le_exp
#print axioms C3B9.ramp_abs_le
#print axioms C3B9.cellDensity_ramp_integrableOn_all
#print axioms C3B9.ramp_split
#print axioms C3B9.ramp_high_nonneg
#print axioms C3B9.ramp_nonneg_of_window
#print axioms C3B9.exists_certified_height
end AxiomAudit
