import c3b9_A2
import c3b4_A5

/-!
# C3 batch 9, block A3 — `hprodH`, and two independent routes at the compact leaf

## What lands here

1. **`hprodH`, the fourth side condition** (`cellDensity_triH_prod_integrable`).  A2 discharged
   `hprodG`, `hTint`, `hqTint` and routed through `sinh_pairing_nonneg_of_second_tail`, which
   does not consume `hprodH`.  It is discharged here anyway, because it is what makes the
   ramp/second-tail identity `second_tail_eq_quadratic_ramp` available **unconditionally** at
   every base point `s ≥ 0` — and that identity is what lets the two routes be *compared*
   instead of merely coexisting.  The mechanism is the separable majorant
   `|triH C (r,u)| ≤ (K e^{−πr²})·e^{(10−4π)u−3πu²}` from A2's `tailT_integrand_le`, fed to
   `MeasureTheory.Integrable.mul_prod`.

2. **The explicit window.**  `certHeight x = ½·log(20(|x|+1)²/2π)`, with
   `certHeight_spec` proving `20(|x|+1)² ≤ modeA 0 0 u` for every `u > certHeight x`.  Batch 8
   only had `exists_certified_height`; this names it, so the window `[0, certHeight x]` is a
   closed-form object (`certHeight 88 = 5.0676`, `certHeight 14.134725 = 3.2959`).

## The two routes

**ROUTE 2 — the ramp-order ladder, on `tailT`.**  `cellDensity_pos_uncond` gives pointwise
positivity of `C` above `certHeight x`, which is exactly the `hWpos` of the already-compiled
`C3B4B.sinh_pairing_nonneg_of_compact`.  So the whole chain collapses onto
`hcompact : ∀ s ∈ Icc 0 (certHeight x), 0 ≤ ∫_{Ioi s} tailT C` — see
`sinh_pairing_from_compact_window`.  The `w`-parametric form (`hU_of_window`) is also proved,
since it does not need `w = certHeight x`.

**ROUTE 1 — mode-by-mode integrated bounds, on `C` itself.**
`∫_{Ioc s w}(u−s)²/2·C(u,x)du = 16·Σ_z ∫_{Ioc s w}(u−s)²/2·modeTerm x u z du`.  The interchange
needs a `u`-uniform, `z`-summable majorant on the window; that majorant is built and proved
here (`modeBndS_window_le`) — it is `modeBndS` with `e^{5u}` and the polynomial frozen at `w`
and the exponential frozen at `s`, hence `z`-summable by the batch-7 geometric mechanism.

## The routes are NOT the same statement — route 2's hypothesis is strictly weaker

`ramp_window_le_tailT_window` proves

  `∫_{Ioc s w}(u−s)²/2·C ≤ ∫_{Ioc s w} tailT C`.

Both windows sit under the same total (`ramp_split` vs `tailT_split`), but route 1's high
piece carries `(u−s)²` while route 2's carries `(u−w)²`, and `(u−w)² ≤ (u−s)²` with `C > 0`
up there.  So route 2's window hypothesis is implied by route 1's and not conversely.  This
is stated and proved rather than asserted, because the two windows *look* like a renaming.

SCOPE: nothing here mentions `Ξ`, zeros, RH, or GRH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B9

open C3B6.Bessel
open C3B6.Theta
open C3B7
open C3B8
open CriticalLinePhasor.WeightedTail
open CriticalLinePhasor.C3B4B

/-! ### 0. The explicit certified height -/

/-- `certHeight x = ½ log(20(|x|+1)²/2π)` — the exact solution of `modeA 0 0 u = 20(|x|+1)²`. -/
def certHeight (x : ℝ) : ℝ := Real.log (20 * (|x| + 1) ^ 2 / (2 * Real.pi)) / 2

theorem certHeight_spec (x : ℝ) {u : ℝ} (hu : certHeight x < u) :
    20 * (|x| + 1) ^ 2 ≤ modeA 0 0 u := by
  have hpi := Real.pi_pos
  have hx : (0 : ℝ) < |x| + 1 := by positivity
  have hq : (0 : ℝ) < 20 * (|x| + 1) ^ 2 / (2 * Real.pi) := by positivity
  unfold certHeight at hu
  have h2 : Real.log (20 * (|x| + 1) ^ 2 / (2 * Real.pi)) < 2 * u := by linarith
  have hexp : 20 * (|x| + 1) ^ 2 / (2 * Real.pi) < Real.exp (2 * u) := by
    have h := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log hq] at h
  have hA : modeA 0 0 u = 2 * Real.pi * Real.exp (2 * u) := by
    unfold modeA
    push_cast
    ring
  rw [hA]
  have hclear := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hexp
  nlinarith [hclear]

/-- `cellDensity_pos_uncond` in the form `C3B4B.sinh_pairing_nonneg_of_compact` consumes. -/
theorem cellDensity_nonneg_above (x : ℝ) :
    ∀ u ∈ Ioi (certHeight x), 0 ≤ cellDensity x u := fun _ hu =>
  (cellDensity_pos_uncond x (certHeight_spec x hu)).le

/-! ### 1. `hprodH` — the fourth side condition -/

theorem triH_measurable {W : ℝ → ℝ} (hW : Measurable W) :
    Measurable (Function.uncurry (triH W)) := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 < z.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hf : Measurable (fun z : ℝ × ℝ => (z.2 - z.1) * W z.2) :=
    (measurable_snd.sub measurable_fst).mul (hW.comp measurable_snd)
  show Measurable (fun z : ℝ × ℝ => if z.1 < z.2 then (z.2 - z.1) * W z.2 else 0)
  exact Measurable.ite hset hf measurable_const

private theorem gauss_sq_integrable :
    Integrable (fun r : ℝ => Real.exp (-(Real.pi * r ^ 2))) := by
  have hpi := Real.pi_pos
  have h := integrable_exp_lin_quad (b := Real.pi) (c := (0 : ℝ)) hpi
  have hcongr : (fun w : ℝ => Real.exp (0 * w - Real.pi * w ^ 2))
      = fun w : ℝ => Real.exp (-(Real.pi * w ^ 2)) := by
    funext w
    congr 1
    ring
  rwa [hcongr] at h

/-- **`hprodH`.**  The triangular layer-cake kernel of the cell density is product-integrable
on `(s,∞) × (s,∞)` for every `s ≥ 0`.  Proof: the A2 envelope
`|(u−r)C(u)| ≤ K·e^{−πr²}·e^{(10−4π)u−3πu²}` is **separable**, and `triH` vanishes off
`r < u`, so a single `Integrable.mul_prod` dominates the whole kernel. -/
theorem cellDensity_triH_prod_integrable (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (Function.uncurry (triH (cellDensity x)))
      ((volume.restrict (Ioi s)).prod (volume.restrict (Ioi s))) := by
  have hpi := Real.pi_pos
  have hf : Integrable (fun r : ℝ => 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))
      * Real.exp (-(Real.pi * r ^ 2))) (volume.restrict (Ioi s)) :=
    (gauss_sq_integrable.const_mul _).integrableOn
  have hg : Integrable (fun u : ℝ =>
      Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2))
      (volume.restrict (Ioi s)) := gaussConst_integrable.integrableOn
  have hmaj := hf.mul_prod hg
  refine Integrable.mono hmaj
    (triH_measurable (cellDensity_measurable x)).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with z hz
  have hr0 : (0 : ℝ) ≤ z.1 := le_of_lt (lt_of_le_of_lt hs hz.1)
  have hmajnn : (0 : ℝ) ≤ 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))
      * Real.exp (-(Real.pi * z.1 ^ 2))
      * Real.exp ((10 - 4 * Real.pi) * z.2 - 3 * Real.pi * z.2 ^ 2) := by positivity
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hmajnn]
  by_cases hlt : z.1 < z.2
  · have heq : Function.uncurry (triH (cellDensity x)) z
        = (z.2 - z.1) * cellDensity x z.2 := by
      show triH (cellDensity x) z.1 z.2 = _
      simp only [triH, if_pos hlt]
    rw [heq]
    exact tailT_integrand_le x hr0 (le_of_lt hlt)
  · have heq : Function.uncurry (triH (cellDensity x)) z = 0 := by
      show triH (cellDensity x) z.1 z.2 = _
      simp only [triH, if_neg hlt]
    rw [heq, abs_zero]
    exact hmajnn

/-- **THE RAMP IDENTITY, UNCONDITIONALLY.**  With `hprodH` discharged, the second tail
primitive of the cell density IS the quadratic ramp, at every base point `s ≥ 0`. -/
theorem second_tail_eq_ramp (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ r in Ioi s, tailT (cellDensity x) r)
      = ∫ u in Ioi s, (u - s) ^ 2 / 2 * cellDensity x u :=
  second_tail_eq_quadratic_ramp _ s (cellDensity_triH_prod_integrable x hs)

/-! ### 2. ROUTE 2 — the ramp-order ladder on `tailT` -/

theorem tailT_integrand_integrableOn (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun u => (u - r) * cellDensity x u) (Ioi r) := by
  have hpi := Real.pi_pos
  have hmaj : IntegrableOn
      (fun u : ℝ => 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))
        * Real.exp (-(Real.pi * r ^ 2))
        * Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2)) (Ioi r) :=
    (gaussConst_integrable.integrableOn).const_mul _
  refine Integrable.mono hmaj ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (cellDensity_aestronglyMeasurable x _)
    exact (continuous_id.sub continuous_const).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := r))] with u hu
    have hnn : (0 : ℝ) ≤ 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))
        * Real.exp (-(Real.pi * r ^ 2))
        * Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2) := by positivity
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hnn]
    exact tailT_integrand_le x hr (le_of_lt hu)

/-- **ROUTE 2, the pointwise half.**  Above the certified height `tailT` is nonnegative,
because its integrand is. -/
theorem tailT_nonneg_above (x : ℝ) {r : ℝ}
    (hr : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 r) :
    0 ≤ tailT (cellDensity x) r := by
  unfold tailT
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hru : r ≤ u := le_of_lt hu
  have hAu : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 u := le_trans hr (modeA_head_mono hru)
  have hC : 0 < cellDensity x u := cellDensity_pos_uncond x hAu
  exact mul_nonneg (by linarith) hC.le

theorem tailT_split (x : ℝ) {s w : ℝ} (hs : 0 ≤ s) (hsw : s ≤ w) :
    (∫ r in Ioi s, tailT (cellDensity x) r)
      = (∫ r in Ioc s w, tailT (cellDensity x) r)
        + ∫ r in Ioi w, tailT (cellDensity x) r := by
  have hdisj : Disjoint (Ioc s w) (Ioi w) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact absurd hb (by simpa using ha.2)
  have hsub1 : Ioc s w ⊆ Ioi (0 : ℝ) := fun a ha => lt_of_le_of_lt hs ha.1
  have hsub2 : Ioi w ⊆ Ioi (0 : ℝ) := fun a ha => lt_of_le_of_lt (le_trans hs hsw) ha
  have hi1 : IntegrableOn (tailT (cellDensity x)) (Ioc s w) :=
    (tailT_integrableOn x).mono_set hsub1
  have hi2 : IntegrableOn (tailT (cellDensity x)) (Ioi w) :=
    (tailT_integrableOn x).mono_set hsub2
  rw [← Set.Ioc_union_Ioi_eq_Ioi hsw,
    setIntegral_union hdisj measurableSet_Ioi hi1 hi2]

theorem tailT_high_nonneg (x : ℝ) {w : ℝ}
    (hw : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w) :
    0 ≤ ∫ r in Ioi w, tailT (cellDensity x) r := by
  refine setIntegral_nonneg measurableSet_Ioi fun r hr => ?_
  exact tailT_nonneg_above x (le_trans hw (modeA_head_mono (le_of_lt hr)))

/-- **ROUTE 2, the `w`-parametric reduction.**  `hU` at base `s` follows from nonnegativity of
one compact integral of `tailT`, for ANY `w` clearing the certified height. -/
theorem hU_of_window (x : ℝ) {s w : ℝ} (hs : 0 ≤ s) (hsw : s ≤ w)
    (hw : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w)
    (hwin : 0 ≤ ∫ r in Ioc s w, tailT (cellDensity x) r) :
    0 ≤ ∫ r in Ioi s, tailT (cellDensity x) r := by
  rw [tailT_split x hs hsw]
  have := tailT_high_nonneg x hw
  linarith

/-- **ROUTE 2, THE COMPOSITION.**  The entire `sinh`-pairing chain rests on nonnegativity of
the second tail primitive on the CLOSED, EXPLICIT window `[0, certHeight x]`.  All six other
hypotheses of `C3B4B.sinh_pairing_nonneg_of_compact` are discharged from A2 and from
`cellDensity_pos_uncond`. -/
theorem sinh_pairing_from_compact_window (x : ℝ) {y : ℝ} (hy : 0 ≤ y)
    (hcompact : ∀ s ∈ Icc (0 : ℝ) (certHeight x),
      0 ≤ ∫ r in Ioi s, tailT (cellDensity x) r) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u :=
  sinh_pairing_nonneg_of_compact hy (cellDensity_measurable x)
    (gY_abs_cellDensity_integrableOn x hy) (tailT_prodG_integrable x hy)
    (tailT_integrableOn x) (tailT_weighted_integrableOn x hy)
    (cellDensity_nonneg_above x) hcompact

/-! ### 3. The two window hypotheses are ordered — route 2's is strictly weaker -/

theorem window_gap_nonneg (x : ℝ) {s w : ℝ} (hs : 0 ≤ s) (hsw : s ≤ w)
    (hw : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w) :
    (∫ u in Ioi w, (u - w) ^ 2 / 2 * cellDensity x u)
      ≤ ∫ u in Ioi w, (u - s) ^ 2 / 2 * cellDensity x u := by
  have hw0 : (0 : ℝ) ≤ w := le_trans hs hsw
  refine setIntegral_mono_on (cellDensity_ramp_integrableOn_all x hw0)
    ((cellDensity_ramp_integrableOn_all x hs).mono_set (Ioi_subset_Ioi hsw))
    measurableSet_Ioi ?_
  intro u hu
  have hwu : w ≤ u := le_of_lt hu
  have hC : 0 < cellDensity x u :=
    cellDensity_pos_uncond x (le_trans hw (modeA_head_mono hwu))
  have hsq : (u - w) ^ 2 ≤ (u - s) ^ 2 := by nlinarith [hsw, hwu, hs]
  nlinarith [hC.le, hsq]

/-- **THE ORDERING.**  Route 2's window quantity dominates route 1's, so route 2's
hypothesis is implied by route 1's.  They are therefore genuinely different asks, not the
same set renamed. -/
theorem ramp_window_le_tailT_window (x : ℝ) {s w : ℝ} (hs : 0 ≤ s) (hsw : s ≤ w)
    (hw : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w) :
    (∫ u in Ioc s w, (u - s) ^ 2 / 2 * cellDensity x u)
      ≤ ∫ r in Ioc s w, tailT (cellDensity x) r := by
  have hw0 : (0 : ℝ) ≤ w := le_trans hs hsw
  have h1 := ramp_split x hs hsw
  have h2 := tailT_split x hs hsw
  have h3 := second_tail_eq_ramp x hs
  have h4 := second_tail_eq_ramp x hw0
  have h5 := window_gap_nonneg x hs hsw hw
  linarith

/-! ### 4. ROUTE 1 — the `u`-uniform window majorant -/

/-- **ROUTE 1's first brick.**  On the window `Ioc s w` the mode majorant is dominated by a
`u`-**independent** quantity: `modeBndS` with `e^{5u}` and the polynomial frozen at `w`, and
the exponential frozen at `s`.  It is `z`-summable by the batch-7 geometric mechanism, since
`modeA z s = ab·modeA 0 0 s` sits in the exponent.  This is the dominated-convergence input
for `∫_{Ioc s w} Σ_z = Σ_z ∫_{Ioc s w}`. -/
theorem modeBndS_window_le (x : ℝ) {s w u : ℝ} (hsu : s ≤ u) (huw : u ≤ w) (z : ℕ × ℕ) :
    modeBndS x u z
      ≤ Real.pi ^ 2 * Real.exp (5 * w) * (((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1)) ^ 2
        * (2 * (modeA z.1 z.2 w + 3) ^ 2 * Real.exp (-modeA z.1 z.2 s)) := by
  have hpi := Real.pi_pos
  have hprod : (1 : ℝ) ≤ ((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1) := one_le_prod z.1 z.2
  have hAs : modeA z.1 z.2 s ≤ modeA z.1 z.2 u := by
    rw [modeA_factor z.1 z.2 s, modeA_factor z.1 z.2 u]
    nlinarith [modeA_head_mono hsu, hprod, modeA_head_pos s]
  have hAw : modeA z.1 z.2 u ≤ modeA z.1 z.2 w := by
    rw [modeA_factor z.1 z.2 u, modeA_factor z.1 z.2 w]
    nlinarith [modeA_head_mono huw, hprod, modeA_head_pos u]
  have hAu0 : (0 : ℝ) < modeA z.1 z.2 u := modeA_pos z.1 z.2 u
  have he5 : Real.exp (5 * u) ≤ Real.exp (5 * w) :=
    Real.exp_le_exp.mpr (by linarith)
  have heA : Real.exp (-modeA z.1 z.2 u) ≤ Real.exp (-modeA z.1 z.2 s) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsq : (modeA z.1 z.2 u + 3) ^ 2 ≤ (modeA z.1 z.2 w + 3) ^ 2 := by
    nlinarith [hAw, hAu0]
  unfold modeBndS
  have hw0 : (0 : ℝ) ≤ (((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1)) ^ 2 := by positivity
  have hstep1 : 2 * (modeA z.1 z.2 u + 3) ^ 2 * Real.exp (-modeA z.1 z.2 u)
      ≤ 2 * (modeA z.1 z.2 w + 3) ^ 2 * Real.exp (-modeA z.1 z.2 s) := by
    nlinarith [hsq, heA, Real.exp_pos (-modeA z.1 z.2 u), Real.exp_pos (-modeA z.1 z.2 s),
      sq_nonneg (modeA z.1 z.2 u + 3), sq_nonneg (modeA z.1 z.2 w + 3)]
  have hnn : (0 : ℝ) ≤ 2 * (modeA z.1 z.2 u + 3) ^ 2 * Real.exp (-modeA z.1 z.2 u) := by
    positivity
  have hpre : Real.pi ^ 2 * Real.exp (5 * u) * (((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1)) ^ 2
      ≤ Real.pi ^ 2 * Real.exp (5 * w) * (((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1)) ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he5 (by positivity)) hw0
  have hpre_nn : (0 : ℝ)
      ≤ Real.pi ^ 2 * Real.exp (5 * w) * (((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1)) ^ 2 := by
    positivity
  exact mul_le_mul hpre hstep1 hnn hpre_nn

end C3B9

section AxiomAudit
#print axioms C3B9.certHeight_spec
#print axioms C3B9.cellDensity_nonneg_above
#print axioms C3B9.triH_measurable
#print axioms C3B9.cellDensity_triH_prod_integrable
#print axioms C3B9.second_tail_eq_ramp
#print axioms C3B9.tailT_integrand_integrableOn
#print axioms C3B9.tailT_nonneg_above
#print axioms C3B9.tailT_split
#print axioms C3B9.tailT_high_nonneg
#print axioms C3B9.hU_of_window
#print axioms C3B9.sinh_pairing_from_compact_window
#print axioms C3B9.window_gap_nonneg
#print axioms C3B9.ramp_window_le_tailT_window
#print axioms C3B9.modeBndS_window_le
end AxiomAudit
