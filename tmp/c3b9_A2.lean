import c3b9_A1

/-!
# C3 batch 9, block A2 — the `WeightedTail` side conditions, from `tailT` Gaussian decay

Batch 8 left five inputs of the batch-4 bridge open.  The right target is
`CriticalLinePhasor.C3B4B.sinh_pairing_nonneg_of_second_tail'` (`tmp/c3b4_A2.lean:422`),
which already packages `hprodG` out of `hTmeas` + `hscalar` via `triG_prod_integrable`.
Its inputs are

  `hy`, `hW`, `hint`      — discharged in batch 8 (`C3B8`)
  `hTmeas  : Measurable (tailT W)`
  `hscalar : IntegrableOn (fun r => (gY'' y r − 4y) * |tailT W r|) (Ioi 0)`
  `hTint   : IntegrableOn (tailT W) (Ioi 0)`
  `hqTint  : IntegrableOn (fun r => gY'' y r * tailT W r) (Ioi 0)`
  `hU      : ∀ s ≥ 0, 0 ≤ ∫ r in Ioi s, tailT W r`

All four integrability conditions come from **one** estimate, proved here:

  `|tailT (cellDensity x) r| ≤ Kgauss · e^{−π r²}`   for `r ≥ 0`   (`tailT_abs_le`)

whose mechanism is: `(u−r)|C(u,x)| ≤ K exp((10−4π)u − 4πu²)` on `u ≥ r ≥ 0` (block A1's
envelope with the `(u−r) ≤ u ≤ e^u` step), and then, **for `u ≥ r`**,
`4πu² ≥ πr² + 3πu²`, which pulls a clean `e^{−πr²}` out of the `u`-integral and leaves a
convergent Gaussian constant.

Measurability of `tailT W` is the same trick as `C3B8.cellDensity_stronglyMeasurable`:
`tailT W r = ∫ u, triH W r u` with `triH` jointly measurable, then
`MeasureTheory.StronglyMeasurable.integral_prod_right'`.

`gY'' y r = 4y·cosh(2yr) + 4y²r·sinh(2yr)` grows only exponentially, so `e^{−πr²}` absorbs
it and all three weighted conditions follow from the same bound.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
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

/-! ### 1. `tailT` as a full-line parametric integral -/

theorem tailT_eq_integral (W : ℝ → ℝ) (r : ℝ) :
    tailT W r = ∫ u : ℝ, triH W r u := by
  have hind : (fun u : ℝ => triH W r u)
      = Set.indicator (Ioi r) (fun u => (u - r) * W u) := by
    funext u
    simp [triH, Set.indicator_apply, Set.mem_Ioi]
  rw [hind, integral_indicator measurableSet_Ioi]
  rfl

theorem tailT_stronglyMeasurable (x : ℝ) :
    StronglyMeasurable (fun r : ℝ => tailT (cellDensity x) r) := by
  have hmeas : Measurable (fun q : ℝ × ℝ => triH (cellDensity x) q.1 q.2) := by
    have hset : MeasurableSet {q : ℝ × ℝ | q.1 < q.2} :=
      measurableSet_lt measurable_fst measurable_snd
    have hf : Measurable (fun q : ℝ × ℝ => (q.2 - q.1) * cellDensity x q.2) :=
      (measurable_snd.sub measurable_fst).mul
        ((cellDensity_measurable x).comp measurable_snd)
    have heq : (fun q : ℝ × ℝ => triH (cellDensity x) q.1 q.2)
        = fun q : ℝ × ℝ => if q.1 < q.2 then (q.2 - q.1) * cellDensity x q.2 else 0 := by
      funext q
      simp [triH]
    rw [heq]
    exact hf.ite hset measurable_const
  have heq2 : (fun r : ℝ => tailT (cellDensity x) r)
      = fun r : ℝ => ∫ u : ℝ, triH (cellDensity x) r u := by
    funext r
    exact tailT_eq_integral (cellDensity x) r
  rw [heq2]
  exact hmeas.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))

theorem tailT_measurable (x : ℝ) : Measurable (tailT (cellDensity x)) :=
  (tailT_stronglyMeasurable x).measurable

/-! ### 2. The Gaussian decay of `tailT` -/

/-- The Gaussian constant `∫_ℝ exp((10−4π)u − 3πu²) du`, finite and nonnegative. -/
def gaussConst : ℝ := ∫ u : ℝ, Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2)

theorem gaussConst_nonneg : 0 ≤ gaussConst := by
  unfold gaussConst
  exact integral_nonneg fun u => (Real.exp_pos _).le

theorem gaussConst_integrable :
    Integrable (fun u : ℝ => Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2)) := by
  have hpi := Real.pi_pos
  exact integrable_exp_lin_quad (by linarith : (0 : ℝ) < 3 * Real.pi)

/-- The `(u−r)`-weighted envelope, with the `e^{−πr²}` already extracted. -/
theorem tailT_integrand_le (x : ℝ) {r u : ℝ} (hr : 0 ≤ r) (hru : r ≤ u) :
    |(u - r) * cellDensity x u|
      ≤ (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))) * Real.exp (-(Real.pi * r ^ 2))
        * Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2) := by
  have hpi := Real.pi_pos
  have hu : (0 : ℝ) ≤ u := le_trans hr hru
  have hC := cellDensity_abs_le_simple6 x hu
  have habs : (0 : ℝ) ≤ |cellDensity x u| := abs_nonneg _
  have hlin : u - r ≤ Real.exp u := by
    have h1 : u - r ≤ u := by linarith
    have h2 : u ≤ Real.exp u := self_le_exp hu
    linarith
  have hlin0 : (0 : ℝ) ≤ u - r := by linarith
  have hA : Real.exp (-modeA 0 0 u)
      ≤ Real.exp (-(2 * Real.pi)) * Real.exp (-(4 * Real.pi * u))
        * Real.exp (-(4 * Real.pi * u ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := modeA_head_quad_lower hu
    nlinarith [this, hpi]
  -- 4πu² ≥ πr² + 3πu² for u ≥ r ≥ 0
  have hsplit : Real.exp (-(4 * Real.pi * u ^ 2))
      ≤ Real.exp (-(Real.pi * r ^ 2)) * Real.exp (-(3 * Real.pi * u ^ 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hru2 : r ^ 2 ≤ u ^ 2 := by nlinarith [hr, hru]
    linarith [mul_le_mul_of_nonneg_left hru2 hpi.le]
  rw [abs_mul, abs_of_nonneg hlin0]
  calc (u - r) * |cellDensity x u|
      ≤ Real.exp u * (33280 * Real.pi ^ 4 * Real.exp (9 * u) * Real.exp (-modeA 0 0 u)) := by
        exact mul_le_mul hlin hC habs (Real.exp_pos u).le
    _ ≤ Real.exp u * (33280 * Real.pi ^ 4 * Real.exp (9 * u)
          * (Real.exp (-(2 * Real.pi)) * Real.exp (-(4 * Real.pi * u))
            * Real.exp (-(4 * Real.pi * u ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos u).le
        refine mul_le_mul_of_nonneg_left hA ?_
        positivity
    _ ≤ Real.exp u * (33280 * Real.pi ^ 4 * Real.exp (9 * u)
          * (Real.exp (-(2 * Real.pi)) * Real.exp (-(4 * Real.pi * u))
            * (Real.exp (-(Real.pi * r ^ 2)) * Real.exp (-(3 * Real.pi * u ^ 2))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos u).le
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left hsplit ?_
        positivity
    _ = (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))) * Real.exp (-(Real.pi * r ^ 2))
          * (Real.exp u * Real.exp (9 * u) * Real.exp (-(4 * Real.pi * u))
            * Real.exp (-(3 * Real.pi * u ^ 2))) := by ring
    _ = (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))) * Real.exp (-(Real.pi * r ^ 2))
          * Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2) := by
        congr 1
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- **THE `tailT` DECAY BOUND.**  `|tailT (cellDensity x) r| ≤ Kgauss·e^{−πr²}` on `r ≥ 0`. -/
theorem tailT_abs_le (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    |tailT (cellDensity x) r|
      ≤ (33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi))) * gaussConst
        * Real.exp (-(Real.pi * r ^ 2)) := by
  have hpi := Real.pi_pos
  set K : ℝ := 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  have hbnd : IntegrableOn
      (fun u : ℝ => K * Real.exp (-(Real.pi * r ^ 2))
        * Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2)) (Ioi r) :=
    (gaussConst_integrable.integrableOn).const_mul _
  have hpt : ∀ u ∈ Ioi r, ‖(u - r) * cellDensity x u‖
      ≤ K * Real.exp (-(Real.pi * r ^ 2))
        * Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2) := by
    intro u hu
    rw [Real.norm_eq_abs]
    exact tailT_integrand_le x hr (le_of_lt hu)
  have hstep : |tailT (cellDensity x) r|
      ≤ ∫ u in Ioi r, K * Real.exp (-(Real.pi * r ^ 2))
          * Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2) := by
    unfold tailT
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hbnd ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := r))] with u hu
    exact hpt u hu
  refine hstep.trans ?_
  rw [integral_const_mul]
  have hsub : (∫ u in Ioi r, Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2))
      ≤ gaussConst := by
    unfold gaussConst
    refine setIntegral_le_integral gaussConst_integrable ?_
    filter_upwards with u
    exact (Real.exp_pos _).le
  have hcoef : (0 : ℝ) ≤ K * Real.exp (-(Real.pi * r ^ 2)) := by positivity
  calc K * Real.exp (-(Real.pi * r ^ 2))
        * ∫ u in Ioi r, Real.exp ((10 - 4 * Real.pi) * u - 3 * Real.pi * u ^ 2)
      ≤ K * Real.exp (-(Real.pi * r ^ 2)) * gaussConst :=
        mul_le_mul_of_nonneg_left hsub hcoef
    _ = K * gaussConst * Real.exp (-(Real.pi * r ^ 2)) := by ring

/-! ### 3. The `gY''` envelope -/

/-- `gY'' y r = 4y cosh(2yr) + 4y²r sinh(2yr) ≤ (4y + 4y²)·e^{(2y+1)r}` on `r ≥ 0`. -/
theorem gY''_le (y : ℝ) (hy : 0 ≤ y) {r : ℝ} (hr : 0 ≤ r) :
    gY'' y r ≤ (4 * y + 4 * y ^ 2) * Real.exp ((2 * y + 1) * r) := by
  have hch : Real.cosh (2 * y * r) ≤ Real.exp (2 * y * r) := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.mpr (by nlinarith [hy, hr] : -(2 * y * r) ≤ 2 * y * r)
    linarith
  have hsh : Real.sinh (2 * y * r) ≤ Real.exp (2 * y * r) := by
    rw [Real.sinh_eq]
    have h1 := Real.exp_pos (-(2 * y * r))
    have h2 := Real.exp_pos (2 * y * r)
    linarith
  have hre : r ≤ Real.exp r := self_le_exp hr
  have hE : (0 : ℝ) < Real.exp (2 * y * r) := Real.exp_pos _
  have hsh0 : (0 : ℝ) ≤ Real.sinh (2 * y * r) := by
    rw [← Real.sinh_zero]
    exact Real.sinh_le_sinh.mpr (by nlinarith [hy, hr])
  have hprod : Real.exp (2 * y * r) * Real.exp r = Real.exp ((2 * y + 1) * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gY''
  have h1 : 4 * y * Real.cosh (2 * y * r) ≤ 4 * y * Real.exp (2 * y * r) := by
    refine mul_le_mul_of_nonneg_left hch (by linarith)
  have h2 : 4 * y ^ 2 * r * Real.sinh (2 * y * r)
      ≤ 4 * y ^ 2 * (Real.exp r * Real.exp (2 * y * r)) := by
    have hr' : r * Real.sinh (2 * y * r) ≤ Real.exp r * Real.exp (2 * y * r) :=
      mul_le_mul hre hsh hsh0 (Real.exp_pos r).le
    nlinarith [hr', sq_nonneg y, hy]
  have hEr : (0 : ℝ) < Real.exp r := Real.exp_pos r
  have hone : Real.exp (2 * y * r) ≤ Real.exp ((2 * y + 1) * r) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hr]
  nlinarith [h1, h2, hprod, hone, hE, hEr, hy, sq_nonneg y]

/-! ### 4. The four side conditions -/

private theorem gauss_exp_integrableOn (c : ℝ) :
    IntegrableOn (fun r : ℝ => Real.exp (c * r) * Real.exp (-(Real.pi * r ^ 2)))
      (Ioi (0 : ℝ)) := by
  have hpi := Real.pi_pos
  have hcongr : (fun r : ℝ => Real.exp (c * r) * Real.exp (-(Real.pi * r ^ 2)))
      = fun r : ℝ => Real.exp (c * r - Real.pi * r ^ 2) := by
    funext r
    rw [← Real.exp_add]
    congr 1
  rw [hcongr]
  exact (integrable_exp_lin_quad (by linarith : (0 : ℝ) < Real.pi)).integrableOn

/-- **`hTint`.** -/
theorem tailT_integrableOn (x : ℝ) :
    IntegrableOn (tailT (cellDensity x)) (Ioi (0 : ℝ)) := by
  have hpi := Real.pi_pos
  set K : ℝ := 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)) * gaussConst with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    have := gaussConst_nonneg
    positivity
  have hmaj : IntegrableOn (fun r : ℝ => K * (Real.exp (0 * r)
      * Real.exp (-(Real.pi * r ^ 2)))) (Ioi (0 : ℝ)) :=
    (gauss_exp_integrableOn 0).const_mul _
  refine Integrable.mono hmaj (tailT_stronglyMeasurable x).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have hb := tailT_abs_le x hr0
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ K * (Real.exp (0 * r) * Real.exp (-(Real.pi * r ^ 2))))]
  simpa [hKdef, zero_mul, Real.exp_zero, one_mul, mul_assoc] using hb

/-- **`hscalar`**, from which `triG_prod_integrable` produces `hprodG`. -/
theorem tailT_scalar_integrableOn (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun r => (gY'' y r - 4 * y) * |tailT (cellDensity x) r|)
      (Ioi (0 : ℝ)) := by
  have hpi := Real.pi_pos
  set K : ℝ := 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)) * gaussConst with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    have := gaussConst_nonneg
    positivity
  set L : ℝ := (4 * y + 4 * y ^ 2) * K with hLdef
  have hL0 : (0 : ℝ) ≤ L := by
    rw [hLdef]
    have : (0 : ℝ) ≤ 4 * y + 4 * y ^ 2 := by positivity
    exact mul_nonneg this hK0
  have hmaj : IntegrableOn (fun r : ℝ => L * (Real.exp ((2 * y + 1) * r)
      * Real.exp (-(Real.pi * r ^ 2)))) (Ioi (0 : ℝ)) :=
    (gauss_exp_integrableOn (2 * y + 1)).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun r => (gY'' y r - 4 * y) * |tailT (cellDensity x) r|)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · have hc : Continuous (gY'' y) := (gY''_contDiff y).continuous
      exact (hc.sub continuous_const).aestronglyMeasurable
    · exact ((tailT_measurable x).abs).aestronglyMeasurable
  refine Integrable.mono hmaj hmeas ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have hb := tailT_abs_le x hr0
  have hg := gY''_le y hy hr0
  have hgnn : (0 : ℝ) ≤ gY'' y r - 4 * y := by
    have h4 : (0 : ℝ) ≤ 4 * y ^ 2 * r * Real.sinh (2 * y * r) := by
      have hs : (0 : ℝ) ≤ Real.sinh (2 * y * r) := by
        rw [← Real.sinh_zero]
        exact Real.sinh_le_sinh.mpr (by nlinarith [hy, hr0])
      positivity
    have hc1 : (1 : ℝ) ≤ Real.cosh (2 * y * r) := Real.one_le_cosh _
    unfold gY''
    nlinarith [h4, hc1, hy]
  have habs0 : (0 : ℝ) ≤ |tailT (cellDensity x) r| := abs_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hgnn habs0),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ L * (Real.exp ((2 * y + 1) * r) * Real.exp (-(Real.pi * r ^ 2))))]
  have hgle : gY'' y r - 4 * y ≤ (4 * y + 4 * y ^ 2) * Real.exp ((2 * y + 1) * r) := by
    linarith [hg, hy]
  calc (gY'' y r - 4 * y) * |tailT (cellDensity x) r|
      ≤ ((4 * y + 4 * y ^ 2) * Real.exp ((2 * y + 1) * r))
        * (K * Real.exp (-(Real.pi * r ^ 2))) := by
        refine mul_le_mul hgle hb habs0 ?_
        positivity
    _ = L * (Real.exp ((2 * y + 1) * r) * Real.exp (-(Real.pi * r ^ 2))) := by
        rw [hLdef]; ring

/-- **`hqTint`.** -/
theorem tailT_weighted_integrableOn (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun r => gY'' y r * tailT (cellDensity x) r) (Ioi (0 : ℝ)) := by
  have hpi := Real.pi_pos
  set K : ℝ := 33280 * Real.pi ^ 4 * Real.exp (-(2 * Real.pi)) * gaussConst with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    have := gaussConst_nonneg
    positivity
  set L : ℝ := (4 * y + 4 * y ^ 2) * K with hLdef
  have hL0 : (0 : ℝ) ≤ L := by
    rw [hLdef]
    have : (0 : ℝ) ≤ 4 * y + 4 * y ^ 2 := by positivity
    exact mul_nonneg this hK0
  have hmaj : IntegrableOn (fun r : ℝ => L * (Real.exp ((2 * y + 1) * r)
      * Real.exp (-(Real.pi * r ^ 2)))) (Ioi (0 : ℝ)) :=
    (gauss_exp_integrableOn (2 * y + 1)).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun r => gY'' y r * tailT (cellDensity x) r) (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((gY''_contDiff y).continuous).aestronglyMeasurable
    · exact (tailT_measurable x).aestronglyMeasurable
  refine Integrable.mono hmaj hmeas ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have hb := tailT_abs_le x hr0
  have hg := gY''_le y hy hr0
  have hgnn : (0 : ℝ) ≤ gY'' y r := by
    have hs : (0 : ℝ) ≤ Real.sinh (2 * y * r) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr (by nlinarith [hy, hr0])
    have hc1 : (1 : ℝ) ≤ Real.cosh (2 * y * r) := Real.one_le_cosh _
    have hcosh0 : (0 : ℝ) ≤ Real.cosh (2 * y * r) := by linarith
    unfold gY''
    nlinarith [mul_nonneg hy hcosh0, mul_nonneg (mul_nonneg (sq_nonneg y) hr0) hs]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hgnn,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ L * (Real.exp ((2 * y + 1) * r) * Real.exp (-(Real.pi * r ^ 2))))]
  calc gY'' y r * |tailT (cellDensity x) r|
      ≤ ((4 * y + 4 * y ^ 2) * Real.exp ((2 * y + 1) * r))
        * (K * Real.exp (-(Real.pi * r ^ 2))) := by
        refine mul_le_mul hg hb (abs_nonneg _) ?_
        positivity
    _ = L * (Real.exp ((2 * y + 1) * r) * Real.exp (-(Real.pi * r ^ 2))) := by
        rw [hLdef]; ring

/-- **`hprodG`**, assembled by `C3B4B.triG_prod_integrable`. -/
theorem tailT_prodG_integrable (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Integrable (Function.uncurry (triG (tailT (cellDensity x)) (gY'' y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  refine triG_prod_integrable (gY''_contDiff y) ?_ (tailT_measurable x) ?_
  · intro s hs
    rw [gY''_deriv_eq]
    exact gY'''_nonneg hy (le_of_lt hs)
  · have he : (fun r => (gY'' y r - gY'' y 0) * |tailT (cellDensity x) r|)
        = fun r => (gY'' y r - 4 * y) * |tailT (cellDensity x) r| := by
      funext r
      rw [gY_deriv2_zero]
    rw [he]
    exact tailT_scalar_integrableOn x hy

/-! ### 5. The composition: only `hU` remains -/

/-- **BATCH-9 TARGET C.**  Every input of the batch-4 second-tail bridge is now discharged
except `hU`, the second-tail nonnegativity — which is exactly the `U_x` leaf. -/
theorem sinh_pairing_from_cellDensity' (x : ℝ) {y : ℝ} (hy : 0 ≤ y)
    (hU : ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ r in Ioi s, tailT (cellDensity x) r) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u :=
  sinh_pairing_nonneg_of_second_tail hy (cellDensity_measurable x)
    (gY_abs_cellDensity_integrableOn x hy)
    (tailT_prodG_integrable x hy)
    (tailT_integrableOn x)
    (tailT_weighted_integrableOn x hy)
    hU

end C3B9

section AxiomAudit
#print axioms C3B9.tailT_eq_integral
#print axioms C3B9.tailT_stronglyMeasurable
#print axioms C3B9.tailT_measurable
#print axioms C3B9.gaussConst_nonneg
#print axioms C3B9.tailT_integrand_le
#print axioms C3B9.tailT_abs_le
#print axioms C3B9.gY''_le
#print axioms C3B9.tailT_integrableOn
#print axioms C3B9.tailT_scalar_integrableOn
#print axioms C3B9.tailT_weighted_integrableOn
#print axioms C3B9.tailT_prodG_integrable
#print axioms C3B9.sinh_pairing_from_cellDensity'
end AxiomAudit
