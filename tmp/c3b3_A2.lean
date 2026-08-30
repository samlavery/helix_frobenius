import RequestProject.WeightedTailPrimitive

/-!
# C3 batch 3, attacks C-Lean — the triangle-mixture law, and `g_y(u) = u·sinh(2yu)`

Three things, all abstract real analysis (no `Ξ`, no zeros):

* `gY` — the requested test function `g_y(u) = u sinh(2yu)`, with its first and second
  derivatives computed as *functions* (`gY_deriv_eq`, `gY_deriv2_eq`), the two vanishing
  conditions `g 0 = 0`, `g′ 0 = 0`, and `g″ ≥ 0` on `[0,∞)` for `y ≥ 0`.

* `triF_prod_integrable` — the product-integrability side condition of
  `weighted_tail_primitive_identity` REDUCED, for convex `g` vanishing to second order,
  to the single scalar hypothesis `∫_{u>0} g u · |W u| < ∞`.  This is the honest form of
  "Φ-decay integrability": the triangle integrand is integrable exactly when the weight
  is integrable against `g` itself, because `∫_0^u (u−r) g″(r) dr = g u`.

* `nonneg_of_tail_nonneg` — **the triangle-mixture law**: if the tail primitive
  `T r = ∫_{u>r}(u−r)·W u` is `≥ 0` for every `r > 0` and `g″ ≥ 0`, then
  `∫_{u>0} g·W ≥ 0`.  Ramps are the extreme rays of the cone of such `g`, so this is
  the exact sense in which "positivity of the ramp form" is the whole content.

* `sinh_pairing_nonneg` — the instantiation at `g_y`.
-/

open MeasureTheory Set

noncomputable section

namespace CriticalLinePhasor.WeightedTail

/-! ## The test function `g_y(u) = u · sinh (2 y u)` -/

/-- `g_y(u) = u · sinh (2 y u)`. -/
def gY (y u : ℝ) : ℝ := u * Real.sinh (2 * y * u)

/-- `g_y′(u) = sinh(2yu) + 2yu·cosh(2yu)`. -/
def gY' (y u : ℝ) : ℝ := Real.sinh (2 * y * u) + 2 * y * u * Real.cosh (2 * y * u)

/-- `g_y″(u) = 4y·cosh(2yu) + 4y²u·sinh(2yu)`. -/
def gY'' (y u : ℝ) : ℝ :=
  4 * y * Real.cosh (2 * y * u) + 4 * y ^ 2 * u * Real.sinh (2 * y * u)

theorem gY_hasDerivAt (y u : ℝ) : HasDerivAt (gY y) (gY' y u) u := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * y * t) (2 * y) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * y)
  have hs : HasDerivAt (fun t : ℝ => Real.sinh (2 * y * t))
      (Real.cosh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_sinh (2 * y * u)).comp u hlin
  have h := (hasDerivAt_id u).mul hs
  refine h.congr_deriv ?_
  simp only [gY', id_eq]
  ring

theorem gY'_hasDerivAt (y u : ℝ) : HasDerivAt (gY' y) (gY'' y u) u := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * y * t) (2 * y) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * y)
  have hs : HasDerivAt (fun t : ℝ => Real.sinh (2 * y * t))
      (Real.cosh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_sinh (2 * y * u)).comp u hlin
  have hc : HasDerivAt (fun t : ℝ => Real.cosh (2 * y * t))
      (Real.sinh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_cosh (2 * y * u)).comp u hlin
  have hlin2 : HasDerivAt (fun t : ℝ => 2 * y * t) (2 * y) u := hlin
  have h := hs.add ((hlin2.mul hc))
  refine h.congr_deriv ?_
  simp only [gY'']
  ring

theorem gY_deriv_eq (y : ℝ) : deriv (gY y) = gY' y :=
  funext fun u => (gY_hasDerivAt y u).deriv

theorem gY_deriv2_eq (y : ℝ) : deriv (deriv (gY y)) = gY'' y := by
  rw [gY_deriv_eq]
  exact funext fun u => (gY'_hasDerivAt y u).deriv

theorem gY_contDiff (y : ℝ) : ContDiff ℝ 2 (gY y) := by
  have h1 : ContDiff ℝ 2 (fun t : ℝ => 2 * y * t) := contDiff_const.mul contDiff_id
  exact contDiff_id.mul (Real.contDiff_sinh.comp h1)

theorem gY_zero (y : ℝ) : gY y 0 = 0 := by simp [gY]

theorem gY_deriv_zero (y : ℝ) : deriv (gY y) 0 = 0 := by
  rw [gY_deriv_eq]; simp [gY']

/-- **`g_y″ ≥ 0` on `[0,∞)` for `y ≥ 0`** — the convexity that drives the mixture law. -/
theorem gY_deriv2_nonneg {y : ℝ} (hy : 0 ≤ y) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ gY'' y u := by
  have h1 : 0 ≤ 4 * y * Real.cosh (2 * y * u) :=
    mul_nonneg (by linarith) (Real.cosh_pos _).le
  have h2 : 0 ≤ 4 * y ^ 2 * u * Real.sinh (2 * y * u) := by
    have hs : 0 ≤ Real.sinh (2 * y * u) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr (by positivity)
    have : 0 ≤ 4 * y ^ 2 * u := by positivity
    exact mul_nonneg this hs
  simp only [gY'']
  linarith

/-! ## Product integrability of the triangle integrand -/

theorem triF_measurable {W g : ℝ → ℝ} (hW : Measurable W)
    (hg2 : Continuous (deriv (deriv g))) :
    Measurable (Function.uncurry (triF W g)) := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have hf : Measurable (fun p : ℝ × ℝ =>
      (p.1 - p.2) * deriv (deriv g) p.2 * W p.1) :=
    ((measurable_fst.sub measurable_snd).mul (hg2.measurable.comp measurable_snd)).mul
      (hW.comp measurable_fst)
  have heq : (Function.uncurry (triF W g)) = fun p : ℝ × ℝ =>
      if p.2 < p.1 then (p.1 - p.2) * deriv (deriv g) p.2 * W p.1 else 0 := by
    funext p; simp [Function.uncurry, triF]
  rw [heq]
  exact hf.ite hset measurable_const

/-- The inner `r`-integral of the ABSOLUTE VALUE is `g u · |W u|`, because
`∫_0^u (u−r) g″(r) dr = g u` when `g″ ≥ 0`. -/
theorem inner_u_abs {W g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0) (hg2 : ∀ r, 0 ≤ deriv (deriv g) r) {u : ℝ} (hu : 0 < u) :
    ∫ r in Set.Ioi (0 : ℝ), ‖triF W g u r‖ = g u * |W u| := by
  have hpt : (fun r => ‖triF W g u r‖) = fun r => triF (fun t => |W t|) g u r := by
    funext r
    by_cases hr : r < u
    · have h1 : (0 : ℝ) ≤ u - r := by linarith
      simp only [triF, if_pos hr, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg h1, abs_of_nonneg (hg2 r)]
    · simp [triF, if_neg hr]
  rw [hpt]
  exact inner_u (fun t => |W t|) g hg hg0 hg0' hu

/-- **Φ-decay integrability, reduced.**  For `g` of class `C²` vanishing to second order
with `g″ ≥ 0`, the product-integrability side condition of the weighted-tail identity is
*equivalent in practice* to the single scalar bound `∫_{u>0} g u · |W u| < ∞`. -/
theorem triF_prod_integrable {W g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0) (hg2 : ∀ r, 0 ≤ deriv (deriv g) r)
    (hW : Measurable W) (hWc : Continuous W)
    (hint : IntegrableOn (fun u => g u * |W u|) (Set.Ioi (0 : ℝ))) :
    Integrable (Function.uncurry (triF W g))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  have hg1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hcont2 : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hmeas : AEStronglyMeasurable (Function.uncurry (triF W g))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    (triF_measurable hW hcont2).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with u hu
    have hind : (fun r : ℝ => triF W g u r)
        = Set.indicator (Set.Iio u) (fun r => (u - r) * deriv (deriv g) r * W u) := by
      funext r; simp [triF, Set.indicator_apply, Set.mem_Iio]
    have hcont : Continuous (fun r : ℝ => (u - r) * deriv (deriv g) r * W u) :=
      ((continuous_const.sub continuous_id).mul hcont2).mul continuous_const
    have hIoo : IntegrableOn (fun r : ℝ => (u - r) * deriv (deriv g) r * W u)
        (Set.Ioo (0 : ℝ) u) :=
      (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have : IntegrableOn (Set.indicator (Set.Iio u)
        (fun r => (u - r) * deriv (deriv g) r * W u)) (Set.Ioi (0 : ℝ)) := by
      rw [IntegrableOn, MeasureTheory.integrable_indicator_iff measurableSet_Iio,
        IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
      have hs : Set.Iio u ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 u := by
        ext r; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi]; tauto
      rw [hs]
      exact hIoo
    show Integrable (fun r => triF W g u r) _
    rw [hind]
    exact this
  · have hcongr : (fun u => ∫ r in Set.Ioi (0:ℝ), ‖Function.uncurry (triF W g) (u, r)‖)
        =ᵐ[volume.restrict (Set.Ioi (0:ℝ))] fun u => g u * |W u| := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with u hu
      exact inner_u_abs hg hg0 hg0' hg2 hu
    exact (integrable_congr hcongr).mpr hint

/-! ## The triangle-mixture law -/

/-- **THE TRIANGLE-MIXTURE LAW.**  If the tail primitive of `W` is nonnegative at every
positive `r`, then `∫_{u>0} g·W ≥ 0` for every `C²` `g` vanishing to second order at `0`
with `g″ ≥ 0` on `(0,∞)`.  Ramps `(u−r)_+` are the extreme rays of that cone, so the
positivity of the ramp form carries the entire content. -/
theorem nonneg_of_tail_nonneg {W g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0)
    (hprod : Integrable (Function.uncurry (triF W g))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))))
    (hg2 : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ deriv (deriv g) r)
    (hT : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ ∫ u in Set.Ioi r, (u - r) * W u) :
    0 ≤ ∫ u in Set.Ioi (0:ℝ), g u * W u := by
  rw [weighted_tail_primitive_identity W g hg hg0 hg0' hprod]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun r hr => ?_
  exact mul_nonneg (hg2 r hr) (hT r hr)

/-- **The instantiation at `g_y(u) = u sinh(2yu)`.**  Nonnegativity of the tail primitive
gives nonnegativity of the `sinh`-weighted pairing at every `y ≥ 0`. -/
theorem sinh_pairing_nonneg {W : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hW : Measurable W) (hWc : Continuous W)
    (hint : IntegrableOn (fun u => gY y u * |W u|) (Set.Ioi (0 : ℝ)))
    (hT : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ ∫ u in Set.Ioi r, (u - r) * W u) :
    0 ≤ ∫ u in Set.Ioi (0:ℝ), gY y u * W u := by
  refine nonneg_of_tail_nonneg (gY_contDiff y) (gY_zero y) (gY_deriv_zero y) ?_ ?_ hT
  · refine triF_prod_integrable (gY_contDiff y) (gY_zero y) (gY_deriv_zero y) ?_ hW hWc hint
    intro r
    rw [gY_deriv2_eq]
    rcases le_total 0 r with hr | hr
    · exact gY_deriv2_nonneg hy hr
    · -- `g_y″` is even, so nonnegativity on `[0,∞)` gives it on all of `ℝ`
      have : gY'' y r = gY'' y (-r) := by
        simp only [gY'']
        rw [show 2 * y * -r = -(2 * y * r) by ring, Real.cosh_neg, Real.sinh_neg]
        ring
      rw [this]
      exact gY_deriv2_nonneg hy (by linarith)
  · intro r hr
    rw [gY_deriv2_eq]
    exact gY_deriv2_nonneg hy (le_of_lt hr)

end CriticalLinePhasor.WeightedTail

section AxiomAudit
#print axioms CriticalLinePhasor.WeightedTail.gY_deriv_eq
#print axioms CriticalLinePhasor.WeightedTail.gY_deriv2_eq
#print axioms CriticalLinePhasor.WeightedTail.gY_deriv2_nonneg
#print axioms CriticalLinePhasor.WeightedTail.inner_u_abs
#print axioms CriticalLinePhasor.WeightedTail.triF_prod_integrable
#print axioms CriticalLinePhasor.WeightedTail.nonneg_of_tail_nonneg
#print axioms CriticalLinePhasor.WeightedTail.sinh_pairing_nonneg
end AxiomAudit
