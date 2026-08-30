import RequestProject.WeightedTailPrimitive
import RequestProject.JKernelSignLaw

/-!
# Weighted-tail instantiation for the Xi sinh pairing

This file computes the derivatives of `g_y(u) = u sinh(2yu)`, reduces the product
integrability condition in `weighted_tail_primitive_identity` to a scalar weighted
integrability condition, and connects the resulting pairing to the J-kernel fiber.
-/

open MeasureTheory Set

noncomputable section

namespace CriticalLinePhasor.WeightedTail

/-- `g_y(u) = u sinh(2yu)`. -/
def gY (y u : ℝ) : ℝ := u * Real.sinh (2 * y * u)

/-- `g_y'(u) = sinh(2yu) + 2yu cosh(2yu)`. -/
def gY' (y u : ℝ) : ℝ := Real.sinh (2 * y * u) + 2 * y * u * Real.cosh (2 * y * u)

/-- `g_y''(u) = 4y cosh(2yu) + 4y²u sinh(2yu)`. -/
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
  have h := hs.add (hlin.mul hc)
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
  rw [gY_deriv_eq]
  simp [gY']

/-- The second derivative of `g_y` is nonnegative on the nonnegative half-line. -/
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
    funext p
    simp [Function.uncurry, triF]
  rw [heq]
  exact hf.ite hset measurable_const

/-- The inner absolute-value integral is the scalar weighted integrand. -/
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

/-- Product integrability follows from scalar integrability against `g |W|`. -/
theorem triF_prod_integrable {W g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0) (hg2 : ∀ r, 0 ≤ deriv (deriv g) r)
    (hW : Measurable W)
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
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
    have hind : (fun r : ℝ => triF W g u r)
        = Set.indicator (Set.Iio u) (fun r => (u - r) * deriv (deriv g) r * W u) := by
      funext r
      simp [triF, Set.indicator_apply, Set.mem_Iio]
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
        ext r
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi]
        tauto
      rw [hs]
      exact hIoo
    show Integrable (fun r => triF W g u r) _
    rw [hind]
    exact this
  · have hcongr : (fun u => ∫ r in Set.Ioi (0 : ℝ),
        ‖Function.uncurry (triF W g) (u, r)‖)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun u => g u * |W u| := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
      exact inner_u_abs hg hg0 hg0' hg2 hu
    exact (integrable_congr hcongr).mpr hint

/-- A nonnegative tail primitive gives a nonnegative pairing for convex test functions. -/
theorem nonneg_of_tail_nonneg {W g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0)
    (hprod : Integrable (Function.uncurry (triF W g))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hg2 : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ deriv (deriv g) r)
    (hT : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ ∫ u in Set.Ioi r, (u - r) * W u) :
    0 ≤ ∫ u in Set.Ioi (0 : ℝ), g u * W u := by
  rw [weighted_tail_primitive_identity W g hg hg0 hg0' hprod]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun r hr => ?_
  exact mul_nonneg (hg2 r hr) (hT r hr)

/-- The triangle-mixture implication instantiated at `g_y`. -/
theorem sinh_pairing_nonneg {W : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hW : Measurable W)
    (hint : IntegrableOn (fun u => gY y u * |W u|) (Set.Ioi (0 : ℝ)))
    (hT : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ ∫ u in Set.Ioi r, (u - r) * W u) :
    0 ≤ ∫ u in Set.Ioi (0 : ℝ), gY y u * W u := by
  refine nonneg_of_tail_nonneg (gY_contDiff y) (gY_zero y) (gY_deriv_zero y) ?_ ?_ hT
  · refine triF_prod_integrable (gY_contDiff y) (gY_zero y) (gY_deriv_zero y) ?_ hW hint
    intro r
    rw [gY_deriv2_eq]
    rcases le_total 0 r with hr | hr
    · exact gY_deriv2_nonneg hy hr
    · have : gY'' y r = gY'' y (-r) := by
        simp only [gY'']
        rw [show 2 * y * -r = -(2 * y * r) by ring, Real.cosh_neg, Real.sinh_neg]
        ring
      rw [this]
      exact gY_deriv2_nonneg hy (by linarith)
  · intro r hr
    rw [gY_deriv2_eq]
    exact gY_deriv2_nonneg hy (le_of_lt hr)

open CriticalLinePhasor.JKernel

/-- The nonnegative `d`-fiber weight of the J-kernel. -/
def jWeight (d u : ℝ) : ℝ := phiEven (u + d / 2) * phiEven (u - d / 2)

theorem jWeight_nonneg (d u : ℝ) : 0 ≤ jWeight d u :=
  mul_nonneg (phiEven_nonneg _) (phiEven_nonneg _)

/-- The closed J-kernel sinh form is the `g_y` weighted pairing. -/
theorem jKernel_sinh_eq_gY (d y u : ℝ) :
    2 * jKernel d (2 * u) * Real.sinh (y * (2 * u)) = 4 * (gY y u * jWeight d u) := by
  simp only [jKernel, jWeight, gY]
  rw [show (2 * u + d) / 2 = u + d / 2 by ring,
    show (2 * u - d) / 2 = u - d / 2 by ring,
    show y * (2 * u) = 2 * y * u by ring]
  ring

/-- A J-kernel fiber is nonnegative once its scalar integrability and tail conditions
are discharged. -/
theorem jKernel_fiber_nonneg_of_tail_nonneg {d y : ℝ} (hy : 0 ≤ y)
    (hW : Measurable (jWeight d))
    (hint : IntegrableOn (fun u => gY y u * |jWeight d u|) (Set.Ioi (0 : ℝ)))
    (hT : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ ∫ u in Set.Ioi r, (u - r) * jWeight d u) :
    0 ≤ ∫ u in Set.Ioi (0 : ℝ), gY y u * jWeight d u :=
  sinh_pairing_nonneg hy hW hint hT

end CriticalLinePhasor.WeightedTail

section AxiomAudit
#print axioms CriticalLinePhasor.WeightedTail.gY_deriv_eq
#print axioms CriticalLinePhasor.WeightedTail.gY_deriv2_eq
#print axioms CriticalLinePhasor.WeightedTail.gY_deriv2_nonneg
#print axioms CriticalLinePhasor.WeightedTail.inner_u_abs
#print axioms CriticalLinePhasor.WeightedTail.triF_prod_integrable
#print axioms CriticalLinePhasor.WeightedTail.nonneg_of_tail_nonneg
#print axioms CriticalLinePhasor.WeightedTail.sinh_pairing_nonneg
#print axioms CriticalLinePhasor.WeightedTail.jWeight_nonneg
#print axioms CriticalLinePhasor.WeightedTail.jKernel_sinh_eq_gY
#print axioms CriticalLinePhasor.WeightedTail.jKernel_fiber_nonneg_of_tail_nonneg
end AxiomAudit
