import RequestProject.ClosedForm

open Complex Filter Topology MeasureTheory
open scoped BigOperators

namespace CriticalLinePhasor.CarrierHeadFiniteFiber

noncomputable def physicalHead (y : ℝ) : ℝ := Geometry.Nindex 1 3 y

theorem physicalHead_lower (y : ℝ) :
    9 * (Real.exp y) ^ 2 ≤ physicalHead y := by
  have hs : ∀ t : ℝ, 0 ≤ t → 6 * Real.pi * t ≤ Geometry.speed 1 3 t := by
    intro t ht
    unfold Geometry.speed
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    nlinarith [sq_nonneg (6 * Real.pi * t)]
  have hint : (∫ t in (0 : ℝ)..Real.exp y, 6 * Real.pi * t) ≤
      ∫ t in (0 : ℝ)..Real.exp y, Geometry.speed 1 3 t := by
    apply intervalIntegral.integral_mono_on (Real.exp_pos y).le
    · exact (by fun_prop : Continuous (fun t : ℝ => 6 * Real.pi * t)).intervalIntegrable _ _
    · exact (by unfold Geometry.speed; fun_prop : Continuous (Geometry.speed 1 3)).intervalIntegrable _ _
    · intro t ht
      exact hs t ht.1
  have heval : (∫ t in (0 : ℝ)..Real.exp y, 6 * Real.pi * t) =
      3 * Real.pi * (Real.exp y) ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [heval] at hint
  unfold physicalHead
  rw [Geometry.Nindex_eq]
  simp only [Geometry.kClimb, div_one, Geometry.arclength]
  have hpi := Real.pi_pos
  calc
    9 * Real.exp y ^ 2 = (3 / Real.pi) * (3 * Real.pi * Real.exp y ^ 2) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (by positivity)

theorem physicalHead_gt_height {y : ℝ} (hy : 0 ≤ y) : y < physicalHead y := by
  have hexp := Real.add_one_le_exp y
  have hlo := physicalHead_lower y
  nlinarith [Real.exp_pos y, sq_nonneg (Real.exp y - 1)]

theorem physicalHead_tendsto : Tendsto physicalHead atTop atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  filter_upwards [Filter.eventually_ge_atTop (max b 0)] with y hy
  exact ((le_max_left b 0).trans hy).trans
    (physicalHead_gt_height ((le_max_right b 0).trans hy)).le

/-- The smooth entry profile from the finite-bank experiment, extended by zero at the cutoff. -/
noncomputable def smoothEntry (u : ℝ) : ℝ :=
  if u < 1 then Real.exp (1 - 1 / (1 - u ^ 2)) else 0

theorem smoothEntry_nonneg (u : ℝ) : 0 ≤ smoothEntry u := by
  unfold smoothEntry
  split_ifs <;> positivity

/-- The head is fixed throughout each complex evaluation of this finite bank. -/
noncomputable def finiteFiber (Z : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range ⌈Z⌉₊,
    ((-1 : ℂ) ^ k * (smoothEntry (((k + 1 : ℕ) : ℝ) / Z) : ℂ)) *
      Complex.exp (-s * (Real.log ((k + 1 : ℕ) : ℝ) : ℂ))

/-- Freeze the carrier's actual head at ordinate `y`; `s` remains the readout variable. -/
noncomputable def carrierHeadFiber (y : ℝ) (s : ℂ) : ℂ :=
  finiteFiber (physicalHead y) s

theorem finiteFiber_entire (Z : ℝ) : Differentiable ℂ (finiteFiber Z) := by
  unfold finiteFiber
  fun_prop

theorem carrierHeadFiber_entire (y : ℝ) : Differentiable ℂ (carrierHeadFiber y) :=
  finiteFiber_entire (physicalHead y)

theorem finiteFiber_conj (Z : ℝ) (s : ℂ) :
    finiteFiber Z ((starRingEnd ℂ) s) = (starRingEnd ℂ) (finiteFiber Z s) := by
  unfold finiteFiber
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, Complex.conj_ofReal,
    ← Complex.exp_conj]

end CriticalLinePhasor.CarrierHeadFiniteFiber

#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.physicalHead_lower
#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.physicalHead_gt_height
#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.physicalHead_tendsto
#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.carrierHeadFiber_entire
#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.finiteFiber_conj
