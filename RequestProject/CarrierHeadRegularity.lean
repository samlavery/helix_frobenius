import RequestProject.CarrierHeadFiniteFiber
import RequestProject.AreaLaw

open Filter Topology

namespace CriticalLinePhasor.CarrierHeadFiniteFiber

theorem physicalHead_eq_arclength (y : ℝ) :
    physicalHead y = (3 / Real.pi) * Geometry.arclength 1 3 (Real.exp y) := by
  simp [physicalHead, Geometry.Nindex_eq, Geometry.kClimb]

theorem physicalHead_hasDerivAt (y : ℝ) :
    HasDerivAt physicalHead
      ((3 / Real.pi) * (Geometry.speed 1 3 (Real.exp y) * Real.exp y)) y := by
  have heq : physicalHead = fun t => (3 / Real.pi) * Geometry.arclength 1 3 (Real.exp t) :=
    funext physicalHead_eq_arclength
  rw [heq]
  exact ((Geometry.arclength_hasDerivAt 1 3 (Real.exp y)).comp y
    (Real.hasDerivAt_exp y)).const_mul (3 / Real.pi)

theorem physicalHead_continuous : Continuous physicalHead :=
  (show Differentiable ℝ physicalHead from fun y => (physicalHead_hasDerivAt y).differentiableAt).continuous

theorem physicalHead_strictMono : StrictMono physicalHead := by
  intro a b hab
  rw [physicalHead_eq_arclength, physicalHead_eq_arclength]
  exact mul_lt_mul_of_pos_left
    (Geometry.arclength_strictMono 1 3 (by norm_num) (Real.exp_lt_exp.mpr hab)) (by positivity)

theorem physicalHead_pos (y : ℝ) : 0 < physicalHead y :=
  lt_of_lt_of_le (by positivity) (physicalHead_lower y)

theorem log_physicalHead_hasDerivAt (y : ℝ) :
    HasDerivAt (fun t => Real.log (physicalHead t))
      (((3 / Real.pi) * (Geometry.speed 1 3 (Real.exp y) * Real.exp y)) / physicalHead y) y :=
  (physicalHead_hasDerivAt y).log (physicalHead_pos y).ne'

theorem log_physicalHead_strictMono : StrictMono (fun t => Real.log (physicalHead t)) := by
  intro a b hab
  exact Real.log_lt_log (physicalHead_pos a) (physicalHead_strictMono hab)

end CriticalLinePhasor.CarrierHeadFiniteFiber

#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.physicalHead_hasDerivAt
#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.physicalHead_strictMono
#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.log_physicalHead_hasDerivAt
#print axioms CriticalLinePhasor.CarrierHeadFiniteFiber.log_physicalHead_strictMono
