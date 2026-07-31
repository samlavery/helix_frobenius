import RequestProject.RSAveragedThetaProfile3D
import RequestProject.GeneralEpsteinZeta

/-!
# Continuity of the averaged theta profile in the carrier height

The Petersson-averaged lattice bank `θ̄_f(t) = ∫_𝒟 P_f(z) · Θ_z(t)` is continuous on the
positive carrier axis.  Dominated convergence under the fundamental-domain integral: near a
height `t₀ > 0` every integrand at height `t > t₀/2` is dominated by `P_f(z) · Θ_z(t₀/2)` —
the bank is antitone in the height (`latticeTheta_anti`) — and the dominant is integrable on
the fundamental domain (`integrableOn_P_mul_theta`); per-`z` continuity in the height is
`continuousOn_latticeTheta`, and per-height measurability comes from `P_continuous` and
`measurable_latticeTheta`.

This is the profile-side `ContinuousAt` input that pointwise Mellin-uniqueness closures
consume; the bank side's counterpart is compiled in `CPSMellinFEDischarge.lean`.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Set
open scoped Real MatrixGroups Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound CriticalLinePhasor.EpsteinTheta

variable {k : ℤ}

/-- **Continuity of the averaged profile at each positive carrier height** — dominated
convergence under the fundamental-domain integral.  On the neighborhood `Ioi (x/2)` of the
height `x` every integrand is dominated by `P_f(z) · Θ_z(x/2)` (the bank is antitone in the
height), which is integrable on the fundamental domain; per-`z` the bank is continuous in the
height. -/
theorem averagedTheta_continuousAt (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {x : ℝ}
    (hx : 0 < x) : ContinuousAt (averagedTheta k f) x := by
  have hhalf : (0 : ℝ) < x / 2 := half_pos hx
  unfold averagedTheta
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun z : ℍ => P k f z * latticeTheta z (x / 2)) ?_ ?_ ?_ ?_
  · -- per-height measurability of the integrand
    refine Eventually.of_forall fun t => ?_
    have hm : Measurable fun z : ℍ => P k f z * latticeTheta z t :=
      (P_continuous f).measurable.mul
        (measurable_latticeTheta.comp (measurable_id.prodMk measurable_const))
    exact hm.aestronglyMeasurable
  · -- the domination on the neighborhood `Ioi (x/2)`
    filter_upwards [Ioi_mem_nhds (half_lt_self hx)] with t ht
    refine ae_of_all _ fun z => ?_
    have ht0 : (0 : ℝ) < t := hhalf.trans ht
    have hnn : 0 ≤ P k f z * latticeTheta z t :=
      mul_nonneg (P_nonneg f z) (zero_le_one.trans (one_le_latticeTheta z ht0))
    rw [Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (latticeTheta_anti z hhalf ht.le) (P_nonneg f z)
  · -- the dominant is integrable on the fundamental domain
    exact integrableOn_P_mul_theta f hk hhalf
  · -- per-`z` continuity of the bank in the height
    refine ae_of_all _ fun z => ?_
    exact continuousAt_const.mul
      ((continuousOn_latticeTheta z).continuousAt (Ioi_mem_nhds hx))

/-- **The averaged theta profile is continuous on the positive carrier axis.** -/
theorem averagedTheta_continuousOn (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    ContinuousOn (averagedTheta k f) (Set.Ioi 0) :=
  fun _ ht => (averagedTheta_continuousAt f hk ht).continuousWithinAt

/-- The complex-valued averaged profile is continuous at each positive carrier height. -/
theorem averagedThetaC_continuousAt (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {x : ℝ}
    (hx : 0 < x) : ContinuousAt (averagedThetaC k f) x := by
  unfold averagedThetaC
  exact Complex.continuous_ofReal.continuousAt.comp (averagedTheta_continuousAt f hk hx)

/-- The complex-valued averaged profile is continuous on the positive carrier axis. -/
theorem averagedThetaC_continuousOn (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    ContinuousOn (averagedThetaC k f) (Set.Ioi 0) :=
  fun _ ht => (averagedThetaC_continuousAt f hk ht).continuousWithinAt

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.averagedTheta_continuousAt
#print axioms CriticalLinePhasor.Unfolding.averagedTheta_continuousOn
#print axioms CriticalLinePhasor.Unfolding.averagedThetaC_continuousAt
#print axioms CriticalLinePhasor.Unfolding.averagedThetaC_continuousOn
