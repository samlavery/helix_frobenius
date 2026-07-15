import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Registration gaps: the deterministic component of the unit-chart defect ledger

`CarrierScaleCompensation.lean` proves that `S` is the compensation term produced by reading the
`π/3` carrier lattice through the unit-1 chart (`carrier_scale_compensation_S`), that `S` has no
native carrier home (`S_has_no_native_carrier`), and that the two lattices never re-register
(`lattice_gap_fundamental`, `unit_never_closes`).  This file proves the *dynamics* of that
registration: the deterministic component of the defect ledger — the sequence of carrier ticks
read in the unit chart — is an irrational rotation of the unit ledger, hence

* it never re-aligns (`carrierTick_nsmul_ne_zero`),
* its marks are dense (`denseRange_carrierTicks`),
* the rotation is ergodic (`ergodic_carrierTick_rotation`), so by Birkhoff the registration
  defect equidistributes over the unit cell: the deterministic part of the defect ledger visits
  every defect window with asymptotic frequency equal to its measure.

These are unconditional facts about the chart-artifact component of the `S` ledger, proven from
carrier geometry (the irrationality of the scale ratio) with no zeta input at all.  The
*arithmetic* component — where the actual crossing events sit against this deterministic
grid — is the object of the event-gap program (carrier Jensen: events per height window bounded
by envelope growth).

Named brick, not yet formalized: the Steinhaus three-distance theorem (the finite mark sets
partition the unit cell into gaps of at most three distinct lengths) is not in Mathlib; it is
classical, provable, and queued — the gap trichotomy of the registration marks is stated here
only in the docstring register.

This file does not assume or prove RH/GRH; it concerns the deterministic lattice layer only.
-/

open Real

namespace CriticalLinePhasor.RegistrationGaps

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The carrier tick, read in the unit chart: `π/3` as a point of the unit ledger. -/
noncomputable def carrierTick : AddCircle (1 : ℝ) := ((Real.pi / 3 : ℝ) : AddCircle (1 : ℝ))

/-- The scale ratio of the two lattices is irrational. -/
theorem irrational_pi_div_three : Irrational (Real.pi / 3) := by
  have h := irrational_pi.div_natCast (m := 3) (by norm_num)
  simpa using h

/-- The carrier tick is of infinite order in the unit ledger: the two scales never
re-register. -/
theorem carrierTick_not_isOfFinAddOrder : ¬ IsOfFinAddOrder carrierTick := by
  rw [carrierTick, AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div]
  intro q hq
  rw [div_one] at hq
  exact irrational_pi_div_three.ne_rat q hq.symm

/-- The same fact in the order ledger: the carrier tick has additive order zero. -/
theorem carrierTick_addOrderOf_eq_zero : addOrderOf carrierTick = 0 :=
  addOrderOf_eq_zero_iff.mpr carrierTick_not_isOfFinAddOrder

/-- No positive number of carrier ticks lands on a unit-chart mark. -/
theorem carrierTick_nsmul_ne_zero {k : ℕ} (hk : 0 < k) : k • carrierTick ≠ 0 :=
  (addOrderOf_eq_zero_iff'.mp carrierTick_addOrderOf_eq_zero) k hk

/-- The registration defect after `n` carrier ticks, read in the unit chart. -/
noncomputable def registrationDefect (n : ℤ) : AddCircle (1 : ℝ) := n • carrierTick

/-- **Density.** The registration marks are dense in the unit ledger: the deterministic defect
comes arbitrarily close to every unit-chart position. -/
theorem denseRange_carrierTicks : DenseRange registrationDefect := by
  unfold registrationDefect carrierTick
  exact (AddCircle.denseRange_zsmul_coe_iff).mpr (by simpa using irrational_pi_div_three)

/-- **Ergodicity.** Rotation of the unit ledger by the carrier tick is ergodic; by Birkhoff the
registration defect sequence equidistributes over the unit cell. -/
theorem ergodic_carrierTick_rotation :
    Ergodic (fun x => carrierTick + x) MeasureTheory.volume := by
  rw [AddCircle.ergodic_add_left]
  exact carrierTick_addOrderOf_eq_zero

/-- The defect sequence is injective: no two tick counts produce the same unit-chart defect. -/
theorem registrationDefect_injective : Function.Injective registrationDefect := by
  intro m n hmn
  by_contra hne
  apply carrierTick_not_isOfFinAddOrder
  rw [isOfFinAddOrder_iff_zsmul_eq_zero]
  refine ⟨m - n, sub_ne_zero.mpr hne, ?_⟩
  have hmn' : m • carrierTick = n • carrierTick := hmn
  rw [sub_smul, hmn', sub_self]

end CriticalLinePhasor.RegistrationGaps

#print axioms CriticalLinePhasor.RegistrationGaps.irrational_pi_div_three
#print axioms CriticalLinePhasor.RegistrationGaps.carrierTick_addOrderOf_eq_zero
#print axioms CriticalLinePhasor.RegistrationGaps.carrierTick_nsmul_ne_zero
#print axioms CriticalLinePhasor.RegistrationGaps.denseRange_carrierTicks
#print axioms CriticalLinePhasor.RegistrationGaps.ergodic_carrierTick_rotation
#print axioms CriticalLinePhasor.RegistrationGaps.registrationDefect_injective
