import RequestProject.CPSConverseTheorem3D
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Audit of the abstract CPS hypotheses

The abstract action and unipotent-channel interfaces range over arbitrary data.  These concrete
examples certify that invariance and cuspidality cannot be conclusions of those generic signatures
without specializing the action and channels.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- A scalar readout distinguishing the two points of `Bool`. -/
def boolReadout (x : Bool) : ℂ := if x then 1 else 0

/-- Arbitrary group actions do not make arbitrary readouts invariant. -/
theorem not_all_readouts_invariant_under_all_group_moves :
    ¬(∀ (readout : Bool → ℂ) (g : Equiv.Perm Bool) (x : Bool),
      readout (g • x) = readout x) := by
  intro h
  have hswap := h boolReadout (Equiv.swap false true) false
  norm_num [boolReadout] at hswap

/-- The constant-one kernel on the one-point channel. -/
def unitConstantKernel : Unit → Unit → Unit → ℂ := fun _ _ _ => 1

/-- An integrable channel need not have vanishing constant term without a nontrivial eigenmove. -/
theorem unitConstantKernel_not_cuspidal :
    ¬CuspidalAlong3D (fun _ : Unit => MeasureTheory.Measure.dirac ()) unitConstantKernel := by
  intro h
  have hterm := h () ()
  simp [unipotentConstantTerm, unitConstantKernel] at hterm

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.not_all_readouts_invariant_under_all_group_moves
#print axioms CriticalLinePhasor.ThreeDConverse.unitConstantKernel_not_cuspidal
