import RequestProject.CPSAdelicAssembly3D
import Mathlib.MeasureTheory.Group.Integral

/-!
# Unipotent constant-term cancellation

A nontrivial eigencharacter for a measure-preserving unipotent translation forces the corresponding
constant term to vanish.  This is the Haar/Fourier cancellation used in the cuspidality step of the
3D converse.
-/

namespace CriticalLinePhasor.ThreeDConverse

open MeasureTheory

/-- A nontrivial scalar eigenmove of a measure-preserving measurable equivalence has zero integral. -/
theorem integral_eq_zero_of_nontrivial_eigenEquiv
    {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (T : U ≃ᵐ U) (hT : MeasurePreserving T μ μ)
    (f : U → ℂ) (_hf : Integrable f μ) (c : ℂ)
    (heigen : ∀ x, f (T x) = c * f x) (hc : c ≠ 1) :
    ∫ x, f x ∂μ = 0 := by
  let I : ℂ := ∫ x, f x ∂μ
  have hpreserved : (∫ x, f (T x) ∂μ) = I := by
    exact hT.integral_comp' f
  have heigenIntegral : (∫ x, f (T x) ∂μ) = c * I := by
    rw [integral_congr_ae (Filter.Eventually.of_forall heigen), integral_const_mul]
  have hcI : c * I = I := heigenIntegral.symm.trans hpreserved
  have hmul : (c - 1) * I = 0 := by
    calc
      (c - 1) * I = c * I - I := by ring
      _ = 0 := sub_eq_zero.mpr hcI
  have hI : I = 0 := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hc)
  exact hI

/-- A nontrivial left-translation eigencharacter has vanishing Haar constant term. -/
theorem unipotentConstantTerm_eq_zero
    {U : Type*} [MeasurableSpace U] [Group U]
    [MeasurableMul U] [MeasurableInv U]
    (μ : Measure U) [Measure.IsMulLeftInvariant μ]
    (f : U → ℂ) (hf : Integrable f μ) (a : U) (c : ℂ)
    (heigen : ∀ x, f (a * x) = c * f x) (hc : c ≠ 1) :
    ∫ x, f x ∂μ = 0 := by
  exact integral_eq_zero_of_nontrivial_eigenEquiv μ (MeasurableEquiv.mulLeft a)
    (measurePreserving_mul_left μ a) f hf c heigen hc

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.integral_eq_zero_of_nontrivial_eigenEquiv
#print axioms CriticalLinePhasor.ThreeDConverse.unipotentConstantTerm_eq_zero
