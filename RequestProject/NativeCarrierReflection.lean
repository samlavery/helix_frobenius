import RequestProject.NativeCarrierTransport
import RequestProject.HelixHeightDescent

noncomputable section

namespace CriticalLinePhasor.NativeCarrierTransport

open ThreeDFocal XiChannel

/-- Reflection cancels transported radial drift on the averaged input. -/
theorem transportedDrift_even_eq_zero :
    (zeroHeightCorrespondence.comp xiRadialDriftOperator).comp
      xiReflectionEvenProjection = 0 := by
  apply Finsupp.lhom_ext
  intro rho c
  simp only [LinearMap.comp_apply, xiReflectionEvenProjection,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add, xiZeroReflectionOperator_single, xiRadialDriftOperator,
    UnconditionalFrobenius.diagOp_single, zeroHeightCorrespondence_single,
    carrierState3D_reflected_height, ← Finsupp.single_add,
    Finsupp.smul_single, smul_eq_mul, LinearMap.zero_apply]
  apply Finsupp.single_eq_zero.mpr
  simp only [xiZeroReflection, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- The analytic radial operator on one native basis mode has a single recorded coefficient. -/
theorem transportedDrift_single (rho : XiZeroIndex) (c : ℂ) :
    zeroHeightCorrespondence (xiRadialDriftOperator (Finsupp.single rho c)) =
      Finsupp.single (carrierState3D 1 1 rho.val.im)
        (((rho.val.re : ℂ) - 1 / 2) * c) := by
  rw [xiRadialDriftOperator, UnconditionalFrobenius.diagOp_single,
    zeroHeightCorrespondence_single]
  push_cast
  rfl

/-- The same radial operator applied to a reflected difference retains both contributions. -/
theorem transportedDrift_difference (rho : XiZeroIndex) :
    zeroHeightCorrespondence (xiRadialDriftOperator (reflectedDifferenceMode rho)) =
      Finsupp.single (carrierState3D 1 1 rho.val.im)
        (2 * ((rho.val.re : ℂ) - 1 / 2)) := by
  rw [reflectedDifferenceMode, map_sub, map_sub, transportedDrift_single,
    transportedDrift_single, carrierState3D_reflected_height, ← Finsupp.single_sub]
  congr 1
  simp [xiZeroReflection]
  ring

end CriticalLinePhasor.NativeCarrierTransport

#print axioms CriticalLinePhasor.NativeCarrierTransport.transportedDrift_even_eq_zero
#print axioms CriticalLinePhasor.NativeCarrierTransport.transportedDrift_single
#print axioms CriticalLinePhasor.NativeCarrierTransport.transportedDrift_difference
