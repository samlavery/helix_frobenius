import RequestProject.ZetaZeroNative3DSourceTransfer
import RequestProject.HelixHeightCorrespondence

noncomputable section

namespace CriticalLinePhasor.NativeCarrierTransport

open ThreeDFocal ContourArgument XiChannel

/-- The actual native carrier event supplied by an analytic zero. -/
def nativeMode (rho : XiZeroIndex) : CarrierThreeDMode 1 1 :=
  Finsupp.single (principalZero_focalCancellation_on_carrier rho.property).carrierState 1

/-- The native event constructor agrees with the existing linear height correspondence. -/
theorem nativeMode_eq_heightCorrespondence (rho : XiZeroIndex) :
    nativeMode rho = zeroHeightCorrespondence (Finsupp.single rho 1) := by
  rw [zeroHeightCorrespondence_single]
  rfl

theorem nativeMode_ne_zero (rho : XiZeroIndex) : nativeMode rho ≠ 0 := by
  rw [nativeMode_eq_heightCorrespondence]
  exact zeroHeightCorrespondence_basis_ne_zero rho

/-- The eigenvector equation comes directly from the native focal event. -/
theorem nativeMode_height_eigenvector (rho : XiZeroIndex) :
    carrierThreeDOperator 1 1 (nativeMode rho) =
      (rho.val.im : ℂ) • nativeMode rho :=
  (principalZero_focalCancellation_on_carrier rho.property).ambient_eigenvector

/-- The two expressions for the analytic spectral parameter agree without a location premise. -/
theorem analytic_parameter_eq (rho : ℂ) :
    HelixLimit.poleParam rho = -Complex.I * (rho - 1 / 2) := by
  apply Complex.ext <;> simp [HelixLimit.poleParam, Complex.mul_re, Complex.mul_im]

/-- Transport of the analytic eigenmode retains its full eigenparameter. -/
theorem nativeMode_analytic_transport (rho : XiZeroIndex) :
    zeroHeightCorrespondence (xiZeroLedgerOperator (Finsupp.single rho 1)) =
      (-Complex.I * (rho.val - 1 / 2)) • nativeMode rho := by
  rw [xiZeroLedgerOperator_single', mul_one, zeroHeightCorrespondence_single,
    nativeMode_eq_heightCorrespondence, zeroHeightCorrespondence_single,
    Finsupp.smul_single, smul_eq_mul, mul_one, analytic_parameter_eq]

/-- Exact difference between applying the carrier operator and transporting the analytic
operator, on the same nonzero native mode. -/
theorem nativeMode_transport_residual (rho : XiZeroIndex) :
    carrierThreeDOperator 1 1 (nativeMode rho) -
        zeroHeightCorrespondence (xiZeroLedgerOperator (Finsupp.single rho 1)) =
      (Complex.I * ((rho.val.re : ℂ) - 1 / 2)) • nativeMode rho := by
  rw [nativeMode_height_eigenvector, nativeMode_analytic_transport, ← sub_smul]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Evaluation at the native carrier state records the entire transport residual. -/
theorem nativeMode_transport_residual_at_event (rho : XiZeroIndex) :
    (carrierThreeDOperator 1 1 (nativeMode rho) -
        zeroHeightCorrespondence (xiZeroLedgerOperator (Finsupp.single rho 1)))
      (principalZero_focalCancellation_on_carrier rho.property).carrierState =
        Complex.I * ((rho.val.re : ℂ) - 1 / 2) := by
  rw [nativeMode_transport_residual]
  simp [nativeMode]

/-- The transport equation on the entire finite-support state space, retaining the radial
operator from the analytic spectral parameter. -/
theorem full_operator_transport :
    zeroHeightCorrespondence.comp xiZeroLedgerOperator =
      (carrierThreeDOperator 1 1).comp zeroHeightCorrespondence -
        Complex.I • (zeroHeightCorrespondence.comp xiRadialDriftOperator) := by
  rw [xiZeroLedgerOperator_eq_height_sub_I_smul_radialDrift,
    LinearMap.comp_sub, LinearMap.comp_smul,
    zeroHeightCorrespondence_height_intertwining]

end CriticalLinePhasor.NativeCarrierTransport

#print axioms CriticalLinePhasor.NativeCarrierTransport.nativeMode_eq_heightCorrespondence
#print axioms CriticalLinePhasor.NativeCarrierTransport.nativeMode_ne_zero
#print axioms CriticalLinePhasor.NativeCarrierTransport.nativeMode_height_eigenvector
#print axioms CriticalLinePhasor.NativeCarrierTransport.nativeMode_analytic_transport
#print axioms CriticalLinePhasor.NativeCarrierTransport.nativeMode_transport_residual
#print axioms CriticalLinePhasor.NativeCarrierTransport.nativeMode_transport_residual_at_event
#print axioms CriticalLinePhasor.NativeCarrierTransport.full_operator_transport
