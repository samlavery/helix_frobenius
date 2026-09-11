import RequestProject.NativeCarrierTransport
import RequestProject.HelixHeightDescent

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.XiChannel

/- Fixed target: K.comp D = 0, with no additional assumptions.
Unfolded on a basis vector: the carrier mode at Im rho has coefficient
(Re rho - 1/2) * c, and this coefficient must vanish for every rho and c.

Without a prior expectation: first test the native carrier's geometric
scale law; independently test reflection averaging, retaining composition order.
A begins `apply Finsupp.lhom_ext`.
B begins `have h := zeroHeightCorrespondence_averaged_intertwining`.
-/

-- A: evaluate the operator and consume the actual native carrier scale law.
example : zeroHeightCorrespondence.comp xiRadialDriftOperator = 0 := by
  apply Finsupp.lhom_ext
  intro rho c
  have hgeometry :=
    (principalZero_focalCancellation_on_carrier rho.property).carrierReadout_scaleBalanced
  change zeroHeightCorrespondence (xiRadialDriftOperator (Finsupp.single rho c)) = 0
  rw [xiRadialDriftOperator, UnconditionalFrobenius.diagOp_single,
    zeroHeightCorrespondence_single]
  rw [Finsupp.single_eq_zero]
  simp_all [carrierScaleBalanced_iff, carrierPointAtHeight_re, carrierAbscissa_eq_half, mul_eq_zero]

-- B: try extending the averaged intertwining to the entire input space.
example : Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator
    (carrierThreeDOperator 1 1) := by
  have h := zeroHeightCorrespondence_averaged_intertwining
  intro f
  have hf := LinearMap.congr_fun h f
  simpa only [LinearMap.comp_apply] using hf
