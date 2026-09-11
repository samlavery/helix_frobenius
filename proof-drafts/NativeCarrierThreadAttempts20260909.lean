import RequestProject.ZetaZeroNative3DSourceTransfer
import RequestProject.HelixHeightDischarge
import RequestProject.HPCorrespondenceDoor

/-
Fixed target: RiemannHypothesis, with no additional arguments.
Unfolded: every zero of riemannZeta other than the excluded trivial zeros
and pole has real coordinate 1/2. The bridge reduces this to zeros in
0 < Re rho < 1.

Without a prior expectation, test the existing constructors at the exact
inputs of the three doors. These are deliberately retained compiler tests,
not declarations offered as proved results.

A starts with `apply riemannHypothesis_of_log_correspondence` and uses the
native event's positive physical height.
B starts with `apply riemannHypothesis_of_eigenvalue_correspondence` and
uses the symmetric ambient operator and native event eigenvector.
C uses the analytic zero-ledger eigenvalue and tests whether the symmetry
of the constructed Hermitian projection supplies symmetry of that operator.
-/

open CriticalLinePhasor CriticalLinePhasor.ContourArgument
open CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.XiChannel
open CriticalLinePhasor.HPCorrespondence

-- A: actual native height into the logarithmic correspondence.
example : RiemannHypothesis := by
  apply riemannHypothesis_of_log_correspondence
  intro rho hrho
  let fiber := principalZeroAnalyticFiber3D hrho
  refine ⟨fiber.sourceHeight, fiber.sourceHeight_pos, ?_⟩
  exact congrArg (fun x : ℝ => (x : ℂ)) fiber.log_sourceHeight_eq_im.symm

-- B: actual native eigenvector into the symmetric operator door.
example : RiemannHypothesis := by
  apply riemannHypothesis_of_eigenvalue_correspondence
    (carrierThreeDOperator_isSymmetric 1 1)
  intro rho hrho
  let event := principalZero_focalCancellation_on_carrier hrho
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := Finsupp.single event.carrierState (1 : ℂ))
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact event.ambient_eigenvector
  · rw [event.carrierState_eq]
    exact event.analyticFiber.ambient_nonzero

-- C: exact analytic eigenvalue, symmetry from the constructed projection.
example : RiemannHypothesis := by
  apply riemannHypothesis_of_eigenvalue_correspondence
    (T := xiZeroLedgerOperator)
  · exact xiZeroLedgerNoDriftProjection_isSymmetric
  · intro rho hrho
    have hp : HelixLimit.poleParam rho = -Complex.I * (rho - 1 / 2) := by
      apply Complex.ext <;> simp [HelixLimit.poleParam, Complex.mul_re, Complex.mul_im]
    rw [← hp]
    exact xiZeroLedgerOperator_hasEigenvalue ⟨rho, hrho⟩
