import RequestProject.GlobalHelixIntertwiner
import RequestProject.LogReadoutReflection

/-!
# Centered logarithmic readout of the global 3D carrier

The carrier clock uses the centered coordinate `i log x`; the normalized analytic coordinate adds
the half-unit only afterwards.  This file identifies the repo's logarithmic theta readout with the
global 3D multiplicative-height chart exactly.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection CriticalLinePhasor.StrandExchange

/-- The centered analytic coordinate read from the 3D carrier. -/
noncomputable def centeredReadout (f : Fiber) : ℂ :=
  I * (analyticOrdinate f : ℂ)

/-- The normalized strip readout is the half-unit translated centered readout. -/
theorem stripReadout_eq_half_add_centeredReadout (f : Fiber) :
    stripReadout f = (1 / 2 : ℂ) + centeredReadout f := by
  rfl

/-- The global 3D involution becomes conjugation on the centered coordinate. -/
theorem centeredReadout_globalHelixInvolution_conj (f : Fiber) :
    centeredReadout (globalHelixInvolution f) =
      (starRingEnd ℂ) (centeredReadout f) := by
  apply Complex.ext <;>
    simp [centeredReadout, analyticOrdinate_globalHelixInvolution,
      Complex.mul_re, Complex.mul_im]

/-- The global 3D involution negates the centered coordinate. -/
theorem centeredReadout_globalHelixInvolution_neg (f : Fiber) :
    centeredReadout (globalHelixInvolution f) = -centeredReadout f := by
  rw [centeredReadout_globalHelixInvolution_conj]
  apply Complex.ext <;> simp [centeredReadout, Complex.mul_re, Complex.mul_im]

/-- The centered 3D coordinate is exactly the repo's logarithmic readout of multiplicative height. -/
theorem centeredReadout_eq_logReadout_multiplicativeHeight (f : Fiber) :
    centeredReadout f = logReadout (multiplicativeHeight f) := by
  unfold centeredReadout logReadout
  rw [analyticOrdinate_eq_height]
  unfold multiplicativeHeight heightEncode
  rw [Real.log_exp]

/-- The carrier function's logarithmic theta is exactly its centered global-helix readout. -/
theorem logTheta_multiplicativeHeight (E : ℂ → ℂ) (f : Fiber) :
    logTheta E (multiplicativeHeight f) = E (centeredReadout f) := by
  unfold logTheta
  rw [← centeredReadout_eq_logReadout_multiplicativeHeight]

/-- The completed logarithmic theta is the self-dual envelope times the centered 3D readout. -/
theorem completedLogTheta_multiplicativeHeight
    (E : ℂ → ℂ) (k : ℝ) (f : Fiber) :
    completedLogTheta E k (multiplicativeHeight f) =
      (selfDualEnvelope k (multiplicativeHeight f) : ℂ) * E (centeredReadout f) := by
  unfold completedLogTheta
  rw [logTheta_multiplicativeHeight]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.centeredReadout_globalHelixInvolution_conj
#print axioms CriticalLinePhasor.GlobalHelix.centeredReadout_eq_logReadout_multiplicativeHeight
#print axioms CriticalLinePhasor.GlobalHelix.logTheta_multiplicativeHeight
#print axioms CriticalLinePhasor.GlobalHelix.completedLogTheta_multiplicativeHeight
