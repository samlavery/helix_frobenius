import RequestProject.ZetaContourArgument
import RequestProject.TwinResolventTrace
import RequestProject.SpectralCarrierKernelCoupling3D

/-!
# The independent zeta contour wired to native 3D physical-height events

The contour census and the completed focal-event type are constructed independently.  This file
joins their proved interfaces for the principal character modulo one.  Every upper-half-plane
nontrivial zeta zero is either the completed focal cancellation at physical height
`Z = exp ρ.im`, together with every corresponding 3D harmonic-pencil rank drop, or it produces an
explicit higher good contour where the independent and native global coordinates differ.
-/

open Complex Matrix

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor CriticalLinePhasor.CarrierScale CriticalLinePhasor.ResidueJump
  CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.TwinResolventTrace
  CriticalLinePhasor.SpectralCarrierCoupling

/-- The complete native certificate selected by the contour dichotomy on the canonical ambient
carrier.  Its operator state space was defined before event certificates.  The trace uses the
actual analytic multiplicity `xiOrderNat ρ`. -/
structure PrincipalContourNative3DCertificate
    (χ₁ : DirichletCharacter ℂ 1) (ρ : ℂ) where
  event : CompletedThreeDEigenEvent χ₁
  event_height : event.1 = Real.exp ρ.im
  ambient_physicalHeight : (event.toCarrierState 1 1).physicalHeight = Real.exp ρ.im
  analyticPoint : carrierPointAtHeight event.1 = ρ
  kernelCoupling : SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ
  eigenvector_nonzero : Finsupp.single (event.toCarrierState 1 1) (1 : ℂ) ≠ 0
  ambient_eigenvector :
    carrierThreeDOperator 1 1 (Finsupp.single (event.toCarrierState 1 1) (1 : ℂ)) =
      (ρ.im : ℂ) • Finsupp.single (event.toCarrierState 1 1) (1 : ℂ)
  harmonic_rankDrop : ∀ mu lam : ℂ, lam ≠ mu →
    (completedHarmonicGram3DAtHeight χ₁ event.1 mu lam).det = 0
  trace_agreement : ∀ w : ℂ,
    completedTrace3D χ₁ {event} (fun _ => ZD.xiOrderNat ρ) (lineC w) =
      Complex.I * completedTrace1D χ₁ {event} (fun _ => ZD.xiOrderNat ρ) w

/-- A nontrivial zeta zero already placed on the native line is the completed principal-character
focal event at its positive physical helix height.  The equality of analytic and carrier points is
proved coordinatewise; the midpoint comes from `carrierPoint`, while the ordinate is unchanged. -/
theorem completedThreeDZeroAtHeight_modOne_of_nontrivialZero_on_line
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hline : ρ.re = 1 / 2) :
    CompletedThreeDZeroAtHeight χ₁ (Real.exp ρ.im) := by
  apply (completedThreeDZeroAtHeight_iff_L_zero χ₁
    (Real.exp ρ.im) (Real.exp_pos ρ.im)).2
  simp only [DirichletCharacter.LFunction_modOne_eq]
  have hpoint : carrierPointAtHeight (Real.exp ρ.im) = ρ := by
    rw [carrierPointAtHeight_exp]
    apply Complex.ext
    · simpa [carrierPoint] using hline.symm
    · simp [carrierPoint]
  rw [hpoint]
  exact hρ.2.2

/-- Pointwise constructor for the complete native certificate.  This is the reusable native
branch: an analytic zero whose real coordinate has already been obtained from geometry produces
the physical-height event, ambient eigenvector, harmonic rank drops, twin trace, multiplicity, and
full analytic-kernel coupling without any global contour hypothesis. -/
noncomputable def principalContourNative3DCertificate_of_nontrivialZero_on_line
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hline : ρ.re = 1 / 2) :
    PrincipalContourNative3DCertificate χ₁ ρ := by
  have hzero := completedThreeDZeroAtHeight_modOne_of_nontrivialZero_on_line χ₁ hρ hline
  let e : CompletedThreeDEigenEvent χ₁ := ⟨Real.exp ρ.im, hzero⟩
  have hpoint : carrierPointAtHeight e.1 = ρ := by
    dsimp [e]
    rw [carrierPointAtHeight_exp]
    apply Complex.ext
    · simpa [carrierPoint] using hline.symm
    · simp [carrierPoint]
  have heigen := carrierThreeDOperator_completedEvent_eigenvector 1 1 e
  have hcoupling : SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ := by
    rw [← hpoint]
    exact ofCompletedEvent χ₁ 1 1 e
  refine ⟨e, rfl, ?_, hpoint, hcoupling, heigen.1, ?_, ?_, ?_⟩
  · simpa [e] using e.toCarrierState_physicalHeight 1 1 one_ne_zero
  · simpa [e] using heigen.2
  · intro mu lam hlam
    exact (completedHarmonicGram3DAtHeight_rankDrop_iff χ₁ e.1 mu lam e.2.1 hlam).2 e.2
  · intro w
    exact completedTraces_agree χ₁ {e} (fun _ => ZD.xiOrderNat ρ) w

/-- Global physical-height coverage dichotomy for the principal character.  The second branch is
not an unnamed remainder: it returns a concrete good height and a proved mismatch of the two
global coordinates. -/
theorem upper_nontrivialZero_completed3D_or_globalCoordinateDefect
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hρim : 0 < ρ.im) :
    CompletedThreeDZeroAtHeight χ₁ (Real.exp ρ.im) ∨
      ∃ T : ℝ, ∃ hT : GoodHeight T,
        ρ.im < T ∧ classicalSContour hT ≠ Smult T := by
  rcases upper_nontrivialZero_line_or_globalCoordinateDefect hρ hρim with hline | hdefect
  · exact Or.inl (completedThreeDZeroAtHeight_modOne_of_nontrivialZero_on_line χ₁ hρ hline)
  · exact Or.inr hdefect

/-- The same global dichotomy with the completed spatial harmonic-pencil consequence attached.
Spatial lifting cannot manufacture the rank drop: it follows from the completed focal event via
`spatialLiftGram_rankDrop_iff`. -/
theorem upper_nontrivialZero_completed3D_rankDrop_or_globalCoordinateDefect
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hρim : 0 < ρ.im) :
    (CompletedThreeDZeroAtHeight χ₁ (Real.exp ρ.im) ∧
      ∀ mu lam : ℂ, lam ≠ mu →
        (completedHarmonicGram3DAtHeight χ₁ (Real.exp ρ.im) mu lam).det = 0) ∨
      ∃ T : ℝ, ∃ hT : GoodHeight T,
        ρ.im < T ∧ classicalSContour hT ≠ Smult T := by
  rcases upper_nontrivialZero_completed3D_or_globalCoordinateDefect χ₁ hρ hρim with
    hzero | hdefect
  · left
    refine ⟨hzero, ?_⟩
    intro mu lam hlam
    exact (completedHarmonicGram3DAtHeight_rankDrop_iff χ₁
      (Real.exp ρ.im) mu lam (Real.exp_pos ρ.im) hlam).2 hzero
  · exact Or.inr hdefect

/-- Full contour-to-ambient-operator capstone.  In the native branch this constructs the completed
event, verifies its original physical height, identifies its analytic point, supplies its nonzero
ambient eigenvector with eigenvalue `ρ.im`, proves every completed harmonic-pencil rank drop, and
attaches the exact 1D/3D resolvent-trace chart relation with analytic multiplicity. -/
theorem upper_nontrivialZero_native3DCertificate_or_globalCoordinateDefect
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hρim : 0 < ρ.im) :
    Nonempty (PrincipalContourNative3DCertificate χ₁ ρ) ∨
      ∃ T : ℝ, ∃ hT : GoodHeight T,
        ρ.im < T ∧ classicalSContour hT ≠ Smult T := by
  rcases upper_nontrivialZero_line_or_globalCoordinateDefect hρ hρim with hline | hdefect
  · left
    have hzero := completedThreeDZeroAtHeight_modOne_of_nontrivialZero_on_line χ₁ hρ hline
    let e : CompletedThreeDEigenEvent χ₁ := ⟨Real.exp ρ.im, hzero⟩
    have hpoint : carrierPointAtHeight e.1 = ρ := by
      dsimp [e]
      rw [carrierPointAtHeight_exp]
      apply Complex.ext
      · simpa [carrierPoint] using hline.symm
      · simp [carrierPoint]
    have heigen := carrierThreeDOperator_completedEvent_eigenvector 1 1 e
    have hcoupling : SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ := by
      rw [← hpoint]
      exact ofCompletedEvent χ₁ 1 1 e
    refine ⟨⟨e, rfl, ?_, hpoint, hcoupling, heigen.1, ?_, ?_, ?_⟩⟩
    · simpa [e] using e.toCarrierState_physicalHeight 1 1 one_ne_zero
    · simpa [e] using heigen.2
    · intro mu lam hlam
      exact (completedHarmonicGram3DAtHeight_rankDrop_iff χ₁ e.1 mu lam e.2.1 hlam).2 e.2
    · intro w
      exact completedTraces_agree χ₁ {e} (fun _ => ZD.xiOrderNat ρ) w
  · exact Or.inr hdefect

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.completedThreeDZeroAtHeight_modOne_of_nontrivialZero_on_line
#print axioms CriticalLinePhasor.ContourArgument.principalContourNative3DCertificate_of_nontrivialZero_on_line
#print axioms CriticalLinePhasor.ContourArgument.upper_nontrivialZero_completed3D_or_globalCoordinateDefect
#print axioms CriticalLinePhasor.ContourArgument.upper_nontrivialZero_completed3D_rankDrop_or_globalCoordinateDefect
#print axioms CriticalLinePhasor.ContourArgument.upper_nontrivialZero_native3DCertificate_or_globalCoordinateDefect
