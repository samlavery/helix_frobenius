import RequestProject.RoundTrip
import RequestProject.RiemannHypothesisBridge

/-!
# The minimal Hilbert–Pólya door: correspondence, not matching

Sam's correction (2026-08-30): HP does not require exact analytic matching
— no trace identities, no exhaustion, no multiplicity bookkeeping.  It
requires CORRESPONDENCE, and the correct and sufficient definition is the
chart law itself: **the 3D zero location is a height `z > 0`, and in the
chart it becomes `iy = log z`.**  Logs of positive heights are real, so
any zero in the image of the correspondence is on the line — reality is
carried by the definition, before any operator is mentioned.

Two compiled doors to the exact Mathlib target:
* `riemannHypothesis_of_log_correspondence` — Sam's form: every chart zero
  arises from a height through the log chart.
* `riemannHypothesis_of_eigenvalue_correspondence` — the operator form:
  one fixed symmetric operator, eigenvalue membership per zero.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CriticalLinePhasor.HPCorrespondence

open ConeProjection

/-- **RH from the log correspondence** (Sam's definition): every nontrivial
zero's spectral parameter is the logarithm of a positive 3D height.  Logs
of heights are real; the conclusion is the exact Mathlib proposition. -/
theorem riemannHypothesis_of_log_correspondence
    (hcorr : ∀ ρ ∈ ZD.NontrivialZeros, ∃ Z : ℝ, 0 < Z ∧
      -Complex.I * (ρ - 1/2) = (Real.log Z : ℂ)) :
    RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  obtain ⟨Z, hZ, hlog⟩ := hcorr ρ hρ
  have him : (-Complex.I * (ρ - 1/2)).im = 0 := by
    rw [hlog]
    exact Complex.ofReal_im _
  have hcalc : (-Complex.I * (ρ - 1/2)).im = 1/2 - ρ.re := by
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
  rw [hcalc] at him
  linarith

/-- **RH from eigenvalue correspondence**: one fixed symmetric operator,
and for each nontrivial zero the mere membership of its spectral parameter
in the point spectrum. -/
theorem riemannHypothesis_of_eigenvalue_correspondence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hcorr : ∀ ρ ∈ ZD.NontrivialZeros,
      Module.End.HasEigenvalue T (-Complex.I * (ρ - 1/2))) :
    RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  have h := hilbert_polya_on_critical_line hT (hcorr ρ hρ)
  have hinv : spectralZero (-Complex.I * (ρ - 1/2)) = ρ := by
    unfold spectralZero
    linear_combination -(ρ - 1/2) * Complex.I_mul_I
  rw [hinv] at h
  exact h

end CriticalLinePhasor.HPCorrespondence

#print axioms CriticalLinePhasor.HPCorrespondence.riemannHypothesis_of_log_correspondence
#print axioms CriticalLinePhasor.HPCorrespondence.riemannHypothesis_of_eigenvalue_correspondence
