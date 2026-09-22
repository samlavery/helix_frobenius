import RequestProject.HelixPolarization
import RequestProject.SelfAdjointGeneratorReadout

/-!
# The detected helix class in the positive fiber

At a zero, the quotient in `theoremD` identifies with C. The explicit embedding below
sends its distinguished class to `single 0 1` and proves positive cup energy.
This embedding does not assert any intertwining with an analytic spectral operator.
The zero-detecting coboundary has eigenvalue zero. The polarization has eigenvalue i.
`detectedSpectralOperator` is an explicitly introduced scalar candidate retaining the
full spectral parameter; its eigenvector equation and its symmetry defect are computed below.
-/

noncomputable section
open Complex
namespace CriticalLinePhasor.HelixPolarization
open CupIdentity ChiralCup SelfAdjointGenerator UnconditionalFrobenius
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

-- Unfolded target: for 0 < Re ρ < 1 and Lχ(ρ)=0, prove
-- Im(-i*(ρ-1/2))=0. Theorem D supplies [1] ≠ 0 in C/span{Lχ(ρ)}.
-- A supplies positivity on finite-support vectors, not an action on that quotient.
-- Expectation-free next step: construct the actual quotient-to-fiber map, then
-- compute which scalar the available operators apply to its distinguished class.
-- Strategy A starts: rw [coboundaryD, hL, zero_smul].
-- Strategy B starts: rw [vonNeumannOp_apply].

theorem span_LFunction_eq_bot_of_zero (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) :
    Submodule.span ℂ {DirichletCharacter.LFunction χ ρ} = ⊥ := by
  rw [hL, Submodule.span_singleton_eq_bot.mpr rfl]

/-- The detected quotient is canonically a copy of C when the carrier vanishes. -/
def cohomologyEquivAtZero (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) :
    HelixCohomology χ ρ ≃ₗ[ℂ] ℂ :=
  Submodule.quotEquivOfEqBot _ (span_LFunction_eq_bot_of_zero χ ρ hL)

@[simp] theorem cohomologyEquivAtZero_eigenclass (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    cohomologyEquivAtZero χ ρ hL (eigenclass χ ρ) = 1 := by
  rfl

/-- A concrete linear embedding of the detected class into the polarized fiber. -/
def cohomologyToFiber (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) :
    HelixCohomology χ ρ →ₗ[ℂ] Hfib :=
  (Finsupp.lsingle 0).comp (cohomologyEquivAtZero χ ρ hL).toLinearMap

@[simp] theorem cohomologyToFiber_eigenclass (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    cohomologyToFiber χ ρ hL (eigenclass χ ρ) = Finsupp.single 0 1 := by
  rfl

theorem detected_class_polarization_pos (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    0 < OmegaH (Dop (cohomologyToFiber χ ρ hL (eigenclass χ ρ)))
      (JH (Dop (cohomologyToFiber χ ρ hL (eigenclass χ ρ)))) := by
  apply theoremA
  simp

theorem cohomologyToFiber_injective (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    Function.Injective (cohomologyToFiber χ ρ hL) :=
  (Finsupp.single_injective 0).comp (cohomologyEquivAtZero χ ρ hL).injective

theorem coboundaryD_eq_zero_at_zero (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) : coboundaryD χ ρ = 0 := by
  rw [coboundaryD, hL, zero_smul]

theorem coboundaryD_symmetric_at_zero (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) : (coboundaryD χ ρ).IsSymmetric := by
  rw [coboundaryD_eq_zero_at_zero χ ρ hL]
  intro x y
  simp

theorem coboundaryD_hasEigenvalue_zero (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    Module.End.HasEigenvalue (coboundaryD χ ρ) 0 := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : ℂ))
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, one_ne_zero⟩
  simp [coboundaryD_eq_zero_at_zero χ ρ hL]

-- Compute the candidate operator retaining the full analytic spectral height.
def detectedSpectralOperator (ρ : ℂ) : Hfib →ₗ[ℂ] Hfib :=
  specHeight ρ • LinearMap.id

theorem detectedSpectralOperator_eigenclass (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    detectedSpectralOperator ρ (cohomologyToFiber χ ρ hL (eigenclass χ ρ)) =
      specHeight ρ • cohomologyToFiber χ ρ hL (eigenclass χ ρ) := rfl

theorem detectedSpectralOperator_hasEigenvalue (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    Module.End.HasEigenvalue (detectedSpectralOperator ρ) (specHeight ρ) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := cohomologyToFiber χ ρ hL (eigenclass χ ρ))
  exact ⟨Module.End.mem_eigenspace_iff.mpr
    (detectedSpectralOperator_eigenclass χ ρ hL), by simp⟩

theorem detectedSpectralOperator_symmetry_defect (ρ : ℂ) (x y : Hfib) :
    inner ℂ (detectedSpectralOperator ρ x) y -
        inner ℂ x (detectedSpectralOperator ρ y) =
      (2 * Complex.I * ((ρ.re : ℂ) - 1 / 2)) * inner ℂ x y := by
  simp only [detectedSpectralOperator, LinearMap.smul_apply, LinearMap.id_apply,
    inner_smul_left, inner_smul_right]
  rw [← sub_mul]
  congr 1
  apply Complex.ext
  · simp [specHeight, Complex.mul_re, Complex.mul_im]
  · simp [specHeight, Complex.mul_re, Complex.mul_im]
    ring

theorem detected_class_JH_eigenvector (ρ : ℂ)
    (hL : DirichletCharacter.LFunction χ ρ = 0) :
    JH (Dop (cohomologyToFiber χ ρ hL (eigenclass χ ρ))) =
      Complex.I • Dop (cohomologyToFiber χ ρ hL (eigenclass χ ρ)) := rfl

-- Positive polarization alone does not make the polarization operator symmetric.
theorem JH_hasEigenvalue_I : Module.End.HasEigenvalue JH Complex.I := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := Finsupp.single 0 1)
  exact ⟨Module.End.mem_eigenspace_iff.mpr rfl, by simp⟩

theorem JH_not_symmetric : ¬ JH.IsSymmetric := by
  intro h
  have hi := von_neumann_reality h JH_hasEigenvalue_I
  norm_num at hi

-- D applies to trivial zeros as well; the strip restriction must be retained.
theorem theoremD_neg_two_nonnull : eigenclass (1 : DirichletCharacter ℂ 1) (-2) ≠ 0 := by
  apply (theoremD _ _).mp
  rw [DirichletCharacter.LFunction_modOne_eq]
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

theorem theoremD_neg_two_spectralHeight : (specHeight (-2)).im = 5 / 2 := by
  norm_num [specHeight, Complex.mul_im]

end CriticalLinePhasor.HelixPolarization

#print axioms CriticalLinePhasor.HelixPolarization.cohomologyToFiber_injective
#print axioms CriticalLinePhasor.HelixPolarization.detected_class_polarization_pos
#print axioms CriticalLinePhasor.HelixPolarization.coboundaryD_symmetric_at_zero
#print axioms CriticalLinePhasor.HelixPolarization.coboundaryD_hasEigenvalue_zero
#print axioms CriticalLinePhasor.HelixPolarization.detectedSpectralOperator_hasEigenvalue
#print axioms CriticalLinePhasor.HelixPolarization.detectedSpectralOperator_symmetry_defect
#print axioms CriticalLinePhasor.HelixPolarization.JH_not_symmetric
#print axioms CriticalLinePhasor.HelixPolarization.theoremD_neg_two_nonnull
#print axioms CriticalLinePhasor.HelixPolarization.theoremD_neg_two_spectralHeight
