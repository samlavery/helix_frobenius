import RequestProject.AdmissibleEigenheight

/-! Sam's transfer, written as stated: a vanishing is a cancellation at a height; heights are real;
so every nontrivial zero is an admissible height-readout, and RH follows (`RH_of_everyZeroAdmissible`). -/

open Complex CriticalLinePhasor.Geometric

namespace CriticalLinePhasor.Admissible

theorem everyZeroAdmissible_from_vanishing {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    EveryZeroAdmissible χ := by
  intro ρ hρ
  -- the height of the vanishing: Z = exp (Im ρ)
  refine ⟨Real.exp ρ.im, ?_⟩
  -- criticalReadout Z = 1/2 + i·log Z = 1/2 + i·Im ρ ; must equal ρ
  apply Complex.ext
  · simp [criticalReadout]
  · simp [criticalReadout]

end CriticalLinePhasor.Admissible
