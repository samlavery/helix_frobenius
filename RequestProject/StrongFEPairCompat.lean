import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Compatibility wrapper for strong functional-equation pairs

Mathlib 4.32 represents a strong functional-equation pair by a `WeakFEPair` together with an
`IsStrongFEPair` certificate.  The project historically used the equivalent bundled structure.
This file restores that bundled interface while delegating every analytic theorem to Mathlib's
current predicate API.
-/

noncomputable section

open Complex

/-- A bundled weak functional-equation pair whose two constant modes vanish. -/
structure StrongFEPair (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    extends WeakFEPair E where
  hf₀ : f₀ = 0
  hg₀ : g₀ = 0

namespace StrongFEPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The current Mathlib certificate carried by the bundled compatibility object. -/
theorem isStrong (P : StrongFEPair E) : IsStrongFEPair P.toWeakFEPair :=
  ⟨P.hf₀, P.hg₀⟩

/-- Symmetry preserves the vanishing of both constant modes. -/
def symm (P : StrongFEPair E) : StrongFEPair E :=
  StrongFEPair.mk P.toWeakFEPair.symm P.hg₀ P.hf₀

/-- The completed Mellin transform of a strong pair is its everywhere-convergent Mellin integral. -/
def Λ (P : StrongFEPair E) : ℂ → E :=
  mellin P.f

/-- A strong pair has a Mellin transform at every complex argument. -/
theorem hasMellin (P : StrongFEPair E) (s : ℂ) : HasMellin P.f s (P.Λ s) :=
  by
    change HasMellin P.f s (mellin P.f s)
    have h := P.isStrong.hasMellin s
    rw [P.isStrong.Λ_eq] at h
    exact h

/-- The completed Mellin transform of a strong pair is entire. -/
theorem differentiable_Λ (P : StrongFEPair E) : Differentiable ℂ P.Λ :=
  by
    change Differentiable ℂ (mellin P.f)
    rw [← P.isStrong.Λ_eq]
    exact P.isStrong.differentiable_Λ

/-- The bundled pair satisfies the same global functional equation as its underlying weak pair. -/
theorem functional_equation (P : StrongFEPair E) (s : ℂ) :
    P.Λ (P.k - s) = P.ε • P.symm.Λ s :=
  by
    change mellin P.f (P.k - s) = P.ε • mellin P.g s
    rw [← congrFun P.isStrong.Λ_eq (P.k - s),
      ← congrFun P.isStrong.symm_Λ_eq s]
    exact P.toWeakFEPair.functional_equation s

end StrongFEPair
