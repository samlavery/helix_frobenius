import RequestProject.GlobalHelixCPSDualPair

/-!
# Hypothesis-free analytic CPS payload from the three-dimensional Satake bank

The twist degree is packaged with its CPS range proof, and unitarity is packaged inside the prime
phase and Satake-family structures.  No analytic functional equation, continuation, strip bound,
or reflection proposition is supplied by the caller.
-/

namespace CriticalLinePhasor.GlobalHelix

/-- A twist degree in the CPS range `1 ≤ m < r`, with the range proof carried as data. -/
abbrev CPSTwistDegree (r : ℕ) := {m : ℕ // 1 ≤ m ∧ m < r}

/-- **Unconditional 3D analytic CPS payload.** The concrete primal/contragredient Satake banks
have exact global reflection, and their constructed strong pair is entire, bounded on every
vertical strip, and satisfies its functional equation. -/
theorem cpsTwist_unconditional3DAnalyticPayload
    (r : ℕ) (α : UnitaryPrimePhase) (m : CPSTwistDegree r)
    (τ : UnitarySatakeFamily (Fin m.1)) :
    (∀ x : ℝ, 0 < x →
      cpsPrimal3DBankReadout r α τ (1 / x) =
        (x : ℂ) * cpsDual3DBankReadout r α τ x) ∧
    (let P := cpsDualPairStrongFEPair r α τ;
      Differentiable ℂ P.Λ ∧
      Differentiable ℂ P.symm.Λ ∧
      (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
        u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
      (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
        u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
      (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s)) := by
  exact ⟨fun x hx => cpsDualPair3D_globalHelixReflection r α τ hx,
    cpsDualPair_twistedNiceness r α τ⟩

/-- The same payload uniformly for every CPS twist degree and every unitary Satake family. -/
theorem cpsAllTwists_unconditional3DAnalyticPayload
    (r : ℕ) (α : UnitaryPrimePhase) :
    ∀ (m : CPSTwistDegree r) (τ : UnitarySatakeFamily (Fin m.1)),
      (∀ x : ℝ, 0 < x →
        cpsPrimal3DBankReadout r α τ (1 / x) =
          (x : ℂ) * cpsDual3DBankReadout r α τ x) ∧
      (let P := cpsDualPairStrongFEPair r α τ;
        Differentiable ℂ P.Λ ∧
        Differentiable ℂ P.symm.Λ ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
        (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s)) := by
  intro m τ
  exact cpsTwist_unconditional3DAnalyticPayload r α m τ

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.cpsTwist_unconditional3DAnalyticPayload
#print axioms CriticalLinePhasor.GlobalHelix.cpsAllTwists_unconditional3DAnalyticPayload
