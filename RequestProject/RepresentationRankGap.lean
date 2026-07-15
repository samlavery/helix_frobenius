import RequestProject.CarrierMellinContinuation

/-!
# Rank-gap extinction for genuine representation modules

The simple target is a module over a representation algebra `A`, while the dimension comparison is
taken over `ℂ`.  An `A`-linear residual into a simple target is either zero or surjective; after
restricting scalars to `ℂ`, surjectivity contradicts the strict dimension gap.  This is the form
needed by higher-rank tensor twists.
-/

open Complex Module

namespace CriticalLinePhasor.RepresentationRankGap

variable {A W V : Type*} [Ring A] [Algebra ℂ A]
  [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

/-- A smaller representation has no nonzero intertwiner into a simple larger representation. -/
theorem no_nonzero_intertwiner_of_finrank_lt
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    (hV : IsSimpleModule A V) (hdim : finrank ℂ W < finrank ℂ V)
    (f : W →ₗ[A] V) : f = 0 := by
  rcases hV.eq_bot_or_eq_top (LinearMap.range f) with h | h
  · exact LinearMap.range_eq_bot.mp h
  · exfalso
    have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp h
    have hle : finrank ℂ V ≤ finrank ℂ W :=
      (f.restrictScalars ℂ).finrank_le_finrank_of_surjective hsurj
    omega

/-- Every scalar readout of a rank-gap intertwining residual vanishes. -/
theorem constantMode_zero
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    (hV : IsSimpleModule A V) (hdim : finrank ℂ W < finrank ℂ V)
    (residue : W →ₗ[A] V) (readout : (W →ₗ[A] V) →ₗ[ℂ] ℂ) :
    readout residue = 0 := by
  rw [no_nonzero_intertwiner_of_finrank_lt hV hdim residue, map_zero]

/-- Full Mellin niceness when both constant modes are representation-theoretic intertwiners across
a strict rank gap. -/
theorem weakFEPair_twistedNiceness
    (P : WeakFEPair ℂ)
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    (hV : IsSimpleModule A V) (hdim : finrank ℂ W < finrank ℂ V)
    (residueF residueG : W →ₗ[A] V)
    (readoutF readoutG : (W →ₗ[A] V) →ₗ[ℂ] ℂ)
    (hf₀ : P.f₀ = readoutF residueF)
    (hg₀ : P.g₀ = readoutG residueG) :
    Differentiable ℂ (mellin P.f) ∧
    Differentiable ℂ (mellin P.g) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖mellin P.f s‖ ≤ C) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖mellin P.g s‖ ≤ C) ∧
    (∀ s : ℂ, mellin P.f (P.k - s) = P.ε * mellin P.g s) := by
  apply CriticalLinePhasor.CarrierMellinContinuation.zeroConstants_twistedNiceness P
  · rw [hf₀]
    exact constantMode_zero hV hdim residueF readoutF
  · rw [hg₀]
    exact constantMode_zero hV hdim residueG readoutG

end CriticalLinePhasor.RepresentationRankGap

#print axioms CriticalLinePhasor.RepresentationRankGap.no_nonzero_intertwiner_of_finrank_lt
#print axioms CriticalLinePhasor.RepresentationRankGap.constantMode_zero
#print axioms CriticalLinePhasor.RepresentationRankGap.weakFEPair_twistedNiceness
