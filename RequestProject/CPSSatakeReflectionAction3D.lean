import RequestProject.CPSUnconditionalSatakePayload3D

/-!
# The unconditional two-sheet reflection action of the CPS Satake bank

The primal sheet at reciprocal height and the contragredient sheet at direct height are retained
as two coordinates.  Exact three-dimensional helix closure identifies the coordinates, so every
permutation of the two sheets preserves their scalar readout.
-/

namespace CriticalLinePhasor.GlobalHelix

/-- A two-sheet complex state whose coordinates close to one scalar value. -/
structure CPSReflectionState where
  value : Bool → ℂ
  closed : ∀ b, value b = value false

@[ext]
theorem CPSReflectionState.ext {v w : CPSReflectionState}
    (h : v.value = w.value) : v = w := by
  cases v
  cases w
  cases h
  rfl

/-- Sheet permutations act by inverse reindexing. -/
instance : MulAction (Equiv.Perm Bool) CPSReflectionState where
  smul g v :=
    { value := fun b => v.value (g⁻¹ b)
      closed := fun b => by rw [v.closed (g⁻¹ b), v.closed (g⁻¹ false)] }
  one_smul v := by
    apply CPSReflectionState.ext
    funext b
    rfl
  mul_smul g h v := by
    apply CPSReflectionState.ext
    funext b
    rfl

/-- Scalar projection from the closed two-sheet state. -/
def CPSReflectionState.readout (v : CPSReflectionState) : ℂ := v.value false

/-- The concrete primal/contragredient Satake bank as a closed two-sheet state. -/
noncomputable def cpsSatakeReflectionState
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (x : ℝ) (hx : 0 < x) : CPSReflectionState where
  value b := if b then
    (x : ℂ) * cpsDual3DBankReadout r α τ x
  else
    cpsPrimal3DBankReadout r α τ (1 / x)
  closed b := by
    cases b
    · rfl
    · simpa using (cpsDualPair3D_globalHelixReflection r α τ hx).symm

/-- **Unconditional reflection-generator invariance.** No functional-equation or invariance
proposition is supplied by the caller: closure comes from the constructed strong Satake pair. -/
theorem cpsSatakeReflectionState_readout_invariant
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (x : ℝ) (hx : 0 < x)
    (g : Equiv.Perm Bool) :
    CPSReflectionState.readout (g • cpsSatakeReflectionState r α τ x hx) =
      CPSReflectionState.readout (cpsSatakeReflectionState r α τ x hx) := by
  exact (cpsSatakeReflectionState r α τ x hx).closed (g⁻¹ false)

/-- Uniform unconditional reflection invariance over every CPS twist degree. -/
theorem cpsAllTwists_reflectionState_readout_invariant
    (r : ℕ) (α : UnitaryPrimePhase) :
    ∀ (m : CPSTwistDegree r) (τ : UnitarySatakeFamily (Fin m.1))
      (x : ℝ) (hx : 0 < x) (g : Equiv.Perm Bool),
      CPSReflectionState.readout (g • cpsSatakeReflectionState r α τ x hx) =
        CPSReflectionState.readout (cpsSatakeReflectionState r α τ x hx) := by
  intro m τ x hx g
  exact cpsSatakeReflectionState_readout_invariant r α τ x hx g

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.cpsSatakeReflectionState_readout_invariant
#print axioms CriticalLinePhasor.GlobalHelix.cpsAllTwists_reflectionState_readout_invariant
