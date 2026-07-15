import RequestProject.CPSTowerInstance3D
import RequestProject.CarrierFunctoriality
import RequestProject.DualPairFiber

/-!
# Three-dimensional CPS functoriality capstone

The local dual-pair polynomial, the all-height primal/contragredient reflection, the genuine
two-chart tower landing, and closure-preserving carrier composition are assembled here over the
same CPS Satake data.  In particular, the transport is not an abstract map supplied by a caller:
it is the actual general-linear action on the tower bank state, and closure means vanishing of the
actual two-chart bank readout.
-/

open Matrix
open scoped Classical

namespace CriticalLinePhasor.GlobalHelix

/-- Local CPS weights obey the general primal/contragredient polynomial reciprocity law. -/
theorem cpsTensorWeight_localReciprocity
    {κ : Type*} [Fintype κ] (r : ℕ) (alpha : UnitaryPrimePhase)
    (tau : UnitarySatakeFamily κ) (p : Nat.Primes) {X : ℂ} (hX : X ≠ 0) :
    DualPairFiber.dualLocalPoly (cpsTensorWeight r alpha tau p) X =
      (-X) ^ (Fintype.card (Fin (r + 1) × κ)) *
        (∏ i, cpsTensorWeight r alpha tau p i) *
          DualPairFiber.dualLocalPoly
            (DualPairFiber.dualWeights (cpsTensorWeight r alpha tau p)) X⁻¹ := by
  apply DualPairFiber.dualPair_localPoly_reciprocal
  · intro i hzero
    have hunit := cpsTensorWeight_unit r alpha tau p i
    rw [hzero, norm_zero] at hunit
    exact zero_ne_one hunit
  · exact hX

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.CarrierFunctoriality

section Transport

variable {n K κ : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K] [Fintype κ]

/-- The concrete carrier transport induced by the general-linear action on a CPS bank state. -/
def towerBankTransport (g : Matrix.GeneralLinearGroup n K) :
    Transport (TowerState n K (GlobalHelix.UnitarySatakeFamily κ)) :=
  fun x => g • x

/-- Exact focal closure for the tower bank is vanishing of its genuine two-chart readout. -/
noncomputable def towerBankCloses
    (i0 : n) (r : ℕ) (alpha : GlobalHelix.UnitaryPrimePhase)
    (x : TowerState n K (GlobalHelix.UnitarySatakeFamily κ)) : Prop :=
  towerChartReadout i0 r alpha x = 0

/-- The concrete CPS carrier transport preserves the complete two-chart bank readout. -/
theorem towerBankTransport_readout
    (i0 : n) (r : ℕ) (alpha : GlobalHelix.UnitaryPrimePhase)
    (g : Matrix.GeneralLinearGroup n K)
    (x : TowerState n K (GlobalHelix.UnitarySatakeFamily κ)) :
    towerChartReadout i0 r alpha (towerBankTransport (κ := κ) g x) =
      towerChartReadout i0 r alpha x := by
  exact towerBankInstance_landing i0 r alpha g x

/-- Every concrete CPS carrier transport preserves exact bank closure. -/
theorem towerBankTransport_faithful
    (i0 : n) (r : ℕ) (alpha : GlobalHelix.UnitaryPrimePhase)
    (g : Matrix.GeneralLinearGroup n K) :
    Faithful (towerBankCloses (κ := κ) i0 r alpha)
      (towerBankTransport (κ := κ) g) := by
  intro x hx
  unfold towerBankCloses at hx ⊢
  rw [towerBankTransport_readout i0 r alpha g x]
  exact hx

omit [Finite K] [Fintype κ] in
/-- The identity matrix induces the identity CPS carrier transport. -/
theorem towerBankTransport_one :
    towerBankTransport (κ := κ) (1 : Matrix.GeneralLinearGroup n K) =
      (id : Transport (TowerState n K (GlobalHelix.UnitarySatakeFamily κ))) := by
  funext x
  exact one_smul _ _

omit [Finite K] [Fintype κ] in
/-- Matrix multiplication is exactly composition of the induced CPS carrier transports. -/
theorem towerBankTransport_mul (g h : Matrix.GeneralLinearGroup n K) :
    towerBankTransport (κ := κ) (g * h) =
      towerBankTransport (κ := κ) g ∘ towerBankTransport (κ := κ) h := by
  funext x
  exact mul_smul g h x

omit [Finite K] [Fintype κ] in
/-- The concrete CPS tower transport is functorial: it preserves the identity and multiplication
as identity and composition of endomorphisms of the same three-dimensional bank state. -/
theorem towerBankTransport_functorial :
    towerBankTransport (κ := κ) (1 : Matrix.GeneralLinearGroup n K) =
        (id : Transport (TowerState n K (GlobalHelix.UnitarySatakeFamily κ))) ∧
      ∀ g h : Matrix.GeneralLinearGroup n K,
        towerBankTransport (κ := κ) (g * h) =
          towerBankTransport (κ := κ) g ∘ towerBankTransport (κ := κ) h := by
  exact ⟨towerBankTransport_one (κ := κ), towerBankTransport_mul (κ := κ)⟩

/--
Unified CPS functoriality payload on one three-dimensional Satake-bank state.

The clauses give local factor reciprocity, all-height bank reflection, tower landing, exact focal
closure preservation, identity, composition, and closure preservation by a composite transport.
-/
theorem cpsTowerFunctoriality3D_unified
    (i0 : n) (r : ℕ) (alpha : GlobalHelix.UnitaryPrimePhase)
    (x : TowerState n K (GlobalHelix.UnitarySatakeFamily κ))
    (p : Nat.Primes) {X : ℂ} (hX : X ≠ 0)
    (g h : Matrix.GeneralLinearGroup n K) :
    DualPairFiber.dualLocalPoly
        (GlobalHelix.cpsTensorWeight r alpha x.2 p) X =
      (-X) ^ (Fintype.card (Fin (r + 1) × κ)) *
        (∏ i, GlobalHelix.cpsTensorWeight r alpha x.2 p i) *
          DualPairFiber.dualLocalPoly
            (DualPairFiber.dualWeights
              (GlobalHelix.cpsTensorWeight r alpha x.2 p)) X⁻¹ ∧
    (∀ t : ℝ, 0 < t →
      GlobalHelix.cpsPrimal3DBankReadout r alpha x.2 (1 / t) =
        (t : ℂ) * GlobalHelix.cpsDual3DBankReadout r alpha x.2 t) ∧
    towerChartReadout i0 r alpha (towerBankTransport (κ := κ) g x) =
      towerChartReadout i0 r alpha x ∧
    Faithful (towerBankCloses (κ := κ) i0 r alpha)
      (towerBankTransport (κ := κ) g) ∧
    towerBankTransport (κ := κ) (1 : Matrix.GeneralLinearGroup n K) =
      (id : Transport (TowerState n K (GlobalHelix.UnitarySatakeFamily κ))) ∧
    towerBankTransport (κ := κ) (g * h) =
      towerBankTransport (κ := κ) g ∘ towerBankTransport (κ := κ) h ∧
    Faithful (towerBankCloses (κ := κ) i0 r alpha)
      (towerBankTransport (κ := κ) g ∘ towerBankTransport (κ := κ) h) ∧
    (let P := GlobalHelix.cpsDualPairStrongFEPair r alpha x.2;
      (∀ t : ℝ, 0 < t →
        P.f t = GlobalHelix.cpsPrimal3DBankReadout r alpha x.2 t ∧
        P.g t = GlobalHelix.cpsDual3DBankReadout r alpha x.2 t) ∧
      Differentiable ℂ P.Λ ∧
      Differentiable ℂ P.symm.Λ ∧
      (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
        u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
      (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
        u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
      (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s)) := by
  have hfunctor := towerBankTransport_functorial (n := n) (K := K) (κ := κ)
  refine ⟨GlobalHelix.cpsTensorWeight_localReciprocity r alpha x.2 p hX,
    ?_, towerBankTransport_readout i0 r alpha g x,
    towerBankTransport_faithful (κ := κ) i0 r alpha g,
    hfunctor.1, hfunctor.2 g h, ?_, ?_⟩
  · intro t ht
    exact GlobalHelix.cpsDualPair3D_globalHelixReflection r alpha x.2 ht
  · exact faithful_comp
      (towerBankTransport_faithful (κ := κ) i0 r alpha g)
      (towerBankTransport_faithful (κ := κ) i0 r alpha h)
  · dsimp only
    refine ⟨?_, GlobalHelix.cpsDualPair_twistedNiceness r alpha x.2⟩
    intro t ht
    exact ⟨GlobalHelix.cpsDualPairStrongFEPair_f_eq_3DBankReadout r alpha x.2 ht,
      GlobalHelix.cpsDualPairStrongFEPair_g_eq_3DBankReadout r alpha x.2 ht⟩

end Transport

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.GlobalHelix.cpsTensorWeight_localReciprocity
#print axioms CriticalLinePhasor.ThreeDConverse.towerBankTransport_readout
#print axioms CriticalLinePhasor.ThreeDConverse.towerBankTransport_faithful
#print axioms CriticalLinePhasor.ThreeDConverse.towerBankTransport_one
#print axioms CriticalLinePhasor.ThreeDConverse.towerBankTransport_mul
#print axioms CriticalLinePhasor.ThreeDConverse.towerBankTransport_functorial
#print axioms CriticalLinePhasor.ThreeDConverse.cpsTowerFunctoriality3D_unified
