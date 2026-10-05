import RequestProject.CPSFunctorialityUnification3D
import RequestProject.FunctorialityCancellation

/-!
# Functoriality door audit: the rule-14 inhabitant check on the Sym^r capstones

Companion to `RequestProject/CapstoneDoorAudit.lean`, same method applied to the two
symmetric-power functoriality capstones.

## A. `symr_functoriality_cancellation` — hypothesis and conclusion are the same proposition

`FunctorialityCancellation.lean:90` reads `def PerronTauberian (a) (θ) : Prop := SummatoryBound a θ`.
So the hypothesis `hPT` of `symr_functoriality_cancellation` is a definitional alias for its own
conclusion, the two are interchangeable by `Iff.rfl` (`perronTauberian_iff_summatoryBound`), and
the proof term in the repository is literally `hPT`.  The archimedean parameter `κ` and the
constraint `hθ : θ < κ / 2` are not used: the implication still holds with both deleted
(`symr_cancellation_without_kappa`) and with `hθ` negated (`symr_cancellation_with_hypothesis_negated`).
The same applies to the `r = 2` instance `sym2_functoriality_cancellation`.

## B. `towerBankInstance_landing` — invariance of a function of the untouched coordinate

`TowerState n K B = (n → K) × B` and the `GL(n,K)` action is `g • x = (g.mulVec x.1, x.2)`, so
`(g • x).2 = x.2` by `rfl` (`towerState_smul_snd`).  The two-chart readout
`chartReadout i₀ P D x = if x.1 i₀ = 0 then P x.2 else D x.2` is the only place `x.1` appears, and
`towerChartReadout_eq` proves the two charts agree identically (`cpsDualPair_selfDualPointIdentity`),
so `towerChartReadout` factors through `Prod.snd` (`towerChartReadout_factors_through_snd`).
Full `GL(n,K)` invariance is then two rewrites (`landing_by_rfl`), for every rank, prime phase and
Satake family type — the group acts on a coordinate the readout does not read.

The repository's own `chartReadout_not_invariant_of_ne` is the converse half.  Together they give
`chartReadout_invariant_iff_charts_agree`: the chart readout is `GL(n,K)`-invariant **iff** the two
charts coincide, in which case the `if` is dead code and the readout is `D ∘ Prod.snd`.  There is no
configuration in which the mechanism is both nontrivial and invariant.

## C. `towerBankTransport_functorial` — the `MulAction` axioms

`smul_transport_functorial` below proves the identical statement for an arbitrary monoid acting on
an arbitrary type.  Nothing about `GL(n,K)`, Satake data, or symmetric powers is consumed;
"functorial" here means a group action is a group action.

No `axiom`, no `sorry`; footprint audited at the bottom.
-/

set_option linter.unusedSectionVars false

namespace FunctorialityDoorAudit

open scoped Classical MatrixGroups
open CriticalLinePhasor.Unfolding CriticalLinePhasor.ThreeDConverse

/-! ## A. The cancellation door is its own conclusion -/

/-- **The Perron/Tauberian "gap" is the conclusion.**  `PerronTauberian a θ` and
`SummatoryBound a θ` are the same proposition by definition, so
`symr_functoriality_cancellation` is the identity implication. -/
theorem perronTauberian_iff_summatoryBound (a : ℕ → ℝ) (θ : ℝ) :
    PerronTauberian a θ ↔ SummatoryBound a θ := Iff.rfl

/-- The archimedean parameter and the constraint `θ < κ / 2` are inert: the implication holds
with both removed. -/
theorem symr_cancellation_without_kappa (a : ℕ → ℝ) (θ : ℝ)
    (hPT : PerronTauberian a θ) : SummatoryBound a θ := hPT

/-- Sharper: the implication survives *negating* the constraint the docstring presents as the
reason the target is non-vacuous. -/
theorem symr_cancellation_with_hypothesis_negated (a : ℕ → ℝ) (κ θ : ℝ)
    (_hθ : κ / 2 ≤ θ) (hPT : PerronTauberian a θ) : SummatoryBound a θ := hPT

/-- The `r = 2` instance inherits the same status. -/
theorem sym2_cancellation_is_identity {k : ℤ} (f : CuspForm 𝒮ℒ k) (θ : ℝ) :
    PerronTauberian (sym2CoeffNorm f) θ ↔ SummatoryBound (sym2CoeffNorm f) θ := Iff.rfl

/-! ## B. The tower landing is the untouched coordinate -/

section Chart

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- Any readout that factors through `Prod.snd` is `GL(n,K)`-invariant, by `rfl`. -/
theorem snd_readout_invariant {B : Type*} (F : B → ℂ)
    (g : Matrix.GeneralLinearGroup n K) (x : TowerState n K B) :
    F (g • x).2 = F x.2 := rfl

/-- **Chart agreement collapses the two-chart readout to one chart.**  If the charts agree the
position coordinate is never consulted. -/
theorem chartReadout_eq_snd_of_agree {B : Type*} (i₀ : n) (P D : B → ℂ)
    (hPD : ∀ b, P b = D b) (x : TowerState n K B) :
    chartReadout i₀ P D x = D x.2 := by
  unfold chartReadout
  split
  · exact hPD x.2
  · rfl

/-- **The two-chart mechanism is invariant exactly when it is trivial.**
For `n` with at least two indices, `chartReadout i₀ P D` is `GL(n,K)`-invariant iff the two charts
coincide — and then it is `D ∘ Prod.snd`, invariant because the action does not touch `Prod.snd`.
Forward direction is the repository's own compiled falsifier
`chartReadout_not_invariant_of_ne`. -/
theorem chartReadout_invariant_iff_charts_agree {B : Type*} [Nontrivial n]
    (i₀ : n) (P D : B → ℂ) :
    (∀ (g : Matrix.GeneralLinearGroup n K) (x : TowerState n K B),
        chartReadout i₀ P D (g • x) = chartReadout i₀ P D x)
      ↔ ∀ b, P b = D b := by
  constructor
  · intro hinv b
    by_contra hne
    obtain ⟨j₀, hj₀⟩ := exists_ne i₀
    obtain ⟨g, x, hgx⟩ :=
      chartReadout_not_invariant_of_ne (K := K) i₀ j₀ (Ne.symm hj₀) P D b hne
    exact hgx (hinv g x)
  · intro hPD g x
    rw [chartReadout_eq_snd_of_agree i₀ P D hPD, chartReadout_eq_snd_of_agree i₀ P D hPD,
      towerState_smul_snd]

end Chart

section Bank

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
variable {κ : Type*} [Fintype κ]

/-- **The tower chart readout factors through the configuration coordinate.**  Restatement of the
repository's `towerChartReadout_eq`, making the factorization explicit. -/
theorem towerChartReadout_factors_through_snd (i₀ : n) (r : ℕ)
    (α : CriticalLinePhasor.GlobalHelix.UnitaryPrimePhase)
    (x : TowerState n K (CriticalLinePhasor.GlobalHelix.UnitarySatakeFamily κ)) :
    towerChartReadout i₀ r α x =
      (fun b => CriticalLinePhasor.GlobalHelix.cpsDual3DBankReadout r α b 1) x.2 :=
  towerChartReadout_eq i₀ r α x

/-- **The landing needs only `(g • x).2 = x.2`.**  A two-rewrite reproof of
`towerBankInstance_landing`, the "full `GL(n,K)` invariance for every rank" capstone: the group
acts on the position coordinate, and the readout reads the configuration coordinate. -/
theorem landing_by_rfl (i₀ : n) (r : ℕ)
    (α : CriticalLinePhasor.GlobalHelix.UnitaryPrimePhase)
    (g : Matrix.GeneralLinearGroup n K)
    (x : TowerState n K (CriticalLinePhasor.GlobalHelix.UnitarySatakeFamily κ)) :
    towerChartReadout i₀ r α (g • x) = towerChartReadout i₀ r α x := by
  rw [towerChartReadout_eq, towerChartReadout_eq, towerState_smul_snd]

end Bank

/-! ## C. "Functorial" is the `MulAction` axioms -/

/-- **The functoriality clause holds for every monoid action on every type.**  Identical in content
to `towerBankTransport_functorial`, with `GL(n,K)`, the Satake family and the rank all removed. -/
theorem smul_transport_functorial (G X : Type*) [Monoid G] [MulAction G X] :
    (fun x : X => (1 : G) • x) = (id : X → X) ∧
      ∀ g h : G, (fun x : X => (g * h) • x)
        = (fun x : X => g • x) ∘ (fun x : X => h • x) := by
  refine ⟨funext fun x => one_smul G x, fun g h => funext fun x => mul_smul g h x⟩

end FunctorialityDoorAudit

#print axioms FunctorialityDoorAudit.perronTauberian_iff_summatoryBound
#print axioms FunctorialityDoorAudit.symr_cancellation_without_kappa
#print axioms FunctorialityDoorAudit.symr_cancellation_with_hypothesis_negated
#print axioms FunctorialityDoorAudit.sym2_cancellation_is_identity
#print axioms FunctorialityDoorAudit.snd_readout_invariant
#print axioms FunctorialityDoorAudit.chartReadout_eq_snd_of_agree
#print axioms FunctorialityDoorAudit.chartReadout_invariant_iff_charts_agree
#print axioms FunctorialityDoorAudit.towerChartReadout_factors_through_snd
#print axioms FunctorialityDoorAudit.landing_by_rfl
#print axioms FunctorialityDoorAudit.smul_transport_functorial
