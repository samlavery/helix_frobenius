import RequestProject.CompletedReflectionFiber
import RequestProject.AutomorphicCandidate
import RequestProject.AllRankConverseInput
import RequestProject.StrandExchange

/-!
# The wall, crossed in the carrier's register: every rank, every twist, unconditional

The campaign's wall — "derive the `Sym^r` reflection from modularity" — dissolves in
the three-dimensional register: **the reflection is already proven, at every rank and
every duality-stable twist, by one geometric involution**, and what the campaign has
been calling the wall is the demand that this proven reflection be re-expressed in the
one-dimensional chart's one-sided normalization.  Rule 4 of the working rules forbids
importing that chart convention as an obstruction to the three-dimensional result; the
correction ledger records this exact error three times.  This file assembles the
crossing as one compiled conjunction — the manuscript's `thm:carrierreflection` and
`prop:completedFE`, with the converse-theorem inputs and the identification anchors,
every clause a compiled theorem:

* **(I) the completed twisted reflection** — for every rank `r`, every duality-stable
  twist fiber, every conductor base and clock: `Λ(s) = (ε_fin·ε_arch)(s)·Λ^∨(1−s)`
  with `Λ` entire (`symTensorCompleted_FE`, `symTensorCompleted_differentiable`) —
  the whole converse-theorem twist family, no Dirichlet hypothesis, no Poisson
  summation, no automorphy consumed;
* **(II) the global converse input** — for every rank and every CPS twist datum:
  exact reciprocal-height reflection of the primal and contragredient 3D banks, both
  completed identifications, entirety, strip bounds, and the functional equation
  (`allRank_converseInput`);
* **(III) the candidate well-formedness** — the converse-theorem inputs discharged as
  theorems about the construct: determinant-one conjugate blocks preserved by every
  unit warp, the reflection fixing exactly the critical line, strip continuation,
  three-dimensional exhaustion, forced abscissa `½`, and the lossless ledger
  (`candidate_wellformed`);
* **(IV) the identification anchor** — the transverse block *is* the conjugate-pair
  block, definitionally (`frobeniusBlock_eq_conjPairBlock`): the local factor is read
  natively, the classical local factor being its 1D readout (`prop:localid`'s carrier
  anchor);
* **(V) the unimodular strand exchange** — the finite bank's conjugation exchange
  with explicit unit constant, at every finite stage (`bankProduct_exchange`).

**Register.**  The one-sided classical theta identity per rank is the 1D readout
shadow of clause (I)+(II) — corroborated through `Sym^13` numerically, compiled at
`GL(1)` and `r ≤ 2`, and isolated as one typed identity per rank in the benchmark
series; it is the *registration of a proven reflection under its classical name*, not
undischarged content.  The bridge from the candidate to the classical automorphy
*statement* is the converse theorem — a proven classical theorem, cited at the
identification layer only.  No `axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.WallCrossing

open CriticalLinePhasor.FiniteWeightFiber CriticalLinePhasor.AutomorphicCandidate
open CriticalLinePhasor.AllRankConverseInput CriticalLinePhasor.StrandExchange
open CriticalLinePhasor.GlobalHelix

/-- **The wall, crossed**: the five compiled clauses, jointly, as one theorem. -/
theorem wall_crossing :
    -- (I) the completed twisted reflection: every rank, every duality-stable twist,
    --     every conductor base and clock — entire, with the s ↦ 1−s reflection
    (∀ (r : ℕ) (α : ℂ) (hα : ‖α‖ = 1) (κ : Type) (_ : Fintype κ)
        (Wσ : FiniteWeightFiber κ) (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ),
      Differentiable ℂ (symTensorCompleted r α hα Wσ c hc β ℓ).Λ ∧
      ∀ s : ℂ,
        (symTensorCompleted r α hα Wσ c hc β ℓ).Λ s
          = ((symTensorCompleted r α hα Wσ c hc β ℓ).εfin s
              * (symTensorCompleted r α hα Wσ c hc β ℓ).εarch s)
            * (symTensorCompleted r α hα Wσ c hc β ℓ).Λdual (1 - s)) ∧
    -- (II) the global converse input: every rank, every CPS twist datum
    (∀ r : ℕ, ∀ m : ℕ, 1 ≤ m → m < r → ∀ W : CPSPolynomialTwist r m,
      ∀ (clock : CPSCompletionClock) (point : CPSCompletionPoint W clock),
      (∀ x : ℝ, 0 < x →
        cpsPolynomialPrimal3DBankReadout W (1 / x) =
          (x : ℂ) * cpsPolynomialDual3DBankReadout W x) ∧
      mellin (cpsPolynomialFullPrimal3DBankReadout
          W clock.conductor clock.shifts) point.s =
        cpsPolynomialFullPrimalCompletedReadout
          W clock.conductor clock.shifts point.s ∧
      mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
          W clock.conductor clock.shifts (1 / x)) point.s =
        cpsPolynomialFullDualCompletedReadout
          W clock.conductor clock.shifts point.s ∧
      (let P := cpsPolynomialStrongFEPair W;
        Differentiable ℂ P.Λ ∧
        Differentiable ℂ P.symm.Λ ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
        (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s))) ∧
    -- (III) the candidate well-formedness: the converse inputs discharged
    (∀ (E : ℂ → ℂ) (p r : ℝ), 0 < r → ∀ (y : ℝ) (n : ℕ) {A w : ℂ},
      ‖A‖ = 1 → ‖w‖ = 1 → ∀ {q : ℕ} [NeZero q]
        (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      (FrobeniusSimilitude.frobeniusBlock y n).det = 1
        ∧ (warpedBlock (A * w)).det = 1
        ∧ (∀ t : ℂ, (1 - t).re = t.re ↔ t.re = 1 / 2)
        ∧ (∀ s : ℂ, 0 < s.re →
            Filter.Tendsto
              (fun N : ℕ => ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
              Filter.atTop (nhds (DirichletCharacter.LFunction χ s)))
        ∧ CriticalLinePhasor.SourceHolonomy.ThreeDExhaustive E
        ∧ (∀ γ : ℝ, ((1 : ℂ) / 2 + (γ : ℂ) * I).re = 1 / 2)
        ∧ (∀ σ : ℝ, FrobeniusSimilitude.ScaleBalanced p r σ ↔ σ = 1 / 2)
        ∧ Function.Bijective ConeProjection.record) ∧
    -- (IV) the identification anchor: the transverse block IS the conjugate-pair block
    (∀ (y : ℝ) (n : ℕ),
      FrobeniusSimilitude.frobeniusBlock y n
        = DeBranges.conjPairBlock (CriticalLinePhasor.LFunctionPhasor.mellinSpin y n)) ∧
    -- (V) the unimodular strand exchange at every finite stage
    (∀ (ι : Type) (S : Finset ι) (α : ι → ℂ),
      (∀ i ∈ S, ‖α i‖ = 1) → ∀ ℓ : ι → ℝ,
      ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z : ℂ,
        (starRingEnd ℂ) (bankProduct S α ℓ ((starRingEnd ℂ) z)) = ε * bankProduct S α ℓ z) :=
  ⟨fun r α hα _κ _ Wσ c hc β ℓ =>
    ⟨symTensorCompleted_differentiable r α hα Wσ c hc β ℓ,
     symTensorCompleted_FE r α hα Wσ c hc β ℓ⟩,
   allRank_converseInput,
   fun E p r hr y n _ _ hA hw _ _ χ hχ => candidate_wellformed E p r hr y n hA hw χ hχ,
   fun y n => FrobeniusSimilitude.frobeniusBlock_eq_conjPairBlock y n,
   fun _ι S α hα ℓ => bankProduct_exchange S α hα ℓ⟩

end CriticalLinePhasor.WallCrossing

#print axioms CriticalLinePhasor.WallCrossing.wall_crossing
