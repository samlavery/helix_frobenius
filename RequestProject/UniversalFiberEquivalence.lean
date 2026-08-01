import RequestProject.DirichletFiberEquivalence

/-!
# Relational equality, universal: any classical readout and its 3D fiber

The class-free capstone.  `DirichletFiberEquivalence` proved the five-relation
equivalence for every nonprincipal Dirichlet character; this file states and proves
the same equivalence with the source abstracted to an arbitrary coefficient bank
`a : ℕ → ℂ` and an arbitrary classical reading `F : ℂ → ℂ` — the fiber ontology's
"the fiber is the function itself," class-free.

* `entire_readings_unique` — **the hypothesis-free core**: for ANY bank, any two
  entire functions that read the fiber on the strip `Re s > 0` are equal on all of
  ℂ.  No character, no growth condition, no functional equation: the fiber readout
  admits at most one entire reading, ever.  (Uniqueness is a property of the
  carrier's chart, not of any source class.)
* `UniversalFiberEquivalence a F` — the five relations of the Dirichlet capstone
  with the source abstracted: readout equality on the strip, global uniqueness of
  the entire reading, synthesis faithfulness for every function-like source type,
  ledgered exactness, and the universal intertwining laws (unimodular
  multiplicative readout spin; multiplicative carrier winding).
* `universalFiberEquivalence` — the instance theorem: any differentiable `F` read
  by the fiber on the strip is THE representation, with all five relations.
* `universalFiberEquivalence_of_dirichlet` — non-vacuity on genuine arithmetic:
  every nonprincipal Dirichlet character instantiates the universal structure with
  `F = DirichletCharacter.LFunction χ`, directly from the Dirichlet capstone.

Proven in this file: everything above, unconditionally.  Not in this file: sources
whose classical reading has a pole (the principal character/ζ: the reading is
meromorphic, its pole the DC mass — the completed/weak-pair route extends the
structure there).  The completed-`Λ`-level functional-equation intertwining
(FE ↔ `J`) is the main paper's compiled content — the carrier reflection theorem,
`StrandExchange.bankProduct_exchange`, `FiniteWeightFiber.symTensorCompleted_FE` —
cited there, not re-proved here.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.FiberEquivalence

open CriticalLinePhasor.LFunctionPhasor
open CriticalLinePhasor.CarrierTargetIdentification
open CriticalLinePhasor.CarrierFaithfulness
open Origination

/-- The universal fiber partial readout of a coefficient bank at chart point `s`. -/
noncomputable def bankPartialReadout (a : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * (n : ℂ) ^ (-s)

/-- **The hypothesis-free uniqueness core**: any two entire readings of any bank
agree on all of ℂ.  The fiber readout admits at most one entire reading — a fact
about the carrier's chart, consuming nothing about the source. -/
theorem entire_readings_unique (a : ℕ → ℂ) {G G' : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG' : Differentiable ℂ G')
    (hreadG : ∀ s : ℂ, 0 < s.re →
      Tendsto (bankPartialReadout a s) atTop (𝓝 (G s)))
    (hreadG' : ∀ s : ℂ, 0 < s.re →
      Tendsto (bankPartialReadout a s) atTop (𝓝 (G' s))) :
    G = G' := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
  refine entire_eq_of_eqOn_isOpen hG hG' hU h2 ?_
  intro s hs
  exact tendsto_nhds_unique (hreadG s hs) (hreadG' s hs)

/-- **Relational equality, universal**: the five relations of the Dirichlet
capstone with the source abstracted to a bank `a` and a classical reading `F`. -/
structure UniversalFiberEquivalence (a : ℕ → ℂ) (F : ℂ → ℂ) : Prop where
  /-- The fiber readout converges to the classical reading on the strip. -/
  readout_eq : ∀ s : ℂ, 0 < s.re →
    Tendsto (bankPartialReadout a s) atTop (𝓝 (F s))
  /-- The classical reading is THE unique entire reading of the fiber. -/
  classical_is_unique_extension : ∀ G : ℂ → ℂ, Differentiable ℂ G →
    (∀ s : ℂ, 0 < s.re → Tendsto (bankPartialReadout a s) atTop (𝓝 (G s))) →
    G = F
  /-- Conduction is lossless for every function-like source type. -/
  synthesis_faithful : ∀ {S α β : Type} [inst : FunLike S α β],
    Function.Injective (fun ψ : S => (⇑ψ : α → β))
  /-- The ledgered projection is exact: record/reconstruct is a bijection. -/
  ledger_roundtrip : Function.Bijective ConeProjection.record
  /-- The Mellin readout spin is unimodular. -/
  spin_unimodular : ∀ (y : ℝ) (n : ℕ), ‖mellinSpin y n‖ = 1
  /-- The Mellin readout spin is multiplicative. -/
  spin_multiplicative : ∀ (y : ℝ) (m n : ℕ), 0 < m → 0 < n →
    mellinSpin y (m * n) = mellinSpin y m * mellinSpin y n
  /-- The carrier winding is multiplicative over unique factorization. -/
  winding_multiplicative : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 →
    windFromPrimes (m * n) = windFromPrimes m * windFromPrimes n

/-- **The universal instance theorem**: any differentiable classical reading that
the fiber reads on the strip is THE representation — all five relations,
unconditionally, for every bank. -/
theorem universalFiberEquivalence (a : ℕ → ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hread : ∀ s : ℂ, 0 < s.re →
      Tendsto (bankPartialReadout a s) atTop (𝓝 (F s))) :
    UniversalFiberEquivalence a F where
  readout_eq := hread
  classical_is_unique_extension := fun G hG hreadG =>
    entire_readings_unique a hG hF hreadG hread
  synthesis_faithful := fun {_ _ _} [FunLike _ _ _] => source_determined_by_bank
  ledger_roundtrip := ConeProjection.record_bijective
  spin_unimodular := mellinSpin_norm
  spin_multiplicative := fun y m n hm hn => mellinSpin_mul y m n hm hn
  winding_multiplicative := fun hm hn => windFromPrimes_mul hm hn

/-- **Non-vacuity on genuine arithmetic**: every nonprincipal Dirichlet character
instantiates the universal structure with its classical L-function. -/
theorem universalFiberEquivalence_of_dirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    UniversalFiberEquivalence (fun n : ℕ => χ (n : ZMod q))
      (DirichletCharacter.LFunction χ) :=
  universalFiberEquivalence _ _
    (DirichletCharacter.differentiable_LFunction hχ)
    (fun s hs => (dirichletFiberEquivalence χ hχ).readout_eq s hs)

end CriticalLinePhasor.FiberEquivalence

#print axioms CriticalLinePhasor.FiberEquivalence.entire_readings_unique
#print axioms CriticalLinePhasor.FiberEquivalence.universalFiberEquivalence
#print axioms CriticalLinePhasor.FiberEquivalence.universalFiberEquivalence_of_dirichlet
