import RequestProject.LFunctionPhasor
import RequestProject.CarrierTargetIdentification
import RequestProject.RoundTrip
import RequestProject.CarrierFaithfulness
import RequestProject.FocalResidualVanishes
import RequestProject.Origination

/-!
# Relational equality: the classical Dirichlet L-function and its 3D fiber

The Dirichlet capstone of the fiber ontology: for every nonprincipal Dirichlet
character, the classical L-function and the 3D fiber are **equivalent
representations**, packaged as one structure with one instance theorem — the
scattered dictionary made a single citable anchor.

`DirichletFiberEquivalence χ` bundles the five relations:

1. **Readout equality** (`readout_eq`): on the whole strip `Re s > 0`, the fiber's
   phasor readout converges to the classical `DirichletCharacter.LFunction` — the
   analytically continued object, not just the series.
2. **Relational equality on ℂ** (`classical_is_unique_extension`): the classical
   L-function is **the unique entire extension** of the fiber readout — any entire
   function that reads the fiber on the strip *is* `LFunction χ`, everywhere.  The
   fiber determines the full classical object; the classical object is the fiber's
   one entire reading.
3. **Synthesis faithfulness** (`synthesis_faithful`): the character is determined by
   its coefficient bank — conduction is lossless.
4. **Ledgered exactness** (`ledger_roundtrip`): the projection/reconstruction round
   trip is a bijection — the descent to the chart books everything it drops.
5. **Structural intertwining**: the readout spin is unimodular and multiplicative
   (`spin_unimodular`, `spin_multiplicative`), the conduction is a `mod q` sorting
   (`conduction_mod`), the carrier winding is multiplicative over factorization
   (`winding_multiplicative`), and vanishing transports exactly: the fiber's
   completed focal residual vanishes at height `Z` iff the classical L-function
   vanishes at the represented point (`zeros_are_events`).

Proven in this file, unconditionally, for every modulus `q` and every nonprincipal
`χ`: the instance theorem `dirichletFiberEquivalence`.  Fields 1, 3, 4, 5 consume
compiled anchors (`dirichlet_strip_tendsto_LFunction`, `source_determined_by_bank`,
`ConeProjection.record_bijective`, `mellinSpin_norm`/`mellinSpin_mul`,
`windFromPrimes_mul`, `focal_residual_zero_iff_L_zero`); field 2 is the new
assembly (strip agreement + the identity-theorem core `entire_eq_of_eqOn_isOpen`
+ Mathlib's `differentiable_LFunction`).  Not in this file: the principal
character (its pole is the DC mass; it rides the completed/weak-pair route).  The
completed-`Λ`-level functional-equation intertwining (FE ↔ the involution `J`) is
the main paper's compiled content — the carrier reflection theorem, the strand
exchange (`StrandExchange.bankProduct_exchange`), and the completed assembly
(`FiniteWeightFiber.symTensorCompleted_FE`) — cited there, not re-proved here.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.FiberEquivalence

open CriticalLinePhasor.LFunctionPhasor
open CriticalLinePhasor.CarrierTargetIdentification
open CriticalLinePhasor.CarrierFaithfulness
open CriticalLinePhasor.HarmonicCell
open Origination

/-- The fiber's partial readout at chart point `s`: the first `N` phasors, summed. -/
noncomputable def fiberPartialReadout {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s)

/-- **Relational equality of the classical Dirichlet L-function and its 3D fiber.**
Five relations, one structure; the instance theorem below inhabits it for every
nonprincipal character, unconditionally. -/
structure DirichletFiberEquivalence {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Prop where
  /-- The fiber readout converges to the classical (continued) L-function on the
  whole strip `Re s > 0`. -/
  readout_eq : ∀ s : ℂ, 0 < s.re →
    Tendsto (fiberPartialReadout χ s) atTop (𝓝 (DirichletCharacter.LFunction χ s))
  /-- The classical L-function is THE unique entire extension of the fiber readout:
  any entire function reading the fiber on the strip equals `LFunction χ` on ℂ. -/
  classical_is_unique_extension : ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ s : ℂ, 0 < s.re → Tendsto (fiberPartialReadout χ s) atTop (𝓝 (F s))) →
    F = DirichletCharacter.LFunction χ
  /-- Conduction is lossless: the character is determined by its coefficient bank. -/
  synthesis_faithful :
    Function.Injective (fun ψ : DirichletCharacter ℂ q => (⇑ψ : ZMod q → ℂ))
  /-- The ledgered projection is exact: record/reconstruct is a bijection. -/
  ledger_roundtrip : Function.Bijective ConeProjection.record
  /-- The Mellin readout spin is unimodular. -/
  spin_unimodular : ∀ (y : ℝ) (n : ℕ), ‖mellinSpin y n‖ = 1
  /-- The Mellin readout spin is multiplicative. -/
  spin_multiplicative : ∀ (y : ℝ) (m n : ℕ), 0 < m → 0 < n →
    mellinSpin y (m * n) = mellinSpin y m * mellinSpin y n
  /-- Conduction sorts by residue: the bucket of `n` depends only on `n mod q`. -/
  conduction_mod : ∀ m n : ℕ, (m : ZMod q) = (n : ZMod q) →
    χ (m : ZMod q) = χ (n : ZMod q)
  /-- The carrier winding is multiplicative over unique factorization. -/
  winding_multiplicative : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 →
    windFromPrimes (m * n) = windFromPrimes m * windFromPrimes n
  /-- Vanishing transports exactly: the completed focal residual vanishes at height
  `Z` iff the classical L-function vanishes at the represented point. -/
  zeros_are_events : ∀ Z : ℝ, Dcell χ Z = 0 ↔
    DirichletCharacter.LFunction χ (reprPoint χ Z) = 0

/-- **The instance theorem**: every nonprincipal Dirichlet character's classical
L-function and 3D fiber are equivalent representations — unconditionally, at every
modulus. -/
theorem dirichletFiberEquivalence {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : DirichletFiberEquivalence χ where
  readout_eq := fun s hs => dirichlet_strip_tendsto_LFunction χ hχ hs
  classical_is_unique_extension := by
    intro F hF hstrip
    have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
      DirichletCharacter.differentiable_LFunction hχ
    have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
    refine entire_eq_of_eqOn_isOpen hF hLdiff hU h2 ?_
    intro s hs
    exact tendsto_nhds_unique (hstrip s hs)
      (dirichlet_strip_tendsto_LFunction χ hχ hs)
  synthesis_faithful := source_determined_by_bank
  ledger_roundtrip := ConeProjection.record_bijective
  spin_unimodular := mellinSpin_norm
  spin_multiplicative := fun y m n hm hn => mellinSpin_mul y m n hm hn
  conduction_mod := fun m n h => by rw [h]
  winding_multiplicative := fun hm hn => windFromPrimes_mul hm hn
  zeros_are_events := fun Z => focal_residual_zero_iff_L_zero χ Z

end CriticalLinePhasor.FiberEquivalence

#print axioms CriticalLinePhasor.FiberEquivalence.dirichletFiberEquivalence
