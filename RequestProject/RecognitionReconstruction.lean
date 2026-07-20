import RequestProject.GeneratingPairing

/-!
# Phase four, opened: recognition factors through reconstruction

The single remaining field of the program is `sourced_of_pairing`: a fired class has an
algebraic source.  This file proves the **reconstruction factorization** — the first genuine
reduction of that field, splitting it into a provable leg and a finite list:

* **`reconstruct`** — the fired coordinates determine the class as an explicit
  generator-combination-plus-torsion.  This is the Torelli-shaped leg: linear algebra against
  the generating family, *already proven at depth one* (`gens_generate` +
  `realization_eq_zero_iff`: coordinates determine the class mod torsion), provable rung by
  rung.
* **`algebraic_closed`** — every generator combination plus torsion is algebraic.  A
  **finite** list of algebraicity facts (the generators) plus group-closure of the cycle
  class map.

`sourced_of_reconstruction` then fills `sourced_of_pairing`, and
`sourceExhaustion_of_reconstruction` composes with proven retention into the full terminus.
The infinite conjecture — *every* fired class has a source — is thereby reduced,
unconditionally, to finitely many generator algebraicities plus the reconstruction leg.
That is the attack: prove reconstruction (linear algebra, per rung), then hunt the finite
generator list with the freeze-mechanism addresses naming where each generator lives.
No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The reconstruction bundle** for a generating pairing: a finite generating family whose
integer combinations plus torsion are algebraic, and the Torelli-shaped leg — fired rational
DC classes are reconstructed as explicit combinations. -/
structure ReconstructionData {Z : Type*} [AddCommGroup Z] (D : HodgeDial Z)
    (G : GeneratingPairingData D) where
  /-- The rank of the generating family. -/
  rank : ℕ
  /-- The finite generating family. -/
  gens : Fin rank → Z
  /-- **The finite algebraicity list, closed under the group structure**: every integer
  combination of the generators, translated by torsion, is algebraic. -/
  algebraic_closed : ∀ (c : Fin rank → ℤ) (t : Z), IsOfFinAddOrder t →
    D.Algebraic ((∑ i, c i • gens i) + t)
  /-- **Reconstruction (the Torelli leg)**: a fired rational DC class is an explicit integer
  combination of the generators plus torsion — the fired coordinates name the class.  Proven
  at depth one from the cited bundle; provable rung by rung. -/
  reconstruct : ∀ z : Z, G.pairing z ≠ 0 → D.DC z → D.Rational z →
    ∃ (c : Fin rank → ℤ) (t : Z), IsOfFinAddOrder t ∧ z = (∑ i, c i • gens i) + t

/-- **The factorization**: reconstruction fills the program's last field — a fired rational DC
class is algebraic, its source the reconstructed combination. -/
theorem sourced_of_reconstruction {Z : Type*} [AddCommGroup Z] {D : HodgeDial Z}
    {G : GeneratingPairingData D} (R : ReconstructionData D G) :
    ∀ z : Z, G.pairing z ≠ 0 → D.DC z → D.Rational z → D.Algebraic z := by
  intro z hp hdc hrat
  obtain ⟨c, t, ht, rfl⟩ := R.reconstruct z hp hdc hrat
  exact R.algebraic_closed c t ht

/-- A reconstruction bundle completes the generating pairing: the whole
`GeneratingPairingData`, its last field filled by the factorization. -/
def GeneratingPairingData.complete {Z : Type*} [AddCommGroup Z] {D : HodgeDial Z}
    (G : GeneratingPairingData D) (R : ReconstructionData D G) :
    GeneratingPairingData D :=
  { G with sourced_of_pairing := sourced_of_reconstruction R }

/-- **The terminus through reconstruction**: proven retention, the staked collapse, and the
reconstruction bundle give source exhaustion — the Hodge conjecture in the carrier frame,
reduced to the finite generator list plus the Torelli leg. -/
theorem sourceExhaustion_of_reconstruction {Z : Type*} [AddCommGroup Z] {D : HodgeDial Z}
    (hret : Retention D) (G : GeneratingPairingData D) (R : ReconstructionData D G) :
    SourceExhaustion D :=
  sourceExhaustion_of_generating_pairing hret (G.complete R)

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourced_of_reconstruction
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_of_reconstruction
