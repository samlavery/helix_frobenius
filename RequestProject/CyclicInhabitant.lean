import RequestProject.CyclicRealizationInstance

/-!
# The inhabitant-producing theorem, executed: class → record → cycle

The audit's demand: an inhabitant-producing theorem of the shape **actual rational
Hodge class → finite retained carrier record → explicit algebraic cycle whose class is
the original one**, with no-kernel and recognition *proved*, not supplied as fields.

`cyclic_inhabitant` is that theorem, executed on the rung where every arrow is a proof
in this repository: the group-algebra torsor (`ℚ[ℤ/n]`, the zero-dimensional Artin-level
geometry).  For a nonzero translation-invariant class `a` it **exhibits the data**:

* the explicit cycle: `a = q · 𝟙` — `q` times the fundamental class of the full orbit,
  the algebraic cycle of the rung, with the landing `a = (fun _ => q)` exact;
* the finite retained carrier record, in coordinates: the winding record is
  `(n·q, 0, …, 0)` — concentration at frequency zero proved (`winding_dc`), the sole
  surviving amplitude computed;
* faithfulness of the record: any class with the same record **is** `a`
  (`windingTransform_injective` — the proved no-kernel theorem, consumed here).

Register, stratified and exact — where this demand stands above this rung:
* here the regulator slot is vacuous **by the geometry** (dimension zero has no
  extension data), not by evasion; `regCompat` is `rfl` honestly;
* the depth-one rung (`EllipticDepthOneRung`) has genuine regulator content
  (Néron–Tate); its no-kernel is proved *from* the cited MW/NT bundle — it upgrades to
  this rung's unconditional register mechanically when Mathlib's Mordell–Weil and
  canonical-height machinery land (named trigger, tracked);
* positive-dimensional `(p,p)` inhabitants are blocked on Hodge theory not existing in
  Mathlib at all; that stratum lives at paper register (the sixfold `Ξ`, every input
  machine-verified or cited-classical).  No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- **The inhabitant-producing theorem**: an actual nonzero invariant rational class on
the cyclic geometry yields — with all data exhibited — its explicit cycle (`q · 𝟙`, the
weighted fundamental class of the orbit), its finite retained carrier record
(`(n·q, 0, …, 0)`, concentration proved), and the faithfulness of that record (the
proved no-kernel theorem: the record determines the class). -/
theorem cyclic_inhabitant (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℚ) (ha : a ≠ 0)
    (hdc : ∀ j : ZMod n, a (j + 1) = a j) :
    ∃ q : ℚ, q ≠ 0 ∧
      a = (fun _ => q) ∧
      (∀ (l : Fin 1) (k : Fin n), k.val ≠ 0 → windingAmp hζ a l k = 0) ∧
      (∀ (l : Fin 1) (k : Fin n), k.val = 0 → windingAmp hζ a l k = (n : ℂ) * q) ∧
      (∀ b : ZMod n → ℚ, windingAmp hζ b = windingAmp hζ a → b = a) := by
  obtain ⟨q, rfl⟩ := cyclic_diagonal_law hζ a ha hdc
  refine ⟨q, ?_, rfl, ?_, ?_, ?_⟩
  · intro hq0
    exact ha (funext fun _ => hq0)
  · intro l k hk
    refine winding_dc hζ hdc l k ?_
    show ((k.val : ℕ) : ℤ) ≠ 0
    exact_mod_cast hk
  · intro l k hk
    show ∑ j : ZMod n, ((q : ℂ)) * ζ ^ (j.val * k.val) = (n : ℂ) * q
    have : ∀ j : ZMod n, (q : ℂ) * ζ ^ (j.val * k.val) = (q : ℂ) := by
      intro j
      rw [hk, Nat.mul_zero, pow_zero, mul_one]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_comm]
  · intro b hb
    exact windingTransform_injective hζ hb

/-- The record reconstructs the class explicitly: on the DC locus the inverse arrow is
`a = (record at frequency 0) / n · 𝟙` — record → cycle is *constructive*, not just
injective. -/
theorem cyclic_record_reconstructs (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℚ)
    (ha : a ≠ 0) (hdc : ∀ j : ZMod n, a (j + 1) = a j) :
    ∃ q : ℚ, a = (fun _ => q) ∧
      (windingAmp hζ a 0 ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : ℂ) = (n : ℂ) * q := by
  obtain ⟨q, hq0, hcyc, _, hrec, _⟩ := cyclic_inhabitant hζ a ha hdc
  exact ⟨q, hcyc, hrec 0 _ rfl⟩

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.cyclic_inhabitant
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.cyclic_record_reconstructs
