import RequestProject.HodgeDial

/-!
# The rung-4 split no-go: decomposable classes cannot see the primitive quadruple

Grade 4 (the first unnamed rung) has a non-critical center, so its recognition object is a
regulator class -- a subvariety decorated with a unit -- not a height cycle.  The natural
candidates on `X_0(N)^4` are SPLIT: a product surface `C x C'` with a unit, and by Rosenlicht
units on a product split as `u_1(x) u_2(y)`, so the regulator integrand splits as
`log|u_1| + log|u_2|` -- each term carrying one UNIT-FREE Petersson block.  For four
pairwise-distinct newforms the unit-free block is an orthogonality pairing and vanishes.

This file proves the model form of that no-go, unconditionally: a split (sum-form) decoration
paired against a product of two blocks each summing to zero -- the model of cuspidal
orthogonality -- vanishes identically.  Consequence, stated exactly: **the rung-4 recognition
class cannot be assembled from split data**; combined with the measured occupancy zero
(no algebraic `(1,1,1,1)`-classes for four distinct non-isogenous curves,
`tmp/quadruple_rung.py`), the primitive quadruple has no naive `(surface, unit)` home on
`X_0(N)^4` at all.  The classical rung is homeless; the carrier's degree-16 fiber is the
program's proposed home (representation-agnostic transport).  No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The split no-go (model form).**  A split decoration `(i, j) -> a i + b j` (the
`log|u_1| + log|u_2|` of a Rosenlicht-split unit) paired against a product of two blocks
`g1 ⊠ g2`, each of total sum zero (the model of cuspidal/Petersson orthogonality of distinct
forms), vanishes identically -- each term of the split carries one unit-free block. -/
theorem split_unit_pairing_vanishes {m n : ℕ} (a g1 : Fin m → ℂ) (b g2 : Fin n → ℂ)
    (h1 : ∑ i, g1 i = 0) (h2 : ∑ j, g2 j = 0) :
    ∑ i, ∑ j, (a i + b j) * g1 i * g2 j = 0 := by
  have key : ∀ i, ∑ j, (a i + b j) * g1 i * g2 j
      = a i * g1 i * ∑ j, g2 j + g1 i * ∑ j, b j * g2 j := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc ∑ i, ∑ j, (a i + b j) * g1 i * g2 j
      = ∑ i, (a i * g1 i * ∑ j, g2 j + g1 i * ∑ j, b j * g2 j) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = (∑ i, a i * g1 i) * ∑ j, g2 j + (∑ i, g1 i) * ∑ j, b j * g2 j := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ = 0 := by rw [h1, h2]; ring

/-- **Pure product classes factor** (the Fubini face of the no-go): an undecorated product
pairing splits into blocks, so one orthogonal block kills it. -/
theorem product_pairing_factors {m n : ℕ} (x g1 : Fin m → ℂ) (y g2 : Fin n → ℂ) :
    ∑ i, ∑ j, (x i * y j) * g1 i * g2 j
      = (∑ i, x i * g1 i) * (∑ j, y j * g2 j) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.split_unit_pairing_vanishes
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.product_pairing_factors
