import Mathlib

/-!
# Carrier transport functoriality: the composition law

`tmp/composition_test.py` verifies exactly, at the integer-exponent (SU(2) character) level,
that the carrier transports induced by the paper's structural source maps -- symmetric power,
Rankin--Selberg tensor, base change -- satisfy the functoriality criterion of `rem:functor`:
identity, exact composition matching `W_{r∘s} = W_r ∘ W_s`, associativity, tensor and
base-change composition, and exact decomposition of a composite `Sym^a ∘ Sym^b` into irreducible
`Sym^c` blocks (the plethysm -- e.g. `Sym² ∘ Sym² = Sym⁴ ⊕ Sym⁰`, `Sym³ ∘ Sym³ = Sym⁹ ⊕ Sym⁵ ⊕
Sym³`), i.e. coherence up to block permutation.

Formalized here: (i) the abstract composition law -- carrier transports compose associatively
with a two-sided identity, and the *faithful* transports (those carrying exact focal closure to
exact focal closure) are closed under composition and contain the identity, so the carrier
realization preserves identity and composition; (ii) a concrete instance, base change
`bc p : e ↦ p·e`, with `bc p ∘ bc q = bc (p·q)` and `bc 1 = id`.
-/

namespace CriticalLinePhasor.CarrierFunctoriality

variable {S : Type*}

/-- A carrier transport of the carrier state `S` (the induced map on the normalized weight
system / bank). -/
abbrev Transport (S : Type*) := S → S

/-- `Faithful closes T`: the transport carries exact focal closure to exact focal closure --- the
faithfulness leg of the `rem:functor` criterion, with `closes` the exact-cell-closure predicate
(`∑_{k∈C} q_k = 0`, cf. `ForcibleClosure`). -/
def Faithful (closes : S → Prop) (T : Transport S) : Prop := ∀ x, closes x → closes (T x)

/-- Identity transport is faithful (the identity leg of functoriality). -/
theorem faithful_id (closes : S → Prop) : Faithful closes (id : Transport S) := fun _ h => h

/-- **Composition law (faithfulness).** The composite of two faithful transports is faithful:
exact focal closure is preserved along `T ∘ U`. With `faithful_id` this makes the faithful
transports closed under composition and containing the identity --- the carrier realization
preserves identity and composition. -/
theorem faithful_comp {closes : S → Prop} {T U : Transport S}
    (hT : Faithful closes T) (hU : Faithful closes U) : Faithful closes (T ∘ U) :=
  fun x h => hT (U x) (hU x h)

/-- Composition of transports is associative (functoriality). -/
theorem comp_assoc (T U V : Transport S) : (T ∘ U) ∘ V = T ∘ (U ∘ V) := rfl

/-- Left identity for composition. -/
theorem id_comp (T : Transport S) : (id : Transport S) ∘ T = T := rfl

/-- Right identity for composition. -/
theorem comp_id (T : Transport S) : T ∘ (id : Transport S) = T := rfl

/-- Base change to Frobenius degree `p`, acting on a weight exponent: `e ↦ p·e`. -/
def bc (p : ℤ) : Transport ℤ := fun e => p * e

/-- **Composition law (base-change instance).** `bc p ∘ bc q = bc (p·q)` --- base change
composes by multiplying Frobenius degrees, exactly (matching `composition_test.py`). -/
theorem bc_comp (p q : ℤ) : bc p ∘ bc q = bc (p * q) := by
  funext e; simp only [bc, Function.comp_apply]; ring

/-- Base change at degree `1` is the identity transport. -/
theorem bc_one : bc 1 = (id : Transport ℤ) := by funext e; simp [bc]

end CriticalLinePhasor.CarrierFunctoriality
