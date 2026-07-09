import Mathlib

/-!
# The Brauer-zero trap: obstruction removal versus false closure

`tmp/brauer_zero_trap.py` runs the adversarial removal test on genuine Brauer classes over `ℚ`
(Hamilton `(-1,-1)_ℚ`, and a class ramified at `{3,5}`), using Sage's quaternion-algebra /
Hilbert-symbol machinery as an independent oracle at every stage. This file formalises the *logical
core* that benchmark tests, in the abstract `ZMod 2`-invariant model of a `2`-torsion (quaternionic)
Brauer class: the local invariants at the ramified places form a vector `v : ι → ZMod 2` (the value
`1` standing for the invariant `1/2 ∈ ℚ/ℤ`), an extension acts by multiplying each invariant by its
local degree, and

* `false_closure` — **the trap.** The *aggregate* invariant (the sum, forced to `0` by global
  reciprocity) can vanish while the class is *retained* (`v ≠ 0`); a detector reading only the sum
  false-positives. Hamilton is the witness: `v = ![1,1]`, invariants `1/2` at `{2, ∞}`, sum `≡ 0`.
* `even_degree_kills`, `removal` — an extension whose local degree is **even** at every ramified
  place sends the invariant vector to `0`: the class is *split*, not merely its readout zeroed.
* `certified_removal` — the certificate is the **conjunction** `aggregate = 0 ∧ vector = 0`, strictly
  stronger than passing the trap (`aggregate = 0` alone, which `false_closure` shows is insufficient).
* `hamilton_removed` — the concrete instance: local degree `2` at each of `{2, ∞}` (realised over
  `ℚ(√-3)` in the script) kills the Hamilton vector.

The concrete arithmetic --- that `ℚ(√-3)` has even local degree at `2` and `∞`, that a hard-coded
`ℚ(i)` splits Hamilton but not the `{3,5}` class, and that `res[A] = 0` over the synthesised field ---
is the Sage benchmark's job (with Brauer theory as oracle). Formalised here is that the removal *logic*
is sound and, in particular, that a zero aggregate never counts as removal.

No `sorry`, no `axiom`; axiom footprint `{propext, Classical.choice, Quot.sound}`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.BrauerZeroTrap

variable {ι : Type*} [Fintype ι]

/-- The aggregate (global-reciprocity) readout: the sum of the local invariants. For a genuine
quaternion class the ramified set has even cardinality, so this is `0` --- the trap. -/
def aggregate (v : ι → ZMod 2) : ZMod 2 := ∑ i, v i

/-- Extension transport: multiply each local invariant by its local degree `deg i`. -/
def transport (deg : ι → ℕ) (v : ι → ZMod 2) : ι → ZMod 2 := fun i => (deg i : ZMod 2) * v i

/-- Hamilton `(-1,-1)_ℚ`: invariant `1/2` (encoded `1`) at each of the two ramified places `{2, ∞}`. -/
def hamilton : Fin 2 → ZMod 2 := ![1, 1]

/-- **The trap (false closure).** The aggregate readout vanishes on a *nonzero* class: reading only
`∑ inv` cannot distinguish a split class from a live one. The whole benchmark exists to force the
carrier past this point. -/
theorem false_closure : ∃ v : Fin 2 → ZMod 2, aggregate v = 0 ∧ v ≠ 0 :=
  ⟨hamilton, by decide, by decide⟩

/-- Hamilton is trapped: zero aggregate, nonzero obstruction. -/
theorem hamilton_trapped : aggregate hamilton = 0 ∧ hamilton ≠ 0 := ⟨by decide, by decide⟩

/-- **Even local degree kills a `2`-torsion invariant.** At a ramified place whose local degree in the
extension is even, the transported invariant is `0`. -/
theorem even_degree_kills {deg : ι → ℕ} (v : ι → ZMod 2) {i : ι} (h : Even (deg i)) :
    transport deg v i = 0 := by
  have hz : (deg i : ZMod 2) = 0 := (CharP.cast_eq_zero_iff (ZMod 2) 2 (deg i)).mpr h.two_dvd
  simp [transport, hz]

/-- **Removal.** An extension with even local degree at every ramified place sends the entire invariant
vector to `0`: the class is split, not merely read as zero. -/
theorem removal {deg : ι → ℕ} (v : ι → ZMod 2) (h : ∀ i, Even (deg i)) :
    transport deg v = 0 :=
  funext fun i => even_degree_kills v (h i)

/-- The vector vanishing forces the aggregate to vanish (removal implies a closed readout). -/
theorem aggregate_of_zero {v : ι → ZMod 2} (h : v = 0) : aggregate v = 0 := by
  simp [aggregate, h]

/-- **Certified removal.** The certificate is the *conjunction* `aggregate = 0 ∧ vector = 0`. By
`false_closure` the first conjunct alone is insufficient, so this is strictly stronger than passing
the trap: the obstruction coordinate is genuinely dead, not merely invisible to the sum. -/
theorem certified_removal {deg : ι → ℕ} (v : ι → ZMod 2) (h : ∀ i, Even (deg i)) :
    aggregate (transport deg v) = 0 ∧ transport deg v = 0 :=
  let hv := removal v h
  ⟨aggregate_of_zero hv, hv⟩

/-- **Hamilton removed.** Local degree `2` at each of `{2, ∞}` --- the degrees realised over `ℚ(√-3)`
in the benchmark --- kills the Hamilton invariant vector, and the certificate holds jointly. -/
theorem hamilton_removed :
    aggregate (transport ![2, 2] hamilton) = 0 ∧ transport ![2, 2] hamilton = 0 :=
  ⟨by decide, by decide⟩

/-- **The separation, abstractly.** Removal requires the *vector* to die; the trap only kills the
*sum*. So there is a state (Hamilton) that passes the aggregate test yet is not removed --- exactly
what the benchmark's Pass A detects and Passes D–E must repair. -/
theorem trap_weaker_than_removal :
    (∃ v : Fin 2 → ZMod 2, aggregate v = 0 ∧ v ≠ 0) ∧
      (∀ {ι : Type} [Fintype ι] (deg : ι → ℕ) (v : ι → ZMod 2),
        (∀ i, Even (deg i)) → transport deg v = 0) :=
  ⟨false_closure, fun deg v h => removal v h⟩

end CriticalLinePhasor.BrauerZeroTrap
