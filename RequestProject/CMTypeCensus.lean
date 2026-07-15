import Mathlib

/-!
# The CM-type census: the Weil-type obstruction is a dimension-4 phenomenon

A **CM type** for the cyclotomic field `ℚ(ζ_N)` is a choice `Φ ⊆ (ℤ/N)ˣ` of exactly one
of `{a, −a}` for every unit `a` (so `Φ ⊔ (−Φ)` is all of `(ℤ/N)ˣ`).  It records the
holomorphic half of the Hodge structure of the CM abelian variety `A_Φ` with complex
multiplication by `ℚ(ζ_N)`.  Two structural predicates decide the geometry:

* **primitive** — the multiplicative stabiliser `{g : g·Φ = Φ}` is trivial.  By the
  Shimura–Taniyama theory this is exactly the condition that `A_Φ` is **simple** (not
  isogenous to a product): a non-trivial stabiliser exhibits `Φ` as induced from a proper
  subfield, forcing a product decomposition.
* **`K`-balanced** — for an imaginary quadratic subfield `K ⊂ ℚ(ζ_N)`, given by an index-2
  subgroup `H ≤ (ℤ/N)ˣ` with `−1 ∉ H` (the real subfields are the `H ∋ −1`; `K` imaginary
  ⟺ `−1 ∉ H`), the **`K`-signature** of `Φ` is `(|Φ ∩ H|, |Φ ∖ H|)`.  `Φ` is balanced when
  the two halves are equal — signature `(2,2)` at `φ(N)=8` (dimension 4), `(3,3)` at
  `φ(N)=12` (dimension 6).  A balanced primitive type is a **simple abelian variety of Weil
  type**: `√−d ∈ K` acts on the tangent space with each eigenvalue of multiplicity `g/2`,
  and `A_Φ` carries the distinguished exceptional Hodge classes of type `(g/2, g/2)` — the
  Weil classes (Weil 1977; Moonen–Zarhin).

This file is the **finite combinatorial census** of those two predicates, verified by
kernel enumeration.  The search space of CM types is `2^{φ(N)/2} ≤ 64`, and the imaginary
quadratic subfields are the index-2 subgroups avoiding `−1`; everything is a decidable
computation over `(ℤ/N)ˣ` and the kernel checks it.  Two results:

  **(dimension 4) the obstruction.**  For every degree-8 cyclotomic field `ℚ(ζ_N)`,
  `N ∈ {15, 16, 20, 24}`, and every imaginary quadratic `K ⊂ ℚ(ζ_N)`, the number of CM
  types that are **both primitive and `K`-balanced-`(2,2)` is zero**
  (`no_simple_weil_fourfold_cyclotomic`).  A simple abelian fourfold of Weil type therefore
  has **no** cyclotomic (abelian) CM — it requires a non-abelian degree-8 CM field, exactly
  Mumford's 1969 polarisation twist.  This is *why* the point-countable cyclic-cover route
  cannot hand over a simple fourfold target directly.

  **(dimension 6) the dissolution.**  The obstruction does **not** persist.  For each of
  `N ∈ {21, 28, 36}` there are exactly two imaginary quadratic subfields, and each carries
  exactly **12** primitive `K`-balanced-`(3,3)` CM types (`simple_weil_sixfolds_exist`); the
  fields realised are `ℚ(√−3), ℚ(√−7), ℚ(i)`.  For `N ∈ {13, 26}` there is no imaginary
  quadratic subfield at all — `−1` is a square (`5² ≡ −1`), so it lies in the unique index-2
  subgroup and the unique quadratic subfield `ℚ(√13)` is real.  Simple cyclotomic Weil-type
  *sixfolds* thus exist abundantly, on the same exact Jacobi-sum infrastructure that carries
  no simple fourfold: the "simple ⇒ never balanced" obstruction is a dimension-4 fact that
  dissolves at dimension 6.

**Scope.**  This is the census of CM types and their `(primitive, K-balanced)` invariants —
a decidable enumeration over the units of `ℤ/N`, nothing more.  The identification of a
primitive `K`-balanced type with a *simple abelian variety of Weil type* (and of the balanced
`(g/2, g/2)` block with the exceptional Weil/Hodge classes) is the classical dictionary of
Shimura–Taniyama CM theory and the Moonen–Zarhin classification of Hodge classes on abelian
fourfolds; it is cited, not re-proven here.  In particular no claim is made about the
algebraicity of those classes (settled in dimension 4 by Markman, transcendentally; open in
general at dimension 6), and nothing here assumes or proves RH/GRH.  The DC/even-weight
reading of the balanced middle block — the `(2,2)` lane existing because the weight `4` is
even — is the companion parity law of `EvenWeightDC.lean`.  No `axiom`, no `sorry`; the
enumerations carry no axiom footprint.
-/

open List

namespace CriticalLinePhasor.CMTypeCensus

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-! ## The finite model over `(ℤ/N)ˣ` -/

/-- The units of `ℤ/N`, as the list of representatives `a ∈ [0, N)` coprime to `N`
(`(ℤ/N)ˣ` in the concrete finite model). -/
def unitsMod (N : ℕ) : List ℕ := (List.range N).filter (fun a => Nat.gcd a N == 1)

/-- The additive negative `−a` of a residue, `(N − a) mod N`; on a unit `a ∈ [1, N)` this is
the conjugate partner `N − a`. -/
def negMod (N a : ℕ) : ℕ := (N - a) % N

/-- Multiplication in `ℤ/N`. -/
def mulMod (N a b : ℕ) : ℕ := (a * b) % N

/-- One representative per conjugate pair `{a, −a}`: the units `a` with `a < N − a`. -/
def pairReps (N : ℕ) : List ℕ := (unitsMod N).filter (fun a => a < negMod N a)

/-- **All CM types of `ℚ(ζ_N)`**: choose one of `{a, −a}` for every conjugate pair.  A CM
type is a list of `φ(N)/2` units, one from each pair; there are `2^{φ(N)/2}` of them. -/
def cmTypes (N : ℕ) : List (List ℕ) :=
  (pairReps N).foldr (fun a acc => acc.flatMap (fun t => [a :: t, negMod N a :: t])) [[]]

/-- `z` **stabilises** `Φ` when `z · Φ = Φ` as sets (mutual containment of the multiplied
image `{(z·n) mod N : n ∈ Φ}` and `Φ`). -/
def stabilizes (N z : ℕ) (Φ : List ℕ) : Bool :=
  (Φ.map (mulMod N z)).all (fun x => Φ.contains x) &&
    Φ.all (fun x => (Φ.map (mulMod N z)).contains x)

/-- **Primitivity**: the only unit stabilising `Φ` is `1` — no `z ≠ 1` fixes `Φ`.  By CM
theory this is exactly simplicity of the CM abelian variety `A_Φ`. -/
def isPrimitive (N : ℕ) (Φ : List ℕ) : Bool :=
  ((unitsMod N).filter (fun z => z != 1)).all (fun z => ! stabilizes N z Φ)

/-- The **`K`-signature** of `Φ` relative to an index-2 subgroup `H` (an embedding of the
imaginary quadratic `K`): the pair `(|Φ ∩ H|, |Φ ∖ H|)`. -/
def kSignature (H Φ : List ℕ) : ℕ × ℕ :=
  let inside := Φ.countP (fun n => H.contains n)
  (inside, Φ.length - inside)

/-- `Φ` is **`K`-balanced-`(k, k)`**: its `K`-signature is `(k, k)` — the two conjugate
halves are equal.  The Weil-type condition (`k = g/2`). -/
def isBalanced (H : List ℕ) (k : ℕ) (Φ : List ℕ) : Bool := kSignature H Φ == (k, k)

/-- The census count: the number of CM types of `ℚ(ζ_N)` that are simultaneously
**primitive** (simple) and **`K`-balanced-`(k, k)`** (Weil type) for the subfield `H`. -/
def censusCount (N : ℕ) (H : List ℕ) (k : ℕ) : ℕ :=
  (cmTypes N).countP (fun Φ => isPrimitive N Φ && isBalanced H k Φ)

/-! ## The imaginary quadratic subfields as index-2 subgroups -/

/-- `H` is a multiplicatively closed subgroup: contains `1` and is closed under
`mulMod N`.  (For a finite set of units this forces closure under inverses.) -/
def isSubgroupClosed (N : ℕ) (H : List ℕ) : Bool :=
  H.contains 1 && H.all (fun a => H.all (fun b => H.contains (mulMod N a b)))

/-- **All index-2 subgroups of `(ℤ/N)ˣ`**: the multiplicatively closed sub-lists of the
units of length `φ(N)/2`.  Every index-2 subgroup appears (a closed length-`φ(N)/2` sublist
containing `1` is a subgroup of index 2), and only they do. -/
def index2Subgroups (N : ℕ) : List (List ℕ) :=
  ((unitsMod N).sublistsLen ((unitsMod N).length / 2)).filter (isSubgroupClosed N)

/-- **The imaginary quadratic subfields of `ℚ(ζ_N)`**: the index-2 subgroups `H` with
`−1 ∉ H` (`K` imaginary ⟺ `−1 ∉ H`; the `H ∋ −1` cut out the real quadratic subfields).
Each such `H` is one of the two embeddings `σ, σ̄` of an imaginary quadratic `K`. -/
def imaginaryQuadSubgroups (N : ℕ) : List (List ℕ) :=
  (index2Subgroups N).filter (fun H => ! H.contains (N - 1))

/-! ## Dimension 4 — the obstruction

For every degree-8 cyclotomic field and every imaginary quadratic subfield, there is **no**
CM type that is both primitive and balanced-`(2,2)`.  Each theorem records that the imaginary
quadratic subfields exist (their count) so the vanishing is not vacuous. -/

/-- `ℚ(ζ₁₅)`: two imaginary quadratic subfields (`ℚ(√−3), ℚ(√−15)`), each with **zero**
primitive balanced-`(2,2)` CM types. -/
theorem obstruction_15 :
    (imaginaryQuadSubgroups 15).length = 2 ∧
      ∀ H ∈ imaginaryQuadSubgroups 15, censusCount 15 H 2 = 0 := by decide

/-- `ℚ(ζ₁₆)`: two imaginary quadratic subfields (`ℚ(i), ℚ(√−2)`), each with **zero**
primitive balanced-`(2,2)` CM types. -/
theorem obstruction_16 :
    (imaginaryQuadSubgroups 16).length = 2 ∧
      ∀ H ∈ imaginaryQuadSubgroups 16, censusCount 16 H 2 = 0 := by decide

/-- `ℚ(ζ₂₀)`: two imaginary quadratic subfields (`ℚ(i), ℚ(√−5)`), each with **zero**
primitive balanced-`(2,2)` CM types. -/
theorem obstruction_20 :
    (imaginaryQuadSubgroups 20).length = 2 ∧
      ∀ H ∈ imaginaryQuadSubgroups 20, censusCount 20 H 2 = 0 := by decide

/-- `ℚ(ζ₂₄)`: four imaginary quadratic subfields (`ℚ(√−2), ℚ(√−3), ℚ(i), ℚ(√−6)`), each with
**zero** primitive balanced-`(2,2)` CM types. -/
theorem obstruction_24 :
    (imaginaryQuadSubgroups 24).length = 4 ∧
      ∀ H ∈ imaginaryQuadSubgroups 24, censusCount 24 H 2 = 0 := by decide

/-! ## Dimension 6 — the dissolution

The obstruction does not recur: for `N ∈ {21, 28, 36}` each of the two imaginary quadratic
subfields carries exactly 12 primitive balanced-`(3,3)` CM types, and `N ∈ {13, 26}` have no
imaginary quadratic subfield at all. -/

/-- `ℚ(ζ₂₁)`: two imaginary quadratic subfields (`ℚ(√−3), ℚ(√−7)`), each carrying exactly
**12** primitive balanced-`(3,3)` CM types — simple Weil-type sixfolds. -/
theorem dissolution_21 :
    (imaginaryQuadSubgroups 21).length = 2 ∧
      ∀ H ∈ imaginaryQuadSubgroups 21, censusCount 21 H 3 = 12 := by decide

/-- `ℚ(ζ₂₈)`: two imaginary quadratic subfields (`ℚ(√−7), ℚ(i)`), each carrying exactly
**12** primitive balanced-`(3,3)` CM types. -/
theorem dissolution_28 :
    (imaginaryQuadSubgroups 28).length = 2 ∧
      ∀ H ∈ imaginaryQuadSubgroups 28, censusCount 28 H 3 = 12 := by decide

/-- `ℚ(ζ₃₆)`: two imaginary quadratic subfields (`ℚ(√−3), ℚ(i)`), each carrying exactly
**12** primitive balanced-`(3,3)` CM types. -/
theorem dissolution_36 :
    (imaginaryQuadSubgroups 36).length = 2 ∧
      ∀ H ∈ imaginaryQuadSubgroups 36, censusCount 36 H 3 = 12 := by decide

/-- `ℚ(ζ₁₃)` has **no imaginary quadratic subfield**: its unique index-2 subgroup contains
`−1` (indeed `−1 = 5²` is a square), so the unique quadratic subfield `ℚ(√13)` is real. -/
theorem no_imaginary_quadratic_13 : imaginaryQuadSubgroups 13 = [] := by decide

/-- `ℚ(ζ₂₆)` has **no imaginary quadratic subfield**: as for `N = 13`, `−1 = 5²` lies in the
unique index-2 subgroup, and `ℚ(√13)` is real. -/
theorem no_imaginary_quadratic_26 : imaginaryQuadSubgroups 26 = [] := by decide

/-- The square witness behind `no_imaginary_quadratic_13`/`_26`: `−1` is a square modulo both
`13` and `26` (`5² ≡ −1`), hence lies in every index-2 subgroup, hence in every quadratic
subfield's group — no imaginary one can exist. -/
theorem neg_one_is_square_13_26 :
    (5 * 5) % 13 = 13 - 1 ∧ (5 * 5) % 26 = 26 - 1 := by decide

/-! ## Headline corollaries -/

/-- **No simple abelian fourfold of Weil type has cyclotomic CM.**  Across every degree-8
cyclotomic field `ℚ(ζ_N)`, `N ∈ {15, 16, 20, 24}`, and every imaginary quadratic subfield
`K ⊂ ℚ(ζ_N)`, the count of primitive (simple) balanced-`(2,2)` (Weil-type) CM types is `0`.
The dimension-4 obstruction: a simple Weil fourfold needs a non-abelian degree-8 CM field
(Mumford 1969). -/
theorem no_simple_weil_fourfold_cyclotomic :
    ∀ N ∈ ([15, 16, 20, 24] : List ℕ),
      ∀ H ∈ imaginaryQuadSubgroups N, censusCount N H 2 = 0 := by
  intro N hN
  fin_cases hN
  · exact obstruction_15.2
  · exact obstruction_16.2
  · exact obstruction_20.2
  · exact obstruction_24.2

/-- **Simple cyclotomic Weil-type sixfolds exist — 12 per imaginary quadratic field.**  For
each of `N ∈ {21, 28, 36}` there are exactly two imaginary quadratic subfields
`K ⊂ ℚ(ζ_N)`, and each carries exactly `12` primitive (simple) balanced-`(3,3)` (Weil-type)
CM types.  For `N ∈ {13, 26}` there is no imaginary quadratic subfield at all.  The
dimension-4 "simple ⇒ never balanced" obstruction dissolves at dimension 6. -/
theorem simple_weil_sixfolds_exist :
    (∀ N ∈ ([21, 28, 36] : List ℕ),
        (imaginaryQuadSubgroups N).length = 2 ∧
          ∀ H ∈ imaginaryQuadSubgroups N, censusCount N H 3 = 12) ∧
      imaginaryQuadSubgroups 13 = [] ∧ imaginaryQuadSubgroups 26 = [] := by
  refine ⟨?_, no_imaginary_quadratic_13, no_imaginary_quadratic_26⟩
  intro N hN
  fin_cases hN
  · exact dissolution_21
  · exact dissolution_28
  · exact dissolution_36

end CriticalLinePhasor.CMTypeCensus

#print axioms CriticalLinePhasor.CMTypeCensus.no_simple_weil_fourfold_cyclotomic
#print axioms CriticalLinePhasor.CMTypeCensus.simple_weil_sixfolds_exist
#print axioms CriticalLinePhasor.CMTypeCensus.obstruction_24
#print axioms CriticalLinePhasor.CMTypeCensus.dissolution_21
#print axioms CriticalLinePhasor.CMTypeCensus.no_imaginary_quadratic_13
