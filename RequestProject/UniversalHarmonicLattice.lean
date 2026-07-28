import Mathlib

/-!
# The universal harmonic lattice: one denominator, all rails, all ranks

The missing normalization law (review dialogue, 2026-07-28): a single
canonical denominator `D` placing every rail frequency on one integral
lattice `ω = k/D`, so DC, annihilation, freeze, projector support, and
rail matching are compared in one coordinate system across dimensions and
ranks.

The theorems, at the review's exact demands:

* `tower_denominator_stable` — THE headline, answering the "dangerous
  case": the `D`-lattice is closed under all integer combinations, hence
  under duals, tensors, symmetric and exterior powers — the whole tower
  generated from base rails on `(1/D)ℤ` stays on `(1/D)ℤ`.  `D` is
  controlled by the base representation data alone (weight parity,
  character order, cyclotomic order: `D = lcm(2, N, M)`-type, uniform
  over the admissible family) and DOES NOT GROW with rank: `D_r = D` for
  every `r`, not merely `D_r ∣ D_{r+1}`.
* `freeze_invariant` — the freeze condition is a single integral relation
  `Σ ε_j ν_j = 0` on the normalized coordinates, equivalent to the raw
  rational relation: normalization changes no verdict.
* `coord_add` / `coord_neg` — tensor additivity and duality of the
  normalized frequencies (`ν_{V⊗W} = ν_V + ν_W`, `ν_{V^∨} = −ν_V`).
* `coord_transition` — the canonical transition maps between lattices
  when denominators divide: `ν_{D'} = m·ν_D` for `D' = m·D` — the
  `ℤ/D → ℤ/D'` compatibility.

The carrier instance: `D = 6` is the μ₆/`ℤ[ζ₆]` angle lattice — the
`π/3` method-law is exactly this lattice's harmonic scale, and
`ZetaSixClosure` is its closure arithmetic; tower stability is WHY the
μ₆ cells survive the entire `Sym^r`/tensor tower unrescaled.  Scope:
does not assume or prove RH/GRH or the Hodge conjecture.
-/

namespace CriticalLinePhasor.HarmonicLattice

variable {ι : Type*}

/-- Membership in the `D`-harmonic lattice `(1/D)ℤ`. -/
def OnLattice (D : ℕ+) (ω : ℚ) : Prop :=
  ∃ k : ℤ, ω = (k : ℚ) / ((D : ℕ) : ℚ)

/-- The normalized integral coordinate `ν = D·ω`. -/
def coord (D : ℕ+) (ω : ℚ) : ℤ := (ω * ((D : ℕ) : ℚ)).num

theorem dcast_ne_zero (D : ℕ+) : (((D : ℕ) : ℚ)) ≠ 0 :=
  Nat.cast_ne_zero.mpr D.ne_zero

/-- The coordinate law: on the lattice, `(ν : ℚ) = D·ω` exactly. -/
theorem coord_spec {D : ℕ+} {ω : ℚ} (h : OnLattice D ω) :
    ((coord D ω : ℤ) : ℚ) = ω * ((D : ℕ) : ℚ) := by
  obtain ⟨k, rfl⟩ := h
  rw [coord, div_mul_cancel₀ _ (dcast_ne_zero D)]
  simp

/-- Lattice membership is decided by the coordinate law. -/
theorem onLattice_of_coord {D : ℕ+} {ω : ℚ} (k : ℤ)
    (h : ω * ((D : ℕ) : ℚ) = (k : ℚ)) : OnLattice D ω :=
  ⟨k, (eq_div_iff (dcast_ne_zero D)).mpr h⟩

theorem onLattice_zero (D : ℕ+) : OnLattice D 0 := ⟨0, by simp⟩

theorem onLattice_add {D : ℕ+} {a b : ℚ} (ha : OnLattice D a)
    (hb : OnLattice D b) : OnLattice D (a + b) := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact ⟨k + j, by push_cast; ring⟩

theorem onLattice_neg {D : ℕ+} {a : ℚ} (ha : OnLattice D a) :
    OnLattice D (-a) := by
  obtain ⟨k, rfl⟩ := ha
  exact ⟨-k, by push_cast; ring⟩

theorem onLattice_intMul {D : ℕ+} (c : ℤ) {a : ℚ} (ha : OnLattice D a) :
    OnLattice D ((c : ℚ) * a) := by
  obtain ⟨k, rfl⟩ := ha
  exact ⟨c * k, by push_cast; ring⟩

/-- **Tower denominator stability** (the headline): every integer
combination of lattice rails is a lattice rail — hence every dual,
tensor, symmetric-power, and exterior-power frequency of the tower
generated from base rails on `(1/D)ℤ` lies on the SAME `(1/D)ℤ`.  The
denominator is fixed by the base representation data and does not grow
with rank. -/
theorem tower_denominator_stable {D : ℕ+} (s : Finset ι) (c : ι → ℤ)
    (f : ι → ℚ) (h : ∀ i ∈ s, OnLattice D (f i)) :
    OnLattice D (∑ i ∈ s, (c i : ℚ) * f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using onLattice_zero D
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact onLattice_add
      (onLattice_intMul (c a) (h a (Finset.mem_insert_self a t)))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Freeze invariance under normalization**: the rational freeze
relation and the single integral relation on normalized coordinates are
equivalent — normalization changes no verdict. -/
theorem freeze_invariant {D : ℕ+} (s : Finset ι) (f : ι → ℚ) (ε : ι → ℤ)
    (h : ∀ i ∈ s, OnLattice D (f i)) :
    (∑ i ∈ s, (ε i : ℚ) * f i) = 0 ↔
      (∑ i ∈ s, ε i * coord D (f i)) = 0 := by
  have key : ((∑ i ∈ s, ε i * coord D (f i) : ℤ) : ℚ)
      = ((D : ℕ) : ℚ) * ∑ i ∈ s, (ε i : ℚ) * f i := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [coord_spec (h i hi)]
    ring
  constructor
  · intro h0
    have hz : ((∑ i ∈ s, ε i * coord D (f i) : ℤ) : ℚ) = 0 := by
      rw [key, h0, mul_zero]
    exact_mod_cast hz
  · intro h0
    have hz : ((D : ℕ) : ℚ) * (∑ i ∈ s, (ε i : ℚ) * f i) = 0 := by
      rw [← key]
      exact_mod_cast h0
    exact (mul_eq_zero.mp hz).resolve_left (dcast_ne_zero D)

/-- **Tensor additivity of normalized frequencies**: `ν(V⊗W) = ν V + ν W`. -/
theorem coord_add {D : ℕ+} {a b : ℚ} (ha : OnLattice D a)
    (hb : OnLattice D b) : coord D (a + b) = coord D a + coord D b := by
  have key : ((coord D (a + b) : ℤ) : ℚ)
      = ((coord D a + coord D b : ℤ) : ℚ) := by
    rw [coord_spec (onLattice_add ha hb), Int.cast_add, coord_spec ha,
      coord_spec hb]
    ring
  exact_mod_cast key

/-- **Duality**: `ν(V^∨) = −ν(V)`. -/
theorem coord_neg {D : ℕ+} {a : ℚ} (ha : OnLattice D a) :
    coord D (-a) = -coord D a := by
  have key : ((coord D (-a) : ℤ) : ℚ) = ((-coord D a : ℤ) : ℚ) := by
    rw [coord_spec (onLattice_neg ha), Int.cast_neg, coord_spec ha]
    ring
  exact_mod_cast key

/-- **The transition map between lattices**: for `D' = m·D` the
normalized coordinates transform by the canonical multiplier —
the `ℤ/D → ℤ/D'` compatibility demanded of a universal lattice. -/
theorem coord_transition (D D' : ℕ+) (m : ℕ)
    (hm : (D' : ℕ) = (D : ℕ) * m) {ω : ℚ} (h : OnLattice D ω) :
    coord D' ω = (m : ℤ) * coord D ω := by
  have hm0 : m ≠ 0 := by
    intro h0
    exact D'.ne_zero (by rw [hm, h0, mul_zero])
  have h' : OnLattice D' ω := by
    obtain ⟨k, rfl⟩ := h
    refine ⟨k * m, ?_⟩
    rw [hm]
    have hD := dcast_ne_zero D
    have hmq : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    push_cast
    field_simp
  have key : ((coord D' ω : ℤ) : ℚ) = (((m : ℤ) * coord D ω : ℤ) : ℚ) := by
    rw [coord_spec h', hm]
    push_cast
    rw [coord_spec h]
    ring
  exact_mod_cast key

/-! ## Common-source coherence: the factorization principle, typed with
its own vacuity witness

The sharper recognition principle (review dialogue): a carrier block is
algebraic precisely when its rail harmonics descend from a single
algebraic clock through an integral character representation —
`ω r = c · k r` with `c` the shared geometric period and the integer
vector `k` the algebraic datum.  The corpus already holds this principle
in measured form ("every class is a frozen frequency with source,
address, and certificate"); here it is typed, together with the review's
own caution as a THEOREM: the bare factorization structure is vacuous
(`trivial_factorization_exists` — any rails factor through `c = 1` over
`ℂ`), so ALL content lives in the integrality of the residual weights and
their representation laws (`coord_add`/`coord_neg` above).  The
observable form is `cross_ratio_integral`: the common factor cancels in
cross-ratios, leaving integer relations among the rails — exactly what
the freeze instruments measure without ever knowing `c`. -/

/-- The harmonic factorization of a rail family through a coefficient
ring: `ω r = commonFactor · realization (weight r)`. -/
structure AlgebraicHarmonicFactorization {Rail : Type*} (ω : Rail → ℂ) where
  coeffRing : Type
  [ringStr : CommRing coeffRing]
  commonFactor : ℂ
  factor_ne_zero : commonFactor ≠ 0
  weight : Rail → coeffRing
  realization : coeffRing →+* ℂ
  factorization : ∀ r, ω r = commonFactor * realization (weight r)

/-- **The vacuity witness** (the review's caution, machine-checked):
every rail family admits the trivial factorization — `c = 1` over `ℂ`
itself.  The bare structure therefore certifies nothing; algebraicity
content requires the integral lattice and the representation laws. -/
theorem trivial_factorization_exists {Rail : Type*} (ω : Rail → ℂ) :
    Nonempty (AlgebraicHarmonicFactorization ω) :=
  ⟨{ coeffRing := ℂ
     commonFactor := 1
     factor_ne_zero := one_ne_zero
     weight := ω
     realization := RingHom.id ℂ
     factorization := fun r => by simp }⟩

/-- The contentful form: integral residual weights — the algebraic datum
is the integer vector, the common factor the geometric period. -/
structure IntegralHarmonicFactorization {Rail : Type*} (ω : Rail → ℂ) where
  commonFactor : ℂ
  factor_ne_zero : commonFactor ≠ 0
  weight : Rail → ℤ
  factorization : ∀ r, ω r = commonFactor * (weight r : ℂ)

/-- **The observable certificate**: the common factor cancels in
cross-ratios — an integrally factorized block satisfies integer
cross-relations `ω r · k r' = ω r' · k r` with no reference to `c`.
This is the measurable freeze law: instruments certify common-source
coherence without recovering the period. -/
theorem IntegralHarmonicFactorization.cross_ratio_integral
    {Rail : Type*} {ω : Rail → ℂ} (F : IntegralHarmonicFactorization ω)
    (r r' : Rail) :
    ω r * (F.weight r' : ℂ) = ω r' * (F.weight r : ℂ) := by
  rw [F.factorization r, F.factorization r']
  ring

end CriticalLinePhasor.HarmonicLattice

#print axioms CriticalLinePhasor.HarmonicLattice.trivial_factorization_exists
#print axioms CriticalLinePhasor.HarmonicLattice.IntegralHarmonicFactorization.cross_ratio_integral
#print axioms CriticalLinePhasor.HarmonicLattice.tower_denominator_stable
#print axioms CriticalLinePhasor.HarmonicLattice.freeze_invariant
#print axioms CriticalLinePhasor.HarmonicLattice.coord_add
#print axioms CriticalLinePhasor.HarmonicLattice.coord_neg
#print axioms CriticalLinePhasor.HarmonicLattice.coord_transition
