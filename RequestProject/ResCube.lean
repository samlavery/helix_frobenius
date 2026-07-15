import Mathlib

/-!
# The Res-cube identity: the algebraic heart of the freeze-order mechanism

Placeholder docstring — replaced once the proof lands.
-/

open Finset

namespace ResCube

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- Root-form resultant `Res(f, g) = ∏_{i,j} (aᵢ − bⱼ)` for the monic split polynomials
`f = ∏ᵢ (X − aᵢ)`, `g = ∏ⱼ (X − bⱼ)`. -/
def resRoots (a : Fin m → R) (b : Fin n → R) : R := ∏ i, ∏ j, (a i - b j)

/-- Root-form discriminant `disc(f) = ∏_{i<j} (aᵢ − aⱼ)²` for the monic split polynomial
`f = ∏ᵢ (X − aᵢ)`. -/
def discRoots (a : Fin m → R) : R := ∏ i, ∏ j ∈ Finset.Ioi i, (a i - a j) ^ 2

/-- The root-form derivative value `f′(aᵢ) = ∏_{k≠i} (aᵢ − a_k)` (for `f = ∏(X − aᵢ)`, the
value of `f′` at the simple root `aᵢ`). -/
def derivProd (a : Fin m → R) (i : Fin m) : R := ∏ k ∈ Finset.univ.erase i, (a i - a k)

/-- The product of the **leading Laurent coefficients** of `h = f · g²` at its finite branch
points, in root form.  At a simple root `aᵢ` of `f` the point is simple on `h` with leading
coefficient `f′(aᵢ)·g(aᵢ)²`; at a simple root `bⱼ` of `g` the point is a double point of `h`
with leading coefficient `f(bⱼ)·g′(bⱼ)²`.  Here `g(aᵢ) = ∏ⱼ (aᵢ − bⱼ)` and
`f(bⱼ) = ∏ᵢ (bⱼ − aᵢ)`.  This is the integer `C` of the freeze mechanism (`weil_scout §L4`). -/
def bigC (a : Fin m → R) (b : Fin n → R) : R :=
  (∏ i, derivProd a i * (∏ j, (a i - b j)) ^ 2) *
    (∏ j, (∏ i, (b j - a i)) * (derivProd b j) ^ 2)

/-! ## The two sign lemmas -/

/-- The number of strictly-ordered index pairs is the binomial `C(m, 2)`. -/
theorem sum_card_Ioi (m : ℕ) : (∑ i : Fin m, (Finset.Ioi i).card) = m.choose 2 := by
  simp only [Fin.card_Ioi, Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_reflect (fun i => i) m, Nat.choose_two_right]
  have := Finset.sum_range_id_mul_two m
  omega

/-- `∏ᵢ f′(aᵢ) = (−1)^{C(m,2)} · disc(f)` — the classical `Res(f, f′) = ±disc(f)`
in root form. -/
theorem prod_derivProd (a : Fin m → R) :
    (∏ i, derivProd a i) = (-1) ^ m.choose 2 * discRoots a := by
  rw [discRoots]
  have hset : ∀ i : Fin m, Finset.univ.erase i = Finset.Iio i ∪ Finset.Ioi i := by
    intro i; ext k
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi,
      Finset.mem_univ, and_true]
    exact ne_iff_lt_or_gt
  have hdisj : ∀ i : Fin m, Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    intro i
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_Iio, Finset.mem_Ioi] at hk hk'
    exact absurd (hk.trans hk') (lt_irrefl _)
  have hsplit : ∀ i : Fin m, derivProd a i
      = (∏ k ∈ Finset.Iio i, (a i - a k)) * (∏ k ∈ Finset.Ioi i, (a i - a k)) := by
    intro i
    rw [derivProd, hset i, Finset.prod_union (hdisj i)]
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib]
  have hcomm : (∏ i, ∏ k ∈ Finset.Iio i, (a i - a k))
      = ∏ k, ∏ i ∈ Finset.Ioi k, (a i - a k) := by
    apply Finset.prod_comm'; intro i k; simp [Finset.mem_Iio, Finset.mem_Ioi]
  rw [hcomm, ← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib]
  have hterm : ∀ x y : Fin m, (a y - a x) * (a x - a y) = (-1) * (a x - a y) ^ 2 :=
    fun x y => by ring
  simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum, sum_card_Ioi]

/-- `∏ⱼ f(bⱼ) = (−1)^{d_f d_g} · Res(f, g)` — the classical `Res(g, f) = (−1)^{d_f d_g} Res(f, g)`
in root form. -/
theorem prod_swap_cross (a : Fin m → R) (b : Fin n → R) :
    (∏ j, ∏ i, (b j - a i)) = (-1) ^ (m * n) * resRoots a b := by
  rw [resRoots, Finset.prod_comm]
  have hterm : ∀ (i : Fin m) (j : Fin n), (b j - a i) = (-1) * (a i - b j) := fun i j => by ring
  simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm n m]

/-! ## The Res-cube identity (the heart) -/

/-- **THE RES-CUBE IDENTITY.**  For monic coprime squarefree `f = ∏(X − aᵢ)`,
`g = ∏(X − bⱼ)` and `h = f · g²`, the product of the leading Laurent coefficients of `h` at
its finite branch points is
`C = (−1)^{C(d_f,2) + d_f·d_g} · disc(f) · disc(g)² · Res(f, g)³`.
The resultant enters **as a perfect cube**: the `f`-branches each see `g²` (contributing
`Res²`) and the `g`-branches each see `f` (contributing `Res¹`), for total exponent `3`.  The
sign of the `g`-side discriminant squares away, which is why only `C(d_f,2) + d_f·d_g` survives
in the exponent. -/
theorem resCube_identity (a : Fin m → R) (b : Fin n → R) :
    bigC a b
      = (-1) ^ (m.choose 2 + m * n) * discRoots a * (discRoots b) ^ 2 * (resRoots a b) ^ 3 := by
  have hsq : (∏ j, derivProd b j) ^ 2 = (discRoots b) ^ 2 := by
    rw [prod_derivProd, mul_pow, ← pow_mul, Even.neg_one_pow ⟨n.choose 2, by ring⟩, one_mul]
  have hF : (∏ i, derivProd a i * (∏ j, (a i - b j)) ^ 2)
      = (-1) ^ (m.choose 2) * discRoots a * (resRoots a b) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, prod_derivProd, resRoots]
  have hG : (∏ j, (∏ i, (b j - a i)) * (derivProd b j) ^ 2)
      = (-1) ^ (m * n) * resRoots a b * (discRoots b) ^ 2 := by
    rw [Finset.prod_mul_distrib, prod_swap_cross, Finset.prod_pow, hsq]
  rw [bigC, hF, hG, pow_add]; ring

/-- **The resultant enters as a perfect cube.**  `C = (unit sign) · disc(f) · disc(g)² · w³`
with `w = Res(f, g)` — witnessed existentially, so the cube structure is manifest and
character-agnostic. -/
theorem resCube_is_cube (a : Fin m → R) (b : Fin n → R) :
    ∃ w : R, bigC a b = (-1) ^ (m.choose 2 + m * n) * discRoots a * (discRoots b) ^ 2 * w ^ 3 :=
  ⟨resRoots a b, resCube_identity a b⟩

/-- **The cubic character kills the resultant.**  For any multiplicative map `χ : R →* S` that
is cubic (`χ x ^ 3 = 1` for all `x`), the value `χ(C)` depends only on the sign and the
discriminants: the resultant drops out, because it enters `C` as a cube.  This is the freeze
mechanism's `U = χ₃(C) = χ₃(disc(f)·disc(g)²)` step (`weil_scout §L4`); combined with
`χ₃(−1) = 1` the sign drops too, leaving `χ₃(D)` with `D = disc(f)·disc(g)²`. -/
theorem cubic_char_kills_resultant {S : Type*} [CommMonoid S] (χ : R →* S)
    (hχ : ∀ x : R, χ x ^ 3 = 1) (a : Fin m → R) (b : Fin n → R) :
    χ (bigC a b) = χ ((-1) ^ (m.choose 2 + m * n) * discRoots a * (discRoots b) ^ 2) := by
  rw [resCube_identity, map_mul, map_pow, hχ (resRoots a b), mul_one]

/-! ## The multiplicity-1 counterfactual — why balance matters -/

/-- The **multiplicity-1** product of leading coefficients for `h = f · g` (the squarefree
cover `y³ = f g`, item 37's counterfactual).  At a simple root `aᵢ` of `f` the leading
coefficient is `f′(aᵢ)·g(aᵢ)`; at a simple root `bⱼ` of `g` it is `f(bⱼ)·g′(bⱼ)`. -/
def bigC1 (a : Fin m → R) (b : Fin n → R) : R :=
  (∏ i, derivProd a i * (∏ j, (a i - b j))) * (∏ j, (∏ i, (b j - a i)) * (derivProd b j))

/-- **Why the balanced multiplicity-2 structure matters.**  With multiplicity 1 the resultant
enters `C′` as `Res²` — an **even** power, *not* a cube.  A cubic character does not annihilate
`Res²` in general (`χ₃(Res²) = χ̄₃(Res) ≠ 1`), so the freeze fails.  It is precisely the
multiplicity-2 (`g²`) structure of `y³ = f g²` — `f`-branches see `g²` and `g`-branches see `f`,
total exponent `2 + 1 = 3` — that erases `Res` from the freeze invariant.  Note also the
`g`-side discriminant sign `C(d_g,2)` now survives (`disc(g)` appears to the first power),
whereas in the cube identity it squared away. -/
theorem mult_one_resultant_sq (a : Fin m → R) (b : Fin n → R) :
    bigC1 a b = (-1) ^ (m.choose 2 + m * n + n.choose 2)
      * discRoots a * discRoots b * (resRoots a b) ^ 2 := by
  have hF1 : (∏ i, derivProd a i * (∏ j, (a i - b j)))
      = (-1) ^ (m.choose 2) * discRoots a * resRoots a b := by
    rw [Finset.prod_mul_distrib, prod_derivProd, resRoots]
  have hG1 : (∏ j, (∏ i, (b j - a i)) * (derivProd b j))
      = (-1) ^ (m * n) * resRoots a b * ((-1) ^ (n.choose 2) * discRoots b) := by
    rw [Finset.prod_mul_distrib, prod_swap_cross, prod_derivProd]
  rw [bigC1, hF1, hG1, pow_add, pow_add]; ring

end ResCube
