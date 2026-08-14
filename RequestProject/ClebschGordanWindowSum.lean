import Mathlib

/-!
# The Clebsch--Gordan window identity

The combinatorial core of the bank-level Clebsch--Gordan decomposition
`Sym^r ⊗ Sym^r = ⊕_{j=0}^{r} Sym^{2j}`, stated so that no bijection has to be constructed.

Writing exponents in units of `a ^ 2`, the pair bank `{α_i α_k}` carries exponent `r - i - k` at
`(i,k)`, and the block `Sym^{2j}` carries exponent `j - l` at `l ≤ 2j`.  The decomposition is the
statement that these two families of integers agree as multisets — equivalently that

  `∑_i ∑_k g (r - i - k)  =  ∑_j ∑_{l ≤ 2j} g (j - l)`

for **every** `g`.  Quantifying over `g` is what makes the induction work: adding a channel sends
`g` to `g (· + 1)`, the two blocks differ by a telescoping sum `g (j+1) - g (-j)`, and the new
boundary terms assemble into the single new block `∑_{u = -(r+1)}^{r+1} g u`.  No explicit
bijection `Fin (r+1) × Fin (r+1) ≃ Σ j, Fin (2j+1)` is ever needed.

Scope: this file proves the integer-exponent identity only.  Its application to the Satake pair
bank — normalizing the roots to `a ^ (r - 2i)` and reading the Euler logarithm through it — is not
in this file.
-/

open Finset

namespace CriticalLinePhasor.ClebschGordan

/-- Reflecting one block: `∑_{l ≤ 2j} (g (j+1-l) - g (j-l))` telescopes to `g (j+1) - g (-j)`. -/
theorem block_shift_sub {M : Type*} [AddCommGroup M] (g : ℤ → M) (j : ℕ) :
    (∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l + 1)) -
        (∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l)) =
      g ((j : ℤ) + 1) - g (-(j : ℤ)) := by
  rw [← Finset.sum_sub_distrib]
  have hstep : ∀ l ∈ range (2 * j + 1),
      g ((j : ℤ) - l + 1) - g ((j : ℤ) - l) =
        (fun t : ℕ => g ((j : ℤ) + 1 - t)) l - (fun t : ℕ => g ((j : ℤ) + 1 - t)) (l + 1) := by
    intro l _
    simp only
    congr 2 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub' (fun t : ℕ => g ((j : ℤ) + 1 - t))]
  congr 2
  push_cast
  ring

/-- The new block `∑_{u = -(r+1)}^{r+1} g u`, split at the centre. -/
theorem newBlock_split {M : Type*} [AddCommGroup M] (g : ℤ → M) (r : ℕ) :
    (∑ l ∈ range (2 * (r + 1) + 1), g (((r : ℤ) + 1) - l)) =
      (∑ l ∈ range (r + 1), g (((r : ℤ) + 1) - l)) +
        ∑ l ∈ range (r + 2), g (-(l : ℤ)) := by
  have hsplit : 2 * (r + 1) + 1 = (r + 1) + (r + 2) := by omega
  rw [hsplit, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  push_cast
  ring

/-- **The Clebsch--Gordan window identity.**  The pair exponents `r - i - k` and the block
exponents `j - l` agree as multisets, for every test function on the exponents. -/
theorem pair_sum_eq_block_sum {M : Type*} [AddCommGroup M] :
    ∀ (r : ℕ) (g : ℤ → M),
      (∑ i ∈ range (r + 1), ∑ k ∈ range (r + 1), g ((r : ℤ) - i - k)) =
        ∑ j ∈ range (r + 1), ∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l) := by
  intro r
  induction r with
  | zero => intro g; simp
  | succ r ih =>
      intro g
      simp only [Nat.cast_add, Nat.cast_one, show r + 1 + 1 = r + 2 from rfl]
      -- split the pair sum on the new row and column
      have hpair :
          (∑ i ∈ range (r + 2), ∑ k ∈ range (r + 2), g (((r : ℤ) + 1) - i - k)) =
            (∑ i ∈ range (r + 1), ∑ k ∈ range (r + 1), g (((r : ℤ) - i - k) + 1)) +
              (∑ i ∈ range (r + 1), g (-(i : ℤ))) +
                ∑ k ∈ range (r + 2), g (-(k : ℤ)) := by
        rw [Finset.sum_range_succ]
        have hrow : ∀ i ∈ range (r + 1),
            (∑ k ∈ range (r + 2), g (((r : ℤ) + 1) - i - k)) =
              (∑ k ∈ range (r + 1), g (((r : ℤ) - i - k) + 1)) + g (-(i : ℤ)) := by
          intro i _
          rw [Finset.sum_range_succ]
          congr 1
          · refine Finset.sum_congr rfl fun k _ => ?_
            congr 1
            push_cast
            ring
          · congr 1
            push_cast
            ring
        rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        push_cast
        ring
      -- the induction hypothesis, applied to the shifted test function
      have hIH := ih (fun u => g (u + 1))
      -- the block sums differ by a telescoping term
      have hblocks :
          (∑ j ∈ range (r + 1), ∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l + 1)) -
              (∑ j ∈ range (r + 1), ∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l)) =
            ∑ j ∈ range (r + 1), (g ((j : ℤ) + 1) - g (-(j : ℤ))) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => block_shift_sub g j
      have hnew := newBlock_split g r
      have hreflect :
          (∑ l ∈ range (r + 1), g (((r : ℤ) + 1) - l)) =
            ∑ j ∈ range (r + 1), g ((j : ℤ) + 1) := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        congr 1
        push_cast [Nat.cast_sub hj']
        ring
      have hcancel :
          ∑ j ∈ range (r + 1), ∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l + 1) =
            (∑ j ∈ range (r + 1), ∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l)) +
              ∑ j ∈ range (r + 1), (g ((j : ℤ) + 1) - g (-(j : ℤ))) := by
        rw [← hblocks]
        abel
      have hrhs :
          (∑ j ∈ range (r + 2), ∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l)) =
            (∑ j ∈ range (r + 1), ∑ l ∈ range (2 * j + 1), g ((j : ℤ) - l)) +
              ∑ l ∈ range (2 * (r + 1) + 1), g (((r : ℤ) + 1) - l) := by
        rw [Finset.sum_range_succ]
        congr 1
      rw [hpair, hIH, hcancel, hrhs, hnew, hreflect, Finset.sum_sub_distrib]
      abel

end CriticalLinePhasor.ClebschGordan

#print axioms CriticalLinePhasor.ClebschGordan.block_shift_sub
#print axioms CriticalLinePhasor.ClebschGordan.newBlock_split
#print axioms CriticalLinePhasor.ClebschGordan.pair_sum_eq_block_sum
