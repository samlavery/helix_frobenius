import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Block indexing for the Sato--Tate concatenation

`exists_satoTate_block` supplies, for any rank ceiling and tolerance, a finite block whose
character averages are small.  Turning a sequence of such blocks into **one** sequence of angles
needs a position-to-block map, and the map has to satisfy two competing constraints:

* blocks must grow, so the node count — hence the rank ceiling — tends to infinity;
* blocks must grow *slowly*, so a partial block is negligible against everything before it.

Geometric growth fails the second (block `k` is as long as all its predecessors).  Quadratic
cumulative growth satisfies both, and has the advantage that the position-to-block map is just
`Nat.sqrt`:

  **block `k` occupies positions `[k², (k+1)²)`, so `blockOf N = Nat.sqrt N`, of length `2k+1`.**

Then the partial block is `≤ 2k+1` against a total of `≥ k²`, which vanishes, while `k → ∞`.

**Scope.**  This file is the index arithmetic only.  The angle sequence and the three convergence
estimates are not built here.
-/

open Filter

namespace CriticalLinePhasor.ThreeDConverse

/-- The block containing position `N`, where block `k` occupies `[k², (k+1)²)`. -/
def blockOf (N : ℕ) : ℕ := Nat.sqrt N

/-- The offset of `N` inside its block. -/
def offsetIn (N : ℕ) : ℕ := N - (blockOf N) ^ 2

theorem blockOf_sq_le (N : ℕ) : (blockOf N) ^ 2 ≤ N := by
  rw [blockOf]
  exact Nat.sqrt_le' N

theorem lt_succ_blockOf_sq (N : ℕ) : N < (blockOf N + 1) ^ 2 := by
  rw [blockOf]
  exact Nat.lt_succ_sqrt' N

/-- **The offset stays inside the block**: block `k` has length `2k + 1`. -/
theorem offsetIn_lt (N : ℕ) : offsetIn N < 2 * blockOf N + 1 := by
  have h1 := blockOf_sq_le N
  have h2 := lt_succ_blockOf_sq N
  have hexp : (blockOf N + 1) ^ 2 = (blockOf N) ^ 2 + (2 * blockOf N + 1) := by ring
  rw [hexp] at h2
  rw [offsetIn]
  omega

/-- **The block index recovers the position**: `N = k² + offset`. -/
theorem blockOf_add_offsetIn (N : ℕ) : (blockOf N) ^ 2 + offsetIn N = N := by
  have := blockOf_sq_le N
  rw [offsetIn]
  omega

/-- **Blocks grow**: the node count available at position `N` tends to infinity. -/
theorem blockOf_atTop : Tendsto blockOf atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M => ⟨M ^ 2, fun N hN => ?_⟩
  rw [blockOf, Nat.le_sqrt]
  calc M * M = M ^ 2 := (pow_two M).symm
    _ ≤ N := hN

/-- **A partial block is negligible**: its length is `2k+1` against a total of at least `k²`. -/
theorem offsetIn_le_two_mul_sqrt (N : ℕ) : offsetIn N ≤ 2 * Nat.sqrt N := by
  have := offsetIn_lt N
  rw [blockOf] at this
  omega


/-! ## Identifying a block by its position range

Block `j` occupies exactly `[j², (j+1)²)`, so membership in that interval pins both the block index
and the offset.  This is what lets a sum over positions be reorganised block by block. -/

theorem blockOf_eq {j N : ℕ} (h1 : j ^ 2 ≤ N) (h2 : N < (j + 1) ^ 2) : blockOf N = j := by
  have hle : j ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt]
    calc j * j = j ^ 2 := (pow_two j).symm
      _ ≤ N := h1
  have hlt : Nat.sqrt N < j + 1 := by
    rw [Nat.sqrt_lt]
    calc N < (j + 1) ^ 2 := h2
      _ = (j + 1) * (j + 1) := pow_two _
  rw [blockOf]
  omega

theorem offsetIn_eq {j N : ℕ} (h1 : j ^ 2 ≤ N) (h2 : N < (j + 1) ^ 2) :
    offsetIn N = N - j ^ 2 := by
  rw [offsetIn, blockOf_eq h1 h2]

/-- Every position of block `j` lies in `[j², (j+1)²)`, and there are `2j+1` of them. -/
theorem block_card (j : ℕ) :
    (Finset.Ico (j ^ 2) ((j + 1) ^ 2)).card = 2 * j + 1 := by
  rw [Nat.card_Ico]
  have : (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
  omega

/-- The positions below `(k+1)²` split into the blocks `0, …, k`. -/
theorem range_sq_eq_biUnion (k : ℕ) :
    Finset.range ((k + 1) ^ 2)
      = (Finset.range (k + 1)).biUnion fun j => Finset.Ico (j ^ 2) ((j + 1) ^ 2) := by
  ext N
  simp only [Finset.mem_range, Finset.mem_biUnion, Finset.mem_Ico]
  constructor
  · intro hN
    refine ⟨Nat.sqrt N, ?_, ?_, ?_⟩
    · have : Nat.sqrt N ≤ k := by
        rw [← Nat.lt_succ_iff, Nat.sqrt_lt]
        calc N < (k + 1) ^ 2 := hN
          _ = (k + 1) * (k + 1) := pow_two _
      omega
    · have := Nat.sqrt_le' N
      omega
    · have := Nat.lt_succ_sqrt' N
      omega
  · rintro ⟨j, hj, h1, h2⟩
    have hjk : j ≤ k := by omega
    calc N < (j + 1) ^ 2 := h2
      _ ≤ (k + 1) ^ 2 := by
          exact Nat.pow_le_pow_left (by omega) 2


/-! ## Summing over complete blocks

Blocks are pairwise disjoint (block `j` ends where block `j+1` begins), so a sum over `range (k²)`
is the sum of the first `k` block sums. -/

theorem blocks_pairwise_disjoint (k : ℕ) :
    (↑(Finset.range k) : Set ℕ).PairwiseDisjoint
      (fun j => Finset.Ico (j ^ 2) ((j + 1) ^ 2)) := by
  intro a _ b _ hab
  refine Finset.disjoint_left.mpr ?_
  intro x hx hy
  simp only [Finset.mem_Ico] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rcases Nat.lt_or_ge a b with h | h
  · have : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  · have hba : b < a := by omega
    have : (b + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

theorem range_sq_eq_biUnion' (k : ℕ) :
    Finset.range (k ^ 2)
      = (Finset.range k).biUnion fun j => Finset.Ico (j ^ 2) ((j + 1) ^ 2) := by
  ext N
  simp only [Finset.mem_range, Finset.mem_biUnion, Finset.mem_Ico]
  constructor
  · intro hN
    refine ⟨Nat.sqrt N, ?_, ?_, ?_⟩
    · rw [Nat.sqrt_lt]
      calc N < k ^ 2 := hN
        _ = k * k := pow_two k
    · have := Nat.sqrt_le' N; omega
    · have := Nat.lt_succ_sqrt' N; omega
  · rintro ⟨j, hj, _, h2⟩
    calc N < (j + 1) ^ 2 := h2
      _ ≤ k ^ 2 := Nat.pow_le_pow_left (by omega) 2

/-- **Complete blocks.**  A sum over `range (k²)` is the sum of the first `k` block sums. -/
theorem sum_range_sq_eq (k : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k ^ 2), f i
      = ∑ j ∈ Finset.range k, ∑ i ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2), f i := by
  rw [range_sq_eq_biUnion' k, Finset.sum_biUnion (blocks_pairwise_disjoint k)]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.offsetIn_lt
#print axioms CriticalLinePhasor.ThreeDConverse.blockOf_atTop
#print axioms CriticalLinePhasor.ThreeDConverse.blockOf_eq
#print axioms CriticalLinePhasor.ThreeDConverse.range_sq_eq_biUnion
#print axioms CriticalLinePhasor.ThreeDConverse.sum_range_sq_eq
