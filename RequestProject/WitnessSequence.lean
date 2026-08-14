import RequestProject.SatoTateBlock
import RequestProject.RunLength
import RequestProject.BlockIndex
import RequestProject.PeriodicSum
import RequestProject.LinearCesaro

/-!
# The witness sequence

Every piece is now in place, so this file writes the sequence down.  Position `N` sits in block
`k = blockOf N` at offset `offsetIn N`; block `k` uses `blockNodes k ≈ k^{1/4}` Gauss--Chebyshev
nodes with multiplicity budget `blockBudget k ≈ k^{1/2}`, and the offset selects a node by
run-length decoding, cycling if the block slot outlasts one pass.

The three scales are chosen so that all three error terms vanish:

* **ranks reached** `2·blockNodes k − 2 ≈ 2k^{1/4} → ∞`;
* **within-cycle error** `blockNodes k·(r+1)/(blockBudget k − blockNodes k) ≈ k^{-1/4} → 0`
  (`satoTate_block_bound`);
* **partial cycle and partial block** `blockTotal k ≈ k^{1/2}` and `2k+1` against a running total
  of `≥ k²`, both `→ 0` relatively.

**What is proved here.**  The definition, and that it lands in `[0, π]` — so it is a legitimate
Satake angle assignment.  The three estimates above are *not* proved here; they are the remaining
work, and nothing in this file claims the sequence equidistributes.
-/

open Filter
open scoped Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- Node count for block `k`, about `k^{1/4}`, never below two. -/
noncomputable def blockNodes (k : ℕ) : ℕ := max 2 (Nat.sqrt (Nat.sqrt k))

/-- Multiplicity budget for block `k`, about `k^{1/2}`. -/
noncomputable def blockBudget (k : ℕ) : ℝ := (Nat.sqrt k : ℝ)

/-- Multiplicity of node `i` in block `k`. -/
noncomputable def blockMult (k i : ℕ) : ℕ :=
  (⌊blockBudget k * stWeight (blockNodes k) i⌋).toNat

/-- Total length of one pass through block `k`'s nodes. -/
noncomputable def blockTotal (k : ℕ) : ℕ := runStart (blockMult k) (blockNodes k)

theorem two_le_blockNodes (k : ℕ) : 2 ≤ blockNodes k := le_max_left _ _

/-- **The witness sequence.**  A Satake angle for every position. -/
noncomputable def witnessAngle (N : ℕ) : ℝ :=
  if blockTotal (blockOf N) = 0 then Real.pi / 2
  else
    stAngle (blockNodes (blockOf N))
      (runIndex (blockMult (blockOf N)) (blockNodes (blockOf N))
        (offsetIn N % blockTotal (blockOf N)))

/-- **It is a legitimate angle.** -/
theorem witnessAngle_mem (N : ℕ) : witnessAngle N ∈ Set.Icc 0 Real.pi := by
  rw [witnessAngle]
  split_ifs with h
  · constructor
    · positivity
    · linarith [Real.pi_pos]
  · set k := blockOf N with hk
    have hpos : 0 < blockTotal k := Nat.pos_of_ne_zero h
    have hlt : offsetIn N % blockTotal k < blockTotal k := Nat.mod_lt _ hpos
    have hidx : runIndex (blockMult k) (blockNodes k) (offsetIn N % blockTotal k)
        < blockNodes k := runIndex_lt (by rw [← blockTotal]; exact hlt)
    constructor
    · exact (stAngle_pos (by omega : 0 < blockNodes k)).le
    · exact (stAngle_lt_pi hidx).le

/-- The angles all lie in the closed interval the Satake parameter uses. -/
theorem witnessAngle_nonneg (N : ℕ) : 0 ≤ witnessAngle N := (witnessAngle_mem N).1

theorem witnessAngle_le_pi (N : ℕ) : witnessAngle N ≤ Real.pi := (witnessAngle_mem N).2

/-- **The node count grows**, so the rank ceiling of the block containing position `N` tends to
infinity. -/
theorem blockNodes_blockOf_atTop :
    Tendsto (fun N => blockNodes (blockOf N)) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M => ⟨((M ^ 2) ^ 2) ^ 2, fun N hN => ?_⟩
  have h1 : (M ^ 2) ^ 2 ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt]
    calc (M ^ 2) ^ 2 * (M ^ 2) ^ 2 = ((M ^ 2) ^ 2) ^ 2 := (pow_two _).symm
      _ ≤ N := hN
  have h2 : M ^ 2 ≤ Nat.sqrt (Nat.sqrt N) := by
    rw [Nat.le_sqrt]
    calc M ^ 2 * M ^ 2 = (M ^ 2) ^ 2 := (pow_two _).symm
      _ ≤ Nat.sqrt N := h1
  have h3 : M ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt N)) := by
    rw [Nat.le_sqrt]
    calc M * M = M ^ 2 := (pow_two M).symm
      _ ≤ Nat.sqrt (Nat.sqrt N) := h2
  rw [blockNodes, blockOf]
  exact le_trans h3 (le_max_right 2 _)


/-! ## Estimate one: the partial block is negligible

At position `N` the current block contributes at most `offsetIn N ≤ 2·√N` terms out of `N + 1`.
Since blocks sit at `[k², (k+1)²)`, that ratio is `O(N^{-1/2})`. -/

theorem sqrt_cast_atTop : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp blockOf_atTop

/-- **The partial block vanishes** relative to everything before it. -/
theorem offsetIn_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (offsetIn N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun N : ℕ => (2 : ℝ) / (Nat.sqrt N : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds sqrt_cast_atTop
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hs1 : 1 ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]
      simpa using hN
    have hsR : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hs1
    have hnum : (offsetIn N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) := by
      have := offsetIn_le_two_mul_sqrt N
      exact_mod_cast this
    have hden : ((Nat.sqrt N : ℝ)) ^ 2 ≤ (N : ℝ) + 1 := by
      have h := Nat.sqrt_le' N
      have : ((Nat.sqrt N ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
    have hpos : (0 : ℝ) < ((Nat.sqrt N : ℝ)) ^ 2 := by positivity
    calc (offsetIn N : ℝ) / ((N : ℝ) + 1)
        ≤ (2 * (Nat.sqrt N : ℝ)) / ((Nat.sqrt N : ℝ)) ^ 2 := by
          gcongr
      _ = 2 / (Nat.sqrt N : ℝ) := by
          field_simp


/-! ## Estimate two: the partial cycle is negligible

One pass through block `k`'s nodes has length `∑ᵢ ⌊budget·wᵢ⌋ ≤ budget`, because the weights sum to
one.  So a partial cycle costs at most `blockBudget k = √k = N^{1/4}` positions out of `N`. -/

theorem blockTotal_le_budget (k : ℕ) : (blockTotal k : ℝ) ≤ blockBudget k := by
  have hn : 0 < blockNodes k := by have := two_le_blockNodes k; omega
  have hw := stWeight_sum (n := blockNodes k) hn
  have hbn : (0 : ℝ) ≤ blockBudget k := by rw [blockBudget]; positivity
  rw [blockTotal, runStart_eq_sum]
  push_cast
  calc (∑ i ∈ Finset.range (blockNodes k), (blockMult k i : ℝ))
      ≤ ∑ i ∈ Finset.range (blockNodes k), blockBudget k * stWeight (blockNodes k) i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiN : i < blockNodes k := Finset.mem_range.mp hi
        have hwnn : 0 ≤ stWeight (blockNodes k) i := by
          rw [stWeight]
          exact div_nonneg (stMass_pos hiN).le (stTotal_pos hn).le
        have hx : (0:ℝ) ≤ blockBudget k * stWeight (blockNodes k) i :=
          mul_nonneg hbn hwnn
        have hnn : (0:ℤ) ≤ ⌊blockBudget k * stWeight (blockNodes k) i⌋ :=
          Int.floor_nonneg.mpr hx
        rw [blockMult]
        have hcast : (((⌊blockBudget k * stWeight (blockNodes k) i⌋).toNat : ℕ) : ℝ)
            = ((⌊blockBudget k * stWeight (blockNodes k) i⌋ : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hnn
        rw [hcast]
        exact Int.floor_le _
    _ = blockBudget k := by rw [← Finset.mul_sum, hw, mul_one]

/-- **The partial cycle vanishes.** -/
theorem blockTotal_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (blockTotal (blockOf N) : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun N : ℕ => (1 : ℝ) / (Nat.sqrt N : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds sqrt_cast_atTop
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with N
    have : (0 : ℝ) ≤ (blockTotal (blockOf N) : ℝ) := Nat.cast_nonneg _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hs1 : 1 ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]; simpa using hN
    have hsR : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hs1
    have hb : (blockTotal (blockOf N) : ℝ) ≤ (Nat.sqrt N : ℝ) := by
      refine le_trans (blockTotal_le_budget _) ?_
      rw [blockBudget, blockOf]
      exact_mod_cast Nat.sqrt_le_self (Nat.sqrt N)
    have hden : ((Nat.sqrt N : ℝ)) ^ 2 ≤ (N : ℝ) + 1 := by
      have h := Nat.sqrt_le' N
      have hc : ((Nat.sqrt N ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
      push_cast at hc
      linarith
    calc (blockTotal (blockOf N) : ℝ) / ((N : ℝ) + 1)
        ≤ (Nat.sqrt N : ℝ) / ((Nat.sqrt N : ℝ)) ^ 2 := by gcongr
      _ = 1 / (Nat.sqrt N : ℝ) := by field_simp


/-! ## Estimate three: the within-cycle error

`satoTate_block_bound` bounds one cycle's `U_r`-average by `n(r+1)/(L − n)` with `n = blockNodes k`
and `L = blockBudget k`.  Since `blockNodes k = k^{1/4}` and `blockBudget k = k^{1/2}`, that is
`≈ (r+1)·k^{-1/4}`.  This is the scale gap `nodes ≪ budget` doing its work. -/

theorem sqrtsqrt_cast_atTop :
    Tendsto (fun k : ℕ => ((Nat.sqrt (Nat.sqrt k) : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (blockOf_atTop.comp blockOf_atTop)

theorem blockNodes_eq_of_le {k : ℕ} (hk : 16 ≤ k) :
    blockNodes k = Nat.sqrt (Nat.sqrt k) := by
  have h4 : 4 ≤ Nat.sqrt k := by
    rw [Nat.le_sqrt]; omega
  have h2 : 2 ≤ Nat.sqrt (Nat.sqrt k) := by
    rw [Nat.le_sqrt]; omega
  rw [blockNodes, max_eq_right h2]


theorem blockBudget_sub_pos {k : ℕ} (hk : 16 ≤ k) :
    (0:ℝ) < blockBudget k - blockNodes k := by
  have h2 : 2 ≤ Nat.sqrt (Nat.sqrt k) := by rw [Nat.le_sqrt]; rw [Nat.le_sqrt] at *; omega
  have hnodes : blockNodes k = Nat.sqrt (Nat.sqrt k) := blockNodes_eq_of_le hk
  have hsq : (Nat.sqrt (Nat.sqrt k)) ^ 2 ≤ Nat.sqrt k := Nat.sqrt_le' (Nat.sqrt k)
  have hR : ((Nat.sqrt (Nat.sqrt k) ^ 2 : ℕ) : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ) := by
    exact_mod_cast hsq
  have h2R : (2:ℝ) ≤ ((Nat.sqrt (Nat.sqrt k) : ℕ) : ℝ) := by exact_mod_cast h2
  rw [blockBudget, hnodes]
  push_cast at hR ⊢
  nlinarith [hR, h2R]

/-- **The within-cycle error vanishes**, at every rank. -/
theorem blockError_tendsto_zero (r : ℕ) :
    Tendsto (fun k : ℕ => (blockNodes k : ℝ) * ((r : ℝ) + 1) /
      (blockBudget k - blockNodes k)) atTop (𝓝 0) := by
  have hs : Tendsto (fun k : ℕ => ((Nat.sqrt (Nat.sqrt k) : ℕ) : ℝ) - 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ (-1) sqrtsqrt_cast_atTop
  have hmaj : Tendsto (fun k : ℕ => ((r : ℝ) + 1) /
      (((Nat.sqrt (Nat.sqrt k) : ℕ) : ℝ) - 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hs
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 16] with k hk
    have hb := blockBudget_sub_pos hk
    have : (0:ℝ) ≤ (blockNodes k : ℝ) * ((r : ℝ) + 1) := by positivity
    exact div_nonneg this hb.le
  · filter_upwards [eventually_ge_atTop 16] with k hk
    have hb := blockBudget_sub_pos hk
    have hnodes : (blockNodes k : ℝ) = ((Nat.sqrt (Nat.sqrt k) : ℕ) : ℝ) := by
      rw [blockNodes_eq_of_le hk]
    have h2 : 2 ≤ Nat.sqrt (Nat.sqrt k) := by rw [Nat.le_sqrt]; rw [Nat.le_sqrt] at *; omega
    have hn2 : (2:ℝ) ≤ (blockNodes k : ℝ) := by rw [hnodes]; exact_mod_cast h2
    have hden : (blockNodes k : ℝ) * ((blockNodes k : ℝ) - 1)
        ≤ blockBudget k - blockNodes k := by
      have hsq : (Nat.sqrt (Nat.sqrt k)) ^ 2 ≤ Nat.sqrt k := Nat.sqrt_le' (Nat.sqrt k)
      have hR : ((Nat.sqrt (Nat.sqrt k) ^ 2 : ℕ) : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ) := by
        exact_mod_cast hsq
      push_cast at hR
      rw [blockBudget, hnodes]
      nlinarith [hR, hn2, hnodes]
    calc (blockNodes k : ℝ) * ((r : ℝ) + 1) / (blockBudget k - blockNodes k)
        ≤ (blockNodes k : ℝ) * ((r : ℝ) + 1) /
            ((blockNodes k : ℝ) * ((blockNodes k : ℝ) - 1)) := by
          gcongr
          nlinarith [hn2]
      _ = ((r : ℝ) + 1) / ((blockNodes k : ℝ) - 1) := by
          have hne : (blockNodes k : ℝ) ≠ 0 := by linarith
          have hne1 : (blockNodes k : ℝ) - 1 ≠ 0 := by linarith
          field_simp
      _ = ((r : ℝ) + 1) / (((Nat.sqrt (Nat.sqrt k) : ℕ) : ℝ) - 1) := by rw [hnodes]


/-! ## The sum over one block

On block `j` the angle depends only on the offset, cycling with period `blockTotal j`.  So the sum
over the block's positions reindexes to a sum over `range (2j+1)` of the cycled node angles — the
form `sum_range_mod` consumes. -/

theorem witnessAngle_block {j N : ℕ} (h1 : j ^ 2 ≤ N) (h2 : N < (j + 1) ^ 2)
    (hT : blockTotal j ≠ 0) :
    witnessAngle N = stAngle (blockNodes j)
      (runIndex (blockMult j) (blockNodes j) ((N - j ^ 2) % blockTotal j)) := by
  rw [witnessAngle, blockOf_eq h1 h2, if_neg hT, offsetIn_eq h1 h2]

/-- **One block, reindexed.** -/
theorem block_sum_eq (j : ℕ) (hT : blockTotal j ≠ 0) (f : ℝ → ℝ) :
    ∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2), f (witnessAngle N)
      = ∑ t ∈ Finset.range (2 * j + 1),
          f (stAngle (blockNodes j)
            (runIndex (blockMult j) (blockNodes j) (t % blockTotal j))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hcard : (j + 1) ^ 2 - j ^ 2 = 2 * j + 1 := by
    have : (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
    omega
  rw [hcard]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htlt : t < 2 * j + 1 := Finset.mem_range.mp ht
  have hA : j ^ 2 ≤ j ^ 2 + t := Nat.le_add_right _ _
  have hB : j ^ 2 + t < (j + 1) ^ 2 := by
    have : (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
    omega
  rw [witnessAngle_block hA hB hT]
  have hsub : j ^ 2 + t - j ^ 2 = t := by omega
  rw [hsub]

/-- **One cycle** is the multiplicity-weighted node sum — exactly the object
`satoTate_block_bound` controls. -/
theorem cycle_sum_eq (j : ℕ) (f : ℝ → ℝ) :
    ∑ t ∈ Finset.range (blockTotal j),
        f (stAngle (blockNodes j) (runIndex (blockMult j) (blockNodes j) t))
      = ∑ i ∈ Finset.range (blockNodes j),
          (blockMult j i : ℝ) * f (stAngle (blockNodes j) i) := by
  rw [blockTotal]
  exact sum_runIndex (blockMult j) (fun i => f (stAngle (blockNodes j) i)) (blockNodes j)


/-! ## Bridging the multiplicity casts

`blockMult` is `ℕ`-valued (it counts positions); `satoTate_block_bound` is stated with the `ℤ`
floor.  They agree because the weights are nonnegative, and these two lemmas record that so the
block bound can be applied to the sequence. -/

theorem stWeight_nonneg {n i : ℕ} (hi : i < n) : 0 ≤ stWeight n i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hi
  rw [stWeight]
  exact div_nonneg (stMass_pos hi).le (stTotal_pos hn).le

theorem blockMult_cast {j i : ℕ} (hi : i < blockNodes j) :
    ((blockMult j i : ℕ) : ℝ)
      = ((⌊blockBudget j * stWeight (blockNodes j) i⌋ : ℤ) : ℝ) := by
  have hbn : (0 : ℝ) ≤ blockBudget j := by rw [blockBudget]; positivity
  have hx : (0:ℝ) ≤ blockBudget j * stWeight (blockNodes j) i :=
    mul_nonneg hbn (stWeight_nonneg hi)
  have hnn : (0:ℤ) ≤ ⌊blockBudget j * stWeight (blockNodes j) i⌋ := Int.floor_nonneg.mpr hx
  rw [blockMult]
  exact_mod_cast Int.toNat_of_nonneg hnn

theorem blockTotal_cast (j : ℕ) :
    ((blockTotal j : ℕ) : ℝ)
      = ∑ i : Fin (blockNodes j),
          ((⌊blockBudget j * stWeight (blockNodes j) (i : ℕ)⌋ : ℤ) : ℝ) := by
  rw [blockTotal, runStart_eq_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ((⌊blockBudget j * stWeight (blockNodes j) i⌋ : ℤ) : ℝ)) (blockNodes j)]
  push_cast
  exact Finset.sum_congr rfl fun i hi => blockMult_cast (Finset.mem_range.mp hi)

/-- The cycle sum, in the shape `satoTate_block_bound` states. -/
theorem cycle_sum_cast (j r : ℕ) :
    ∑ i ∈ Finset.range (blockNodes j),
        (blockMult j i : ℝ) *
          (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (stAngle (blockNodes j) i))
      = ∑ i : Fin (blockNodes j),
          ((⌊blockBudget j * stWeight (blockNodes j) (i : ℕ)⌋ : ℤ) : ℝ) *
            (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (stNode (blockNodes j) (i : ℕ)) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ((⌊blockBudget j * stWeight (blockNodes j) i⌋ : ℤ) : ℝ) *
      (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (stNode (blockNodes j) i)) (blockNodes j)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [blockMult_cast (Finset.mem_range.mp hi), stNode]


/-! ## The per-block bound

Whole cycles contribute the exactly-controlled node sum; the remainder is bounded by the trivial
`|U_r| ≤ r+1`.  Together: block `j` contributes at most `(2j+1)·ε_j + blockTotal j·(r+1)`. -/

theorem cycle_remainder_bound (j r M : ℕ) :
    |∑ t ∈ Finset.range M,
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (stAngle (blockNodes j)
          (runIndex (blockMult j) (blockNodes j) t)))| ≤ (M : ℝ) * ((r : ℝ) + 1) := by
  calc |∑ t ∈ Finset.range M, (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval
        (Real.cos (stAngle (blockNodes j) (runIndex (blockMult j) (blockNodes j) t)))|
      ≤ ∑ t ∈ Finset.range M, |(Polynomial.Chebyshev.U ℝ (r : ℤ)).eval
          (Real.cos (stAngle (blockNodes j)
            (runIndex (blockMult j) (blockNodes j) t)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range M, ((r : ℝ) + 1) :=
        Finset.sum_le_sum fun t _ => abs_chebyshevU_cos_le r _
    _ = (M : ℝ) * ((r : ℝ) + 1) := by simp; ring

/-- The whole-cycle sum is small: `|C| ≤ blockTotal j · ε_j`. -/
theorem cycle_sum_abs_le {j r : ℕ} (hr : 1 ≤ r) (hn : 0 < blockNodes j)
    (hdeg : ((Polynomial.Chebyshev.U ℝ (r : ℤ)) * (1 - Polynomial.X ^ 2)).degree
      < 2 * ((blockNodes j : ℕ) : WithBot ℕ))
    (hL : ((blockNodes j : ℕ) : ℝ) < blockBudget j) :
    |∑ t ∈ Finset.range (blockTotal j),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (stAngle (blockNodes j)
          (runIndex (blockMult j) (blockNodes j) t)))|
      ≤ (blockTotal j : ℝ) *
          (((blockNodes j : ℕ) : ℝ) * ((r : ℝ) + 1) /
            (blockBudget j - ((blockNodes j : ℕ) : ℝ))) := by
  rcases Nat.eq_zero_or_pos (blockTotal j) with hz | hpos
  · rw [hz]
    simp
  · have hb := satoTate_block_bound hn hr hdeg hL
    rw [cycle_sum_eq j (fun θ => (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos θ)),
      cycle_sum_cast j r]
    rw [← blockTotal_cast j] at hb
    have hTR : (0:ℝ) < (blockTotal j : ℝ) := by exact_mod_cast hpos
    rw [div_le_iff₀ hTR] at hb
    calc |∑ i : Fin (blockNodes j),
          ((⌊blockBudget j * stWeight (blockNodes j) (i : ℕ)⌋ : ℤ) : ℝ) *
            (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (stNode (blockNodes j) (i : ℕ))|
        ≤ ((blockNodes j : ℕ) : ℝ) * ((r : ℝ) + 1) /
            (blockBudget j - ((blockNodes j : ℕ) : ℝ)) * (blockTotal j : ℝ) := hb
      _ = (blockTotal j : ℝ) * (((blockNodes j : ℕ) : ℝ) * ((r : ℝ) + 1) /
            (blockBudget j - ((blockNodes j : ℕ) : ℝ))) := by ring


/-- **The per-block bound.**  Block `j` contributes at most `(2j+1)·ε_j + blockTotal j·(r+1)`:
whole cycles carry the exactly-controlled node sum, the remainder is bounded trivially. -/
theorem block_sum_bound {j r : ℕ} (hr : 1 ≤ r) (hn : 0 < blockNodes j)
    (hT : blockTotal j ≠ 0)
    (hdeg : ((Polynomial.Chebyshev.U ℝ (r : ℤ)) * (1 - Polynomial.X ^ 2)).degree
      < 2 * ((blockNodes j : ℕ) : WithBot ℕ))
    (hL : ((blockNodes j : ℕ) : ℝ) < blockBudget j) :
    |∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))|
      ≤ (2 * (j : ℝ) + 1) *
          (((blockNodes j : ℕ) : ℝ) * ((r : ℝ) + 1) /
            (blockBudget j - ((blockNodes j : ℕ) : ℝ)))
        + (blockTotal j : ℝ) * ((r : ℝ) + 1) := by
  set T := blockTotal j with hTdef
  set ε : ℝ := ((blockNodes j : ℕ) : ℝ) * ((r : ℝ) + 1) /
    (blockBudget j - ((blockNodes j : ℕ) : ℝ)) with hε
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT
  have hTR : (0:ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hεnn : 0 ≤ ε := by
    rw [hε]
    have : (0:ℝ) < blockBudget j - ((blockNodes j : ℕ) : ℝ) := by linarith
    positivity
  set h : ℕ → ℝ := fun t =>
    (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (stAngle (blockNodes j)
      (runIndex (blockMult j) (blockNodes j) t))) with hh
  rw [block_sum_eq j hT (fun θ => (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos θ))]
  rw [sum_range_mod h hTpos (2 * j + 1)]
  have hC : |∑ t ∈ Finset.range T, h t| ≤ (T : ℝ) * ε :=
    cycle_sum_abs_le hr hn hdeg hL
  have hR : |∑ t ∈ Finset.range ((2 * j + 1) % T), h t|
      ≤ (((2 * j + 1) % T : ℕ) : ℝ) * ((r : ℝ) + 1) := cycle_remainder_bound j r _
  have hA : (((2 * j + 1) / T : ℕ) : ℝ) ≤ (2 * (j : ℝ) + 1) / (T : ℝ) := by
    have := Nat.cast_div_le (α := ℝ) (m := 2 * j + 1) (n := T)
    push_cast at this ⊢
    linarith
  have hAnn : (0:ℝ) ≤ (((2 * j + 1) / T : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmod : (((2 * j + 1) % T : ℕ) : ℝ) ≤ (T : ℝ) := by
    have := Nat.mod_lt (2 * j + 1) hTpos
    exact_mod_cast this.le
  calc |(((2 * j + 1) / T : ℕ) : ℝ) * (∑ t ∈ Finset.range T, h t)
        + ∑ t ∈ Finset.range ((2 * j + 1) % T), h t|
      ≤ |(((2 * j + 1) / T : ℕ) : ℝ) * (∑ t ∈ Finset.range T, h t)|
        + |∑ t ∈ Finset.range ((2 * j + 1) % T), h t| := abs_add_le _ _
    _ ≤ (2 * (j : ℝ) + 1) * ε + (T : ℝ) * ((r : ℝ) + 1) := by
        rw [abs_mul, abs_of_nonneg hAnn]
        have h1 : (((2 * j + 1) / T : ℕ) : ℝ) * |∑ t ∈ Finset.range T, h t|
            ≤ (2 * (j : ℝ) + 1) * ε := by
          calc (((2 * j + 1) / T : ℕ) : ℝ) * |∑ t ∈ Finset.range T, h t|
              ≤ ((2 * (j : ℝ) + 1) / (T : ℝ)) * ((T : ℝ) * ε) := by
                refine mul_le_mul hA hC (abs_nonneg _) (by positivity)
            _ = (2 * (j : ℝ) + 1) * ε := by field_simp
        have h2 : |∑ t ∈ Finset.range ((2 * j + 1) % T), h t| ≤ (T : ℝ) * ((r : ℝ) + 1) := by
          refine le_trans hR ?_
          exact mul_le_mul_of_nonneg_right hmod (by positivity)
        linarith


/-! ## Blocks are non-degenerate

`blockTotal j ≠ 0` is needed to cycle at all.  It holds once the budget exceeds the node count:
the weights sum to one over `blockNodes j` nodes, so some weight is at least `1/blockNodes j`, and
`budget/nodes ≥ 1` makes that node's multiplicity at least one. -/

theorem exists_large_weight {n : ℕ} (hn : 0 < n) :
    ∃ i ∈ Finset.range n, (1:ℝ) / (n : ℝ) ≤ stWeight n i := by
  by_contra hc
  push_neg at hc
  have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.mpr hn⟩
  have hlt : ∑ i ∈ Finset.range n, stWeight n i
      < ∑ _i ∈ Finset.range n, (1:ℝ) / (n : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hne fun i hi => hc i hi
  rw [stWeight_sum hn, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hnR : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [mul_one_div, div_self hnR.ne'] at hlt
  exact lt_irrefl 1 hlt

theorem blockTotal_ne_zero {j : ℕ} (hj : 16 ≤ j) : blockTotal j ≠ 0 := by
  have hn : 0 < blockNodes j := by have := two_le_blockNodes j; omega
  have hnR : (0:ℝ) < ((blockNodes j : ℕ) : ℝ) := Nat.cast_pos.mpr hn
  have hbudget : ((blockNodes j : ℕ) : ℝ) ≤ blockBudget j := by
    have := blockBudget_sub_pos hj; linarith
  obtain ⟨i, hi, hw⟩ := exists_large_weight hn
  have hiN : i < blockNodes j := Finset.mem_range.mp hi
  have hx : (1:ℝ) ≤ blockBudget j * stWeight (blockNodes j) i := by
    calc (1:ℝ) = ((blockNodes j : ℕ) : ℝ) * (1 / ((blockNodes j : ℕ) : ℝ)) := by
          field_simp
      _ ≤ blockBudget j * stWeight (blockNodes j) i := by
          refine mul_le_mul hbudget hw (by positivity) (by linarith)
  have hfloor : (1:ℤ) ≤ ⌊blockBudget j * stWeight (blockNodes j) i⌋ :=
    Int.le_floor.mpr (by exact_mod_cast hx)
  have hmult : 1 ≤ blockMult j i := by
    rw [blockMult]
    omega
  have hle : blockMult j i ≤ blockTotal j := by
    rw [blockTotal, runStart_eq_sum]
    exact Finset.single_le_sum (f := blockMult j) (fun _ _ => Nat.zero_le _) hi
  omega


/-! ## The cycle-remainder terms, summed over blocks

Each block contributes a remainder of at most `blockTotal j ≤ √j` positions.  Summed over `j < k`
that is at most `k√k`, which against the running total `k²` is `k^{-1/2}`. -/

theorem blockTotal_sum_ratio_tendsto_zero :
    Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, (blockTotal j : ℝ)) / ((k : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hmaj : Tendsto (fun k : ℕ => (1 : ℝ) / (Nat.sqrt k : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds sqrt_cast_atTop
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with k
    have hs : (0:ℝ) ≤ ∑ j ∈ Finset.range k, (blockTotal j : ℝ) :=
      Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hs1 : 1 ≤ Nat.sqrt k := by rw [Nat.le_sqrt]; simpa using hk
    have hsR : (1:ℝ) ≤ (Nat.sqrt k : ℝ) := by exact_mod_cast hs1
    have hbound : ∑ j ∈ Finset.range k, (blockTotal j : ℝ)
        ≤ (k : ℝ) * (Nat.sqrt k : ℝ) := by
      calc ∑ j ∈ Finset.range k, (blockTotal j : ℝ)
          ≤ ∑ _j ∈ Finset.range k, (Nat.sqrt k : ℝ) := by
            refine Finset.sum_le_sum fun j hj => ?_
            refine le_trans (blockTotal_le_budget j) ?_
            rw [blockBudget]
            exact_mod_cast Nat.sqrt_le_sqrt (le_of_lt (Finset.mem_range.mp hj))
        _ = (k : ℝ) * (Nat.sqrt k : ℝ) := by simp
    have hden : ((Nat.sqrt k : ℝ)) ^ 2 ≤ (k : ℝ) := by
      have h := Nat.sqrt_le' k
      exact_mod_cast h
    calc (∑ j ∈ Finset.range k, (blockTotal j : ℝ)) / ((k : ℝ) ^ 2)
        ≤ ((k : ℝ) * (Nat.sqrt k : ℝ)) / ((k : ℝ) ^ 2) := by gcongr
      _ = (Nat.sqrt k : ℝ) / (k : ℝ) := by field_simp
      _ ≤ (Nat.sqrt k : ℝ) / ((Nat.sqrt k : ℝ)) ^ 2 := by
          gcongr
      _ = 1 / (Nat.sqrt k : ℝ) := by field_simp


/-! ## The summed block bound

Packaging the per-block bound's two terms and sending the total to zero.  The error is clipped at
zero so that `linear_weighted_cesaro` applies at every index, including the small blocks where the
budget has not yet overtaken the node count. -/

/-- The per-block error, clipped at zero. -/
noncomputable def blockErr (j r : ℕ) : ℝ :=
  max 0 (((blockNodes j : ℕ) : ℝ) * ((r : ℝ) + 1) /
    (blockBudget j - ((blockNodes j : ℕ) : ℝ)))

theorem blockErr_nonneg (j r : ℕ) : 0 ≤ blockErr j r := le_max_left _ _

theorem blockErr_tendsto_zero (r : ℕ) : Tendsto (fun j => blockErr j r) atTop (𝓝 0) := by
  have h := blockError_tendsto_zero r
  have hc : Continuous fun x : ℝ => max 0 x := continuous_const.max continuous_id
  have := (hc.tendsto 0).comp h
  simpa [blockErr, Function.comp_def] using this

/-- **The summed block bound vanishes.** -/
theorem blockBound_sum_tendsto_zero (r : ℕ) :
    Tendsto (fun k : ℕ =>
      (∑ j ∈ Finset.range k,
        ((2 * (j : ℝ) + 1) * blockErr j r + (blockTotal j : ℝ) * ((r : ℝ) + 1)))
        / ((k : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hA : Tendsto (fun k : ℕ =>
      (∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) * blockErr j r) / ((k : ℝ) ^ 2))
      atTop (𝓝 0) :=
    linear_weighted_cesaro (fun j => blockErr_nonneg j r) (blockErr_tendsto_zero r)
  have hB : Tendsto (fun k : ℕ =>
      (∑ j ∈ Finset.range k, (blockTotal j : ℝ) * ((r : ℝ) + 1)) / ((k : ℝ) ^ 2))
      atTop (𝓝 0) := by
    have h := (blockTotal_sum_ratio_tendsto_zero).mul_const ((r : ℝ) + 1)
    simp only [zero_mul] at h
    refine h.congr fun k => ?_
    rw [← Finset.sum_mul]
    ring
  have := hA.add hB
  simp only [add_zero] at this
  refine this.congr fun k => ?_
  rw [← add_div, ← Finset.sum_add_distrib]


/-! ## The per-block bound, with side conditions discharged

`block_sum_bound` has four hypotheses.  All hold for large `j`: the node count grows, so the degree
condition is eventually met; `j ≥ 16` gives the rest. -/

theorem blockNodes_atTop : Tendsto blockNodes atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M => ⟨(M ^ 2) ^ 2, fun j hj => ?_⟩
  have h1 : M ^ 2 ≤ Nat.sqrt j := by
    rw [Nat.le_sqrt]
    calc M ^ 2 * M ^ 2 = (M ^ 2) ^ 2 := (pow_two _).symm
      _ ≤ j := hj
  have h2 : M ≤ Nat.sqrt (Nat.sqrt j) := by
    rw [Nat.le_sqrt]
    calc M * M = M ^ 2 := (pow_two M).symm
      _ ≤ Nat.sqrt j := h1
  exact le_trans h2 (le_max_right 2 _)

/-- The trivial bound on a block: `2j+1` terms of size at most `r+1`. -/
theorem block_sum_trivial_bound (j r : ℕ) :
    |∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))|
      ≤ (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) := by
  calc |∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))|
      ≤ ∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
          |(Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2), ((r : ℝ) + 1) :=
        Finset.sum_le_sum fun N _ => abs_chebyshevU_cos_le r _
    _ = (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) := by
        rw [Finset.sum_const, block_card j, nsmul_eq_mul]
        push_cast
        ring

/-- **Eventually, every block obeys the sharp bound.** -/
theorem block_sum_le_bound (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ j : ℕ in atTop,
      |∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
          (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))|
        ≤ (2 * (j : ℝ) + 1) * blockErr j r + (blockTotal j : ℝ) * ((r : ℝ) + 1) := by
  have hdeg : ∀ᶠ j : ℕ in atTop, r + 2 < 2 * blockNodes j := by
    have := blockNodes_atTop.eventually_gt_atTop (r + 2)
    filter_upwards [this] with j hj
    omega
  filter_upwards [hdeg, eventually_ge_atTop 16] with j hjdeg hj16
  have hn : 0 < blockNodes j := by have := two_le_blockNodes j; omega
  have hL : ((blockNodes j : ℕ) : ℝ) < blockBudget j := by
    have := blockBudget_sub_pos hj16; linarith
  have hb := block_sum_bound hr hn (blockTotal_ne_zero hj16)
    (degree_U_mul_one_sub_sq hjdeg) hL
  refine le_trans hb ?_
  have hle : ((blockNodes j : ℕ) : ℝ) * ((r : ℝ) + 1) /
      (blockBudget j - ((blockNodes j : ℕ) : ℝ)) ≤ blockErr j r := le_max_right _ _
  have : (0:ℝ) ≤ 2 * (j : ℝ) + 1 := by positivity
  nlinarith [hle, this]


/-! ## Convergence along the block boundaries

At `N = k²` the sum is exactly the first `k` block sums, so the per-block bound and its summed
limit give the result directly. -/

theorem sq_cast_atTop : Tendsto (fun k : ℕ => ((k : ℝ)) ^ 2) atTop atTop :=
  (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop

/-- **The witness cancels, along block boundaries.** -/
theorem witness_cancellation_sq (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun k : ℕ =>
      (∑ i ∈ Finset.range (k ^ 2),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle i))) / ((k : ℝ) ^ 2))
      atTop (𝓝 0) := by
  obtain ⟨J, hJ⟩ := (block_sum_le_bound r hr).exists_forall_of_atTop
  set C : ℝ := ∑ j ∈ Finset.range J, (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) with hC
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun j _ => by positivity
  -- each block obeys `Bd j` plus a head correction
  have hstep : ∀ j : ℕ,
      |∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
          (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))|
        ≤ ((2 * (j : ℝ) + 1) * blockErr j r + (blockTotal j : ℝ) * ((r : ℝ) + 1))
          + (if j < J then (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) else 0) := by
    intro j
    rcases Nat.lt_or_ge j J with hj | hj
    · rw [if_pos hj]
      have h1 := block_sum_trivial_bound j r
      have h2 : (0:ℝ) ≤ (2 * (j : ℝ) + 1) * blockErr j r :=
        mul_nonneg (by positivity) (blockErr_nonneg j r)
      have h3 : (0:ℝ) ≤ (blockTotal j : ℝ) * ((r : ℝ) + 1) := by positivity
      linarith
    · rw [if_neg (by omega)]
      have := hJ j hj
      linarith
  -- the head correction is bounded by `C`
  have hhead : ∀ k : ℕ,
      ∑ j ∈ Finset.range k, (if j < J then (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) else 0) ≤ C := by
    intro k
    calc ∑ j ∈ Finset.range k, (if j < J then (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) else 0)
        = ∑ j ∈ (Finset.range k).filter (fun j => j < J), (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) := by
          rw [Finset.sum_filter]
      _ ≤ C := by
          rw [hC]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
          exact hj.2
  -- majorant
  have hmaj : Tendsto (fun k : ℕ =>
      (∑ j ∈ Finset.range k,
        ((2 * (j : ℝ) + 1) * blockErr j r + (blockTotal j : ℝ) * ((r : ℝ) + 1)))
        / ((k : ℝ) ^ 2) + C / ((k : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h1 := blockBound_sum_tendsto_zero r
    have h2 : Tendsto (fun k : ℕ => C / ((k : ℝ) ^ 2)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds sq_cast_atTop
    simpa using h1.add h2
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkR : (0:ℝ) < ((k : ℝ)) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hkR, ← add_div]
  gcongr
  calc |∑ i ∈ Finset.range (k ^ 2),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle i))|
      = |∑ j ∈ Finset.range k, ∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
          (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))| := by
        rw [sum_range_sq_eq]
    _ ≤ ∑ j ∈ Finset.range k, |∑ N ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2),
          (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle N))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k,
          (((2 * (j : ℝ) + 1) * blockErr j r + (blockTotal j : ℝ) * ((r : ℝ) + 1))
            + (if j < J then (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) else 0)) :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = (∑ j ∈ Finset.range k,
          ((2 * (j : ℝ) + 1) * blockErr j r + (blockTotal j : ℝ) * ((r : ℝ) + 1)))
        + ∑ j ∈ Finset.range k, (if j < J then (2 * (j : ℝ) + 1) * ((r : ℝ) + 1) else 0) :=
        Finset.sum_add_distrib
    _ ≤ (∑ j ∈ Finset.range k,
          ((2 * (j : ℝ) + 1) * blockErr j r + (blockTotal j : ℝ) * ((r : ℝ) + 1))) + C := by
        linarith [hhead k]


/-! ## Convergence at every index

A general index `n` sits at offset `offsetIn n` inside block `blockOf n`.  Splitting off the
completed blocks reduces to `witness_cancellation_sq`, and the leftover partial block is
`offsetIn_ratio_tendsto_zero`. -/

/-- **The witness cancels at every rank.** -/
theorem witness_cancellation (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range (n + 1),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle i))) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun i =>
    (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle i)) with hf
  have hsq : Tendsto (fun k : ℕ =>
      |∑ i ∈ Finset.range (k ^ 2), f i| / ((k : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h := witness_cancellation_sq r hr
    rw [tendsto_zero_iff_norm_tendsto_zero] at h
    refine h.congr fun k => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k:ℝ))^2)]
  have hcomp : Tendsto (fun n : ℕ =>
      |∑ i ∈ Finset.range ((blockOf n) ^ 2), f i| / (((blockOf n) : ℝ) ^ 2))
      atTop (𝓝 0) := hsq.comp blockOf_atTop
  have htail : Tendsto (fun n : ℕ =>
      (((offsetIn n : ℕ) : ℝ) + 1) * ((r : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 := offsetIn_ratio_tendsto_zero
    have h2 : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h3 := (h1.add h2).mul_const ((r : ℝ) + 1)
    simp only [zero_add, zero_mul] at h3
    refine h3.congr fun n => ?_
    field_simp
  have hmaj := hcomp.add htail
  simp only [add_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with n hn
  set k := blockOf n with hk
  have hk2 : k ^ 2 ≤ n := blockOf_sq_le n
  have hkpos : 0 < k := by
    rw [hk, blockOf, Nat.lt_iff_add_one_le, Nat.le_sqrt]
    simpa using hn
  have hkR : (0:ℝ) < ((k : ℝ)) ^ 2 := by
    have : (0:ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    positivity
  have hnR : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hsplit : ∑ i ∈ Finset.range (n + 1), f i
      = (∑ i ∈ Finset.range (k ^ 2), f i) + ∑ i ∈ Finset.Ico (k ^ 2) (n + 1), f i := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega : k ^ 2 ≤ n + 1)]
  have hcard : ((Finset.Ico (k ^ 2) (n + 1)).card : ℝ) = ((offsetIn n : ℕ) : ℝ) + 1 := by
    rw [Nat.card_Ico, offsetIn, ← hk]
    have : n + 1 - k ^ 2 = (n - k ^ 2) + 1 := by omega
    rw [this]
    push_cast
    ring
  have htailbd : |∑ i ∈ Finset.Ico (k ^ 2) (n + 1), f i|
      ≤ (((offsetIn n : ℕ) : ℝ) + 1) * ((r : ℝ) + 1) := by
    calc |∑ i ∈ Finset.Ico (k ^ 2) (n + 1), f i|
        ≤ ∑ i ∈ Finset.Ico (k ^ 2) (n + 1), |f i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Ico (k ^ 2) (n + 1), ((r : ℝ) + 1) :=
          Finset.sum_le_sum fun i _ => abs_chebyshevU_cos_le r _
      _ = (((offsetIn n : ℕ) : ℝ) + 1) * ((r : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [Real.norm_eq_abs, hsplit, abs_div]
  rw [abs_of_pos hnR]
  have hk2R : ((k : ℝ)) ^ 2 ≤ (n : ℝ) + 1 := by
    have : ((k ^ 2 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hk2
    push_cast at this
    linarith
  calc |(∑ i ∈ Finset.range (k ^ 2), f i) + ∑ i ∈ Finset.Ico (k ^ 2) (n + 1), f i| / ((n : ℝ) + 1)
      ≤ (|∑ i ∈ Finset.range (k ^ 2), f i|
          + |∑ i ∈ Finset.Ico (k ^ 2) (n + 1), f i|) / ((n : ℝ) + 1) := by
        gcongr
        exact abs_add_le _ _
    _ ≤ |∑ i ∈ Finset.range (k ^ 2), f i| / ((k : ℝ) ^ 2)
        + (((offsetIn n : ℕ) : ℝ) + 1) * ((r : ℝ) + 1) / ((n : ℝ) + 1) := by
        rw [add_div]
        gcongr

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.witnessAngle_mem
#print axioms CriticalLinePhasor.ThreeDConverse.blockNodes_blockOf_atTop
#print axioms CriticalLinePhasor.ThreeDConverse.offsetIn_ratio_tendsto_zero
#print axioms CriticalLinePhasor.ThreeDConverse.blockTotal_ratio_tendsto_zero
#print axioms CriticalLinePhasor.ThreeDConverse.blockError_tendsto_zero
#print axioms CriticalLinePhasor.ThreeDConverse.block_sum_eq
#print axioms CriticalLinePhasor.ThreeDConverse.cycle_sum_eq
#print axioms CriticalLinePhasor.ThreeDConverse.blockTotal_cast
#print axioms CriticalLinePhasor.ThreeDConverse.cycle_sum_cast
#print axioms CriticalLinePhasor.ThreeDConverse.cycle_remainder_bound
#print axioms CriticalLinePhasor.ThreeDConverse.cycle_sum_abs_le
#print axioms CriticalLinePhasor.ThreeDConverse.block_sum_bound
#print axioms CriticalLinePhasor.ThreeDConverse.blockTotal_ne_zero
#print axioms CriticalLinePhasor.ThreeDConverse.blockTotal_sum_ratio_tendsto_zero
#print axioms CriticalLinePhasor.ThreeDConverse.blockBound_sum_tendsto_zero
#print axioms CriticalLinePhasor.ThreeDConverse.block_sum_le_bound
#print axioms CriticalLinePhasor.ThreeDConverse.witness_cancellation_sq
#print axioms CriticalLinePhasor.ThreeDConverse.witness_cancellation
