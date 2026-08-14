import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Run-length decoding: positions to node indices

The Sato--Tate block assigns node `i` a multiplicity `mᵢ = ⌊L·wᵢ⌋`.  Turning that into a *sequence*
needs the inverse map: given a position `t`, which node is it?  This file supplies that map and its
defining property, for an arbitrary multiplicity vector — it is pure combinatorics, with no
Sato--Tate content.

  **`runStart m i = m 0 + ⋯ + m (i−1)`**,  **`runIndex m t = #{i | runStart m (i+1) ≤ t}`**.

`runStart` is monotone, and `runIndex` is characterised by

  **`runStart m (runIndex m t) ≤ t < runStart m (runIndex m t + 1)`**

whenever `t` is below the total.  That is exactly the statement "position `t` lies in block `i`'s
run", and it is what lets a block of prescribed multiplicities be read as a sequence.

**Scope.**  Combinatorics only; no analytic content, and nothing here mentions Chebyshev or
Sato--Tate.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- Cumulative multiplicity: the position at which node `i`'s run begins. -/
def runStart (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (i + 1) => runStart m i + m i

@[simp] theorem runStart_zero (m : ℕ → ℕ) : runStart m 0 = 0 := rfl

theorem runStart_succ (m : ℕ → ℕ) (i : ℕ) :
    runStart m (i + 1) = runStart m i + m i := rfl

theorem runStart_mono (m : ℕ → ℕ) : Monotone (runStart m) := by
  intro a b hab
  induction b with
  | zero =>
    have h0 : a = 0 := Nat.le_zero.mp hab
    subst h0; exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge a (k + 1) with h | h
    · have hak : a ≤ k := Nat.lt_succ_iff.mp h
      exact le_trans (ih hak) (by rw [runStart_succ]; exact Nat.le_add_right _ _)
    · have heq : a = k + 1 := le_antisymm hab h
      subst heq; exact le_rfl

theorem runStart_eq_sum (m : ℕ → ℕ) : ∀ n : ℕ, runStart m n = ∑ i ∈ Finset.range n, m i := by
  intro n
  induction n with
  | zero => simp [runStart_zero]
  | succ k ih => rw [runStart_succ, ih, Finset.sum_range_succ]

/-- The node whose run contains position `t`. -/
noncomputable def runIndex (m : ℕ → ℕ) (n t : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i : ℕ => runStart m (i + 1) ≤ t)).card

theorem runIndex_le (m : ℕ → ℕ) (n t : ℕ) : runIndex m n t ≤ n := by
  rw [runIndex]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- Below the total, the index is a genuine node. -/
theorem runIndex_lt {m : ℕ → ℕ} {n t : ℕ} (ht : t < runStart m n) : runIndex m n t < n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [runStart_zero] at ht; omega
    · exact h
  rw [runIndex]
  have hnot : (n - 1) ∉ (Finset.range n).filter (fun i : ℕ => runStart m (i + 1) ≤ t) := by
    simp only [Finset.mem_filter, Finset.mem_range, not_and]
    intro _
    have hs : n - 1 + 1 = n := by omega
    rw [hs]
    omega
  have hsub : (Finset.range n).filter (fun i : ℕ => runStart m (i + 1) ≤ t)
      ⊂ Finset.range n := by
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hc
    exact hnot (hc (Finset.mem_range.mpr (by omega)))
  simpa using Finset.card_lt_card hsub

/-- **The defining property**: the run beginning at `runIndex` contains `t`. -/
theorem runStart_runIndex_le {m : ℕ → ℕ} {n t : ℕ} (ht : t < runStart m n) :
    runStart m (runIndex m n t) ≤ t := by
  -- the filter set is a downward-closed initial segment, so its card indexes the first miss
  have hkey : ∀ j : ℕ, j < runIndex m n t → runStart m (j + 1) ≤ t := by
    intro j hj
    by_contra hcon
    push_neg at hcon
    have hmono : ∀ i, j ≤ i → ¬ (runStart m (i + 1) ≤ t) := by
      intro i hi hle
      exact absurd (le_trans (runStart_mono m (by omega : j + 1 ≤ i + 1)) hle) (by omega)
    have hsub : ((Finset.range n).filter (fun i : ℕ => runStart m (i + 1) ≤ t))
        ⊆ Finset.range j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_range]
      by_contra hc
      exact hmono i (by omega) hi.2
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    rw [runIndex] at hj
    omega
  rcases Nat.eq_zero_or_pos (runIndex m n t) with h0 | hpos
  · rw [h0, runStart_zero]; omega
  · have := hkey (runIndex m n t - 1) (by omega)
    have heq : runIndex m n t - 1 + 1 = runIndex m n t := by omega
    rwa [heq] at this


/-! ## Positions to nodes, as a sum identity

The form the block construction consumes: summing a function of the *node* over all *positions*
reproduces the multiplicity-weighted sum over nodes.  This is what lets
`satoTate_block_bound` — stated in multiplicities — be read as a statement about a sequence. -/

theorem runIndex_of_lt {m : ℕ → ℕ} {n t : ℕ} (ht : t < runStart m n) :
    runIndex m (n + 1) t = runIndex m n t := by
  rw [runIndex, runIndex, Finset.range_add_one, Finset.filter_insert]
  have hno : ¬ (runStart m (n + 1) ≤ t) := by
    have hmono : runStart m n ≤ runStart m (n + 1) :=
      runStart_mono m (Nat.le_add_right n 1)
    omega
  rw [if_neg hno]

theorem runIndex_of_ge {m : ℕ → ℕ} {n t : ℕ} (h1 : runStart m n ≤ t)
    (h2 : t < runStart m (n + 1)) : runIndex m (n + 1) t = n := by
  rw [runIndex, Finset.range_add_one, Finset.filter_insert]
  have hno : ¬ (runStart m (n + 1) ≤ t) := by omega
  rw [if_neg hno]
  have hall : (Finset.range n).filter (fun i : ℕ => runStart m (i + 1) ≤ t)
      = Finset.range n := by
    refine Finset.filter_true_of_mem fun i hi => ?_
    simp only [Finset.mem_range] at hi
    exact le_trans (runStart_mono m (by omega : i + 1 ≤ n)) h1
  rw [hall, Finset.card_range]

/-- **Positions to nodes.**  Summing over the block's positions is the multiplicity-weighted sum
over its nodes. -/
theorem sum_runIndex (m : ℕ → ℕ) (f : ℕ → ℝ) : ∀ n : ℕ,
    ∑ t ∈ Finset.range (runStart m n), f (runIndex m n t)
      = ∑ i ∈ Finset.range n, (m i : ℝ) * f i := by
  intro n
  induction n with
  | zero => simp [runStart_zero]
  | succ k ih =>
    have hsplit : runStart m (k + 1) = runStart m k + m k := runStart_succ m k
    rw [Finset.sum_range_succ, ← ih]
    rw [hsplit, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _
      (Nat.zero_le (runStart m k)) (Nat.le_add_right _ _)]
    congr 1
    · rw [← Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun t ht =>
        congrArg f (runIndex_of_lt (Finset.mem_range.mp ht))
    · have hconst : ∀ t ∈ Finset.Ico (runStart m k) (runStart m k + m k),
          f (runIndex m (k + 1) t) = f k := by
        intro t ht
        simp only [Finset.mem_Ico] at ht
        exact congrArg f (runIndex_of_ge ht.1 (by rw [hsplit]; exact ht.2))
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico]
      simp [mul_comm]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.runIndex_lt
#print axioms CriticalLinePhasor.ThreeDConverse.runStart_runIndex_le
#print axioms CriticalLinePhasor.ThreeDConverse.sum_runIndex
