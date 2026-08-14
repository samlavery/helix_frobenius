import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Linearly weighted Cesàro means

The witness sequence's blocks have lengths `2j + 1`, cumulating to `k²`.  Averaging a per-block
error `a j` over positions therefore forms the **linearly weighted** mean

  **`(∑_{j<k} (2j+1)·a j) / k²`,**

and the assembly needs it to vanish when `a j → 0`.  Mathlib has the unweighted Cesàro theorem
(`Filter.Tendsto.cesaro`), and the weighted case reduces to it by the crude bound `2j + 1 ≤ 2k`:

  `(∑_{j<k} (2j+1)·a j) / k² ≤ 2k·(∑_{j<k} a j) / k² = 2·(∑_{j<k} a j)/k`.

No new limit theory is needed — the linear weight is absorbed by the `k²` normalisation.

**Scope.**  Generic; nothing here mentions Sato--Tate.
-/

open Filter
open scoped Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- **Linearly weighted Cesàro.**  Weights `2j+1` against normalisation `k²`. -/
theorem linear_weighted_cesaro {a : ℕ → ℝ} (hnn : ∀ j, 0 ≤ a j)
    (h : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) * a j) / ((k : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hces : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹ * ∑ j ∈ Finset.range k, a j) atTop (𝓝 0) := by
    simpa using h.cesaro
  have hmaj : Tendsto (fun k : ℕ => 2 * (((k : ℝ))⁻¹ * ∑ j ∈ Finset.range k, a j))
      atTop (𝓝 0) := by
    simpa using hces.const_mul (2 : ℝ)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with k
    have hs : 0 ≤ ∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) * a j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hnn j)
    positivity
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hbound : ∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) * a j
        ≤ ∑ j ∈ Finset.range k, (2 * (k : ℝ)) * a j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk : (j : ℝ) < (k : ℝ) := by exact_mod_cast Finset.mem_range.mp hj
      have h1 : 2 * (j : ℝ) + 1 ≤ 2 * (k : ℝ) := by
        have : (j : ℝ) + 1 ≤ (k : ℝ) := by
          have : (j : ℕ) + 1 ≤ k := Finset.mem_range.mp hj
          exact_mod_cast this
        linarith
      exact mul_le_mul_of_nonneg_right h1 (hnn j)
    calc (∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) * a j) / ((k : ℝ) ^ 2)
        ≤ (∑ j ∈ Finset.range k, (2 * (k : ℝ)) * a j) / ((k : ℝ) ^ 2) := by
          gcongr
      _ = 2 * (((k : ℝ))⁻¹ * ∑ j ∈ Finset.range k, a j) := by
          rw [← Finset.mul_sum]
          field_simp

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.linear_weighted_cesaro
