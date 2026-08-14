import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Summing a periodic function over a range

A Sato--Tate block cycles through its nodes: position `t` in the block uses node index
`t % T` where `T` is one pass's length.  Summing over the block therefore needs

  **`∑_{t < M} h(t % T) = ⌊M/T⌋·(∑_{t < T} h t) + ∑_{t < M % T} h t`**,

full cycles plus a remainder.  Each full cycle contributes the same exactly-cancelling node sum,
and only the remainder — fewer than `T` terms — has to be bounded crudely.  That is the split the
witness assembly needs.

**Scope.**  Generic; nothing here mentions Sato--Tate.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- **Periodic sums split into whole cycles plus a remainder.** -/
theorem sum_range_mod (h : ℕ → ℝ) {T : ℕ} (hT : 0 < T) : ∀ M : ℕ,
    ∑ t ∈ Finset.range M, h (t % T)
      = ((M / T : ℕ) : ℝ) * (∑ t ∈ Finset.range T, h t)
        + ∑ t ∈ Finset.range (M % T), h t := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rcases Nat.lt_or_ge M T with hlt | hge
    · rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Nat.mod_eq_of_lt (lt_trans (Finset.mem_range.mp ht) hlt)]
    · have hMT : M - T < M := by omega
      have hfirst : ∑ t ∈ Finset.range T, h (t % T) = ∑ t ∈ Finset.range T, h t :=
        Finset.sum_congr rfl fun t ht => by
          rw [Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
      have hsplit : ∑ t ∈ Finset.range M, h (t % T)
          = (∑ t ∈ Finset.range T, h (t % T))
            + ∑ t ∈ Finset.Ico T M, h (t % T) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          Finset.sum_Ico_consecutive _ (Nat.zero_le T) hge]
      have htail : ∑ t ∈ Finset.Ico T M, h (t % T)
          = ∑ t ∈ Finset.range (M - T), h (t % T) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Nat.add_mod_left]
      rw [hsplit, hfirst, htail, ih (M - T) hMT]
      have hdiv : M / T = (M - T) / T + 1 := by
        conv_lhs => rw [← Nat.sub_add_cancel hge]
        exact Nat.add_div_right _ hT
      have hmod : M % T = (M - T) % T := by
        conv_lhs => rw [← Nat.sub_add_cancel hge]
        rw [Nat.add_mod_right]
      rw [hdiv, hmod]
      push_cast
      ring

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.sum_range_mod
