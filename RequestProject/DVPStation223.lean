import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 223` (rung-235.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT223 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((223 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((211979/1000000 : ℚ) : ℝ))

theorem st223_c1 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((61101/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132487/2500000) (δ := 201/1000000000) (ψ := 211979/1000000) 223 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t1 : ((488783/500000 : ℚ) : ℝ) ≤ stT223 1 := by
  have hc : ((488783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488783/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((488783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c2 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-182471/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6799493/10000000) (δ := 11181/1000000000) (ψ := 211979/1000000) 223 25
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t2 : ((-322583889927/500000000000 : ℚ) : ℝ) ≤ stT223 2 := by
  have hc : ((-182481/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322583889927/500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-182481/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c3 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((241229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -332093/5000000) (δ := 11321/1000000000) (ψ := 211979/1000000) 223 39
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t3 : ((1392663945183/2500000000000 : ℚ) : ℝ) ≤ stT223 3 := by
  have hc : ((482433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1392663945183/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((482433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c4 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((246361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329869/1250000) (δ := 227/20000000) (ψ := 211979/1000000) 223 49
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t4 : ((3849/15625 : ℚ) : ℝ) ≤ stT223 4 := by
  have hc : ((7698/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3849/15625 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((7698/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c5 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((425969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1377803/10000000) (δ := 2823/250000000) (ψ := 211979/1000000) 223 57
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t5 : ((47621976761/125000000000 : ℚ) : ℝ) ≤ stT223 5 := by
  have hc : ((53243/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47621976761/125000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((53243/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c6 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-933009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6933703/10000000) (δ := 11261/1000000000) (ψ := 211979/1000000) 223 64
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t6 : ((-3809197505497/10000000000000 : ℚ) : ℝ) ≤ stT223 6 := by
  have hc : ((-933059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3809197505497/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-933059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c7 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((196543/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58187/1250000) (δ := 11297/1000000000) (ψ := 211979/1000000) 223 69
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t7 : ((185706193563/500000000000 : ℚ) : ℝ) ≤ stT223 7 := by
  have hc : ((196533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185706193563/500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((196533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c8 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((118293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726113/2000000) (δ := 11233/1000000000) (ψ := 211979/1000000) 223 74
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t8 : ((418052028519/10000000000000 : ℚ) : ℝ) ≤ stT223 8 := by
  have hc : ((118243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418052028519/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((118243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c9 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((949437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199599/2500000) (δ := 11241/1000000000) (ψ := 211979/1000000) 223 78
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t9 : ((3164623016871/10000000000000 : ℚ) : ℝ) ≤ stT223 9 := by
  have hc : ((949387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3164623016871/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((949387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c10 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-94101/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489177/1000000) (δ := 1119/100000000) (ψ := 211979/1000000) 223 82
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t10 : ((-297613050553/2500000000000 : ℚ) : ℝ) ≤ stT223 10 := by
  have hc : ((-188227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297613050553/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-188227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c11 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((450677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1119777/10000000) (δ := 707/62500000) (ψ := 211979/1000000) 223 85
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t11 : ((339691675919/1250000000000 : ℚ) : ℝ) ≤ stT223 11 := by
  have hc : ((112663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339691675919/1250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((112663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c12 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((107741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1252371/5000000) (δ := 1127/100000000) (ψ := 211979/1000000) 223 88
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t12 : ((310992571981/2000000000000 : ℚ) : ℝ) ≤ stT223 12 := by
  have hc : ((107731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310992571981/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((107731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c13 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((499999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2329/5000000) (δ := 2251/200000000) (ψ := 211979/1000000) 223 91
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t13 : ((1386677889/5000000000 : ℚ) : ℝ) ≤ stT223 13 := by
  have hc : ((249987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1386677889/5000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((249987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c14 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-682233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2902011/5000000) (δ := 1397/125000000) (ψ := 211979/1000000) 223 94
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t14 : ((-1823478415479/10000000000000 : ℚ) : ℝ) ≤ stT223 14 := by
  have hc : ((-682283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1823478415479/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-682283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c15 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((109851/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1243593/10000000) (δ := 2803/250000000) (ψ := 211979/1000000) 223 96
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t15 : ((283617826363/1250000000000 : ℚ) : ℝ) ≤ stT223 15 := by
  have hc : ((439379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((283617826363/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((439379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c16 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-4271/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145197/250000) (δ := 5649/500000000) (ψ := 211979/1000000) 223 98
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t16 : ((-170852568341/1000000000000 : ℚ) : ℝ) ≤ stT223 16 := by
  have hc : ((-68341/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170852568341/1000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-68341/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c17 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-247743/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1503559/2000000) (δ := 1397/125000000) (ψ := 211979/1000000) 223 101
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t17 : ((-1201791072427/5000000000000 : ℚ) : ℝ) ≤ stT223 17 := by
  have hc : ((-495511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1201791072427/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-495511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c18 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-475487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7067913/10000000) (δ := 11341/1000000000) (ψ := 211979/1000000) 223 103
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t18 : ((-140099090097/625000000000 : ℚ) : ℝ) ≤ stT223 18 := by
  have hc : ((-59439/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140099090097/625000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-59439/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c19 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-15329/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7366587/10000000) (δ := 2251/200000000) (ψ := 211979/1000000) 223 104
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t19 : ((-562703044687/2500000000000 : ℚ) : ℝ) ≤ stT223 19 := by
  have hc : ((-490553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562703044687/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-490553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c20 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-245343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181867/400000) (δ := 567/50000000) (ψ := 211979/1000000) 223 106
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t20 : ((-137178858681/2500000000000 : ℚ) : ℝ) ≤ stT223 20 := by
  have hc : ((-245393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137178858681/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-245393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c21 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((991233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66257/2000000) (δ := 5663/500000000) (ψ := 211979/1000000) 223 108
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t21 : ((1081468868287/5000000000000 : ℚ) : ℝ) ≤ stT223 21 := by
  have hc : ((991183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1081468868287/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((991183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c22 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-58729/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5149741/10000000) (δ := 11191/1000000000) (ψ := 211979/1000000) 223 110
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t22 : ((-62612011441/625000000000 : ℚ) : ℝ) ≤ stT223 22 := by
  have hc : ((-234941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62612011441/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-234941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c23 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((1127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1962087/5000000) (δ := 2241/200000000) (ψ := 211979/1000000) 223 111
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t23 : ((280712511/1250000000000 : ℚ) : ℝ) ≤ stT223 23 := by
  have hc : ((1077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280712511/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((1077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c24 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((64841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150591/400000) (δ := 11313/1000000000) (ψ := 211979/1000000) 223 113
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t24 : ((132254045631/10000000000000 : ℚ) : ℝ) ≤ stT223 24 := by
  have hc : ((64791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132254045631/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((64791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c25 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((12689/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1642763/5000000) (δ := 11283/1000000000) (ψ := 211979/1000000) 223 114
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t25 : ((25373/500000 : ℚ) : ℝ) ≤ stT223 25 := by
  have hc : ((25373/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25373/500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((25373/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c26 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-804687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313243/500000) (δ := 11169/1000000000) (ψ := 211979/1000000) 223 116
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t26 : ((-789109812197/5000000000000 : ℚ) : ℝ) ≤ stT223 26 := by
  have hc : ((-804737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-789109812197/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-804737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c27 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((931223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -466303/5000000) (δ := 11161/1000000000) (ψ := 211979/1000000) 223 117
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t27 : ((3584084877/20000000000 : ℚ) : ℝ) ≤ stT223 27 := by
  have hc : ((931173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3584084877/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((931173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c28 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((2919/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 454303/1250000) (δ := 11349/1000000000) (ψ := 211979/1000000) 223 118
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t28 : ((11028056281/500000000000 : ℚ) : ℝ) ≤ stT223 28 := by
  have hc : ((11671/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11028056281/500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((11671/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c29 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-247353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 374493/500000) (δ := 2789/250000000) (ψ := 211979/1000000) 223 119
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t29 : ((-459346354687/2500000000000 : ℚ) : ℝ) ≤ stT223 29 := by
  have hc : ((-494731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459346354687/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-494731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c30 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-212787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251299/500000) (δ := 1127/100000000) (ψ := 211979/1000000) 223 121
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t30 : ((-48567475813/625000000000 : ℚ) : ℝ) ≤ stT223 30 := by
  have hc : ((-53203/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48567475813/625000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-53203/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c31 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((111167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1226787/5000000) (δ := 11277/1000000000) (ψ := 211979/1000000) 223 122
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t31 : ((199643863321/2000000000000 : ℚ) : ℝ) ≤ stT223 31 := by
  have hc : ((111157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199643863321/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((111157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c32 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((983/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461637/10000000) (δ := 2257/200000000) (ψ := 211979/1000000) 223 123
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t32 : ((17376255897/100000000000 : ℚ) : ℝ) ≤ stT223 32 := by
  have hc : ((19659/20000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17376255897/100000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((19659/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c33 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((461647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 492783/5000000) (δ := 11311/1000000000) (ψ := 211979/1000000) 223 124
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t33 : ((50223781167/312500000000 : ℚ) : ℝ) ≤ stT223 33 := by
  have hc : ((230811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50223781167/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((230811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c34 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((719121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1920651/10000000) (δ := 11299/1000000000) (ψ := 211979/1000000) 223 125
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t34 : ((246639195787/2000000000000 : ℚ) : ℝ) ≤ stT223 34 := by
  have hc : ((719071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246639195787/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((719071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c35 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((291131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2373219/10000000) (δ := 5653/500000000) (ψ := 211979/1000000) 223 126
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t35 : ((61507350081/625000000000 : ℚ) : ℝ) ≤ stT223 35 := by
  have hc : ((145553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61507350081/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((145553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c36 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((18223/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 592633/2500000) (δ := 1119/100000000) (ψ := 211979/1000000) 223 127
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t36 : ((242952402819/2500000000000 : ℚ) : ℝ) ≤ stT223 36 := by
  have hc : ((291543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242952402819/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((291543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c37 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((357209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1937511/10000000) (δ := 11283/1000000000) (ψ := 211979/1000000) 223 128
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t37 : ((9175102609/78125000000 : ℚ) : ℝ) ≤ stT223 37 := by
  have hc : ((11162/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9175102609/78125000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((11162/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c38 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((3621/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109707/1000000) (δ := 177/15625000) (ψ := 211979/1000000) 223 129
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t38 : ((1835535141/12500000000 : ℚ) : ℝ) ≤ stT223 38 := by
  have hc : ((2263/2500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1835535141/12500000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((2263/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c39 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((499329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8097/625000) (δ := 2267/200000000) (ψ := 211979/1000000) 223 130
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t39 : ((99940751053/625000000000 : ℚ) : ℝ) ≤ stT223 39 := by
  have hc : ((62413/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99940751053/625000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((62413/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c40 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((154359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -861421/5000000) (δ := 5621/500000000) (ψ := 211979/1000000) 223 131
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t40 : ((122023534581/1000000000000 : ℚ) : ℝ) ≤ stT223 40 := by
  have hc : ((154349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122023534581/1000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((154349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c41 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((26183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3664681/10000000) (δ := 5577/500000000) (ψ := 211979/1000000) 223 132
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t41 : ((81742876317/5000000000000 : ℚ) : ℝ) ≤ stT223 41 := by
  have hc : ((52341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81742876317/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((52341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c42 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-360241/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742279/1250000) (δ := 1407/125000000) (ψ := 211979/1000000) 223 133
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t42 : ((-138975671761/1250000000000 : ℚ) : ℝ) ≤ stT223 42 := by
  have hc : ((-180133/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138975671761/1250000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-180133/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c43 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-481941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7180021/10000000) (δ := 11347/1000000000) (ψ := 211979/1000000) 223 133
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t43 : ((-183747850619/1250000000000 : ℚ) : ℝ) ≤ stT223 43 := by
  have hc : ((-240983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183747850619/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-240983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c44 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-144181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67011/156250) (δ := 11339/1000000000) (ψ := 211979/1000000) 223 134
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t44 : ((-217436453667/10000000000000 : ℚ) : ℝ) ≤ stT223 44 := by
  have hc : ((-144231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217436453667/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-144231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c45 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((225789/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1109327/10000000) (δ := 351/31250000) (ψ := 211979/1000000) 223 135
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t45 : ((673135024183/5000000000000 : ℚ) : ℝ) ≤ stT223 45 := by
  have hc : ((451553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((673135024183/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((451553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c46 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((591273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2345399/10000000) (δ := 5639/500000000) (ψ := 211979/1000000) 223 136
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t46 : ((871710424437/10000000000000 : ℚ) : ℝ) ≤ stT223 46 := by
  have hc : ((591223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((871710424437/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((591223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c47 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-754337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15159/25000) (δ := 2257/200000000) (ψ := 211979/1000000) 223 137
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t47 : ((-22007731951/200000000000 : ℚ) : ℝ) ≤ stT223 47 := by
  have hc : ((-754387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22007731951/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-754387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c48 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-643201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 567367/1000000) (δ := 5609/500000000) (ψ := 211979/1000000) 223 137
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t48 : ((-58028315961/625000000000 : ℚ) : ℝ) ≤ stT223 48 := by
  have hc : ((-643251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58028315961/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-643251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c49 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((834063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1460911/10000000) (δ := 1399/125000000) (ψ := 211979/1000000) 223 138
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t49 : ((1191446785423/10000000000000 : ℚ) : ℝ) ≤ stT223 49 := by
  have hc : ((834013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1191446785423/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((834013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c50 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((368319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2983991/10000000) (δ := 11299/1000000000) (ψ := 211979/1000000) 223 139
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t50 : ((520810807297/10000000000000 : ℚ) : ℝ) ≤ stT223 50 := by
  have hc : ((368269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520810807297/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((368269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c51 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-498369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1530401/2000000) (δ := 11207/1000000000) (ψ := 211979/1000000) 223 140
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t51 : ((-348945824357/2500000000000 : ℚ) : ℝ) ≤ stT223 51 := by
  have hc : ((-249197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348945824357/2500000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-249197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c52 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((296821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1586793/5000000) (δ := 11307/1000000000) (ψ := 211979/1000000) 223 140
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t52 : ((1646188737/40000000000 : ℚ) : ℝ) ≤ stT223 52 := by
  have hc : ((296771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1646188737/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((296771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c53 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((45043/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -957503/5000000) (δ := 5607/500000000) (ψ := 211979/1000000) 223 141
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t53 : ((98987195999/1000000000000 : ℚ) : ℝ) ≤ stT223 53 := by
  have hc : ((360319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98987195999/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((360319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c54 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-966199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1800531/2500000) (δ := 5641/500000000) (ψ := 211979/1000000) 223 142
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t54 : ((-328724673543/2500000000000 : ℚ) : ℝ) ≤ stT223 54 := by
  have hc : ((-966249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-328724673543/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-966249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c55 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((88021/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1211/4000) (δ := 11321/1000000000) (ψ := 211979/1000000) 223 142
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t55 : ((237341146783/5000000000000 : ℚ) : ℝ) ≤ stT223 55 := by
  have hc : ((176017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237341146783/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((176017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c56 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((98809/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52703/200000) (δ := 447/40000000) (ψ := 211979/1000000) 223 143
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t56 : ((66012848247/1000000000000 : ℚ) : ℝ) ≤ stT223 56 := by
  have hc : ((98799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66012848247/1000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((98799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c57 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-30289/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7232377/10000000) (δ := 447/40000000) (ψ := 211979/1000000) 223 143
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t57 : ((-641933593917/5000000000000 : ℚ) : ℝ) ≤ stT223 57 := by
  have hc : ((-484649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-641933593917/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-484649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c58 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((110401/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 610171/5000000) (δ := 2817/250000000) (ψ := 211979/1000000) 223 144
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t58 : ((72477686007/625000000000 : ℚ) : ℝ) ≤ stT223 58 := by
  have hc : ((441579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72477686007/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((441579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c59 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-400627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4957493/10000000) (δ := 279/25000000) (ψ := 211979/1000000) 223 145
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t59 : ((-52163737953/1000000000000 : ℚ) : ℝ) ≤ stT223 59 := by
  have hc : ((-400677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52163737953/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-400677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c60 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-48243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 882493/2000000) (δ := 563/50000000) (ψ := 211979/1000000) 223 145
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t60 : ((-24919043689/1000000000000 : ℚ) : ℝ) ≤ stT223 60 := by
  have hc : ((-96511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24919043689/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-96511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c61 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((168319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2080413/10000000) (δ := 9/800000) (ψ := 211979/1000000) 223 146
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t61 : ((26936782099/312500000000 : ℚ) : ℝ) ≤ stT223 61 := by
  have hc : ((336613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26936782099/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((336613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c62 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-94017/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 436551/625000) (δ := 227/20000000) (ψ := 211979/1000000) 223 146
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t62 : ((-29852032011/250000000000 : ℚ) : ℝ) ≤ stT223 62 := by
  have hc : ((-47011/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29852032011/250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-47011/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c63 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((199379/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7883/400000) (δ := 5623/500000000) (ψ := 211979/1000000) 223 147
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t63 : ((251181215089/2000000000000 : ℚ) : ℝ) ≤ stT223 63 := by
  have hc : ((199369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251181215089/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((199369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c64 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-180167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6731211/10000000) (δ := 11239/1000000000) (ψ := 211979/1000000) 223 148
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t64 : ((-225221430177/2000000000000 : ℚ) : ℝ) ≤ stT223 64 := by
  have hc : ((-180177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225221430177/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-180177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c65 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((144283/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1912381/10000000) (δ := 22/1953125) (ψ := 211979/1000000) 223 148
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t65 : ((178948582731/2000000000000 : ℚ) : ℝ) ≤ stT223 65 := by
  have hc : ((144273/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178948582731/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((144273/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c66 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-258261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5283951/10000000) (δ := 11271/1000000000) (ψ := 211979/1000000) 223 149
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t66 : ((-31792811169/500000000000 : ℚ) : ℝ) ≤ stT223 66 := by
  have hc : ((-129143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31792811169/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-129143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c67 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((162459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1549839/5000000) (δ := 11171/1000000000) (ψ := 211979/1000000) 223 149
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t67 : ((49611160799/1250000000000 : ℚ) : ℝ) ≤ stT223 67 := by
  have hc : ((81217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49611160799/1250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((81217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c68 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-167951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4348867/10000000) (δ := 5589/500000000) (ψ := 211979/1000000) 223 150
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t68 : ((-203731284679/10000000000000 : ℚ) : ℝ) ≤ stT223 68 := by
  have hc : ((-168001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203731284679/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-168001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c69 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((54783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 947491/2500000) (δ := 5589/500000000) (ψ := 211979/1000000) 223 150
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t69 : ((32945379957/5000000000000 : ℚ) : ℝ) ≤ stT223 69 := by
  have hc : ((54733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32945379957/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((54733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c70 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((3069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3896299/10000000) (δ := 5593/500000000) (ψ := 211979/1000000) 223 151
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t70 : ((1826607191/1250000000000 : ℚ) : ℝ) ≤ stT223 70 := by
  have hc : ((6113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1826607191/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((6113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c71 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-33843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 802323/2000000) (δ := 11317/1000000000) (ψ := 211979/1000000) 223 151
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t71 : ((-20111801163/5000000000000 : ℚ) : ℝ) ≤ stT223 71 := by
  have hc : ((-33893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20111801163/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-33893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c72 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((5601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1949493/5000000) (δ := 1131/100000000) (ψ := 211979/1000000) 223 152
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t72 : ((821422167/625000000000 : ℚ) : ℝ) ≤ stT223 72 := by
  have hc : ((697/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((821422167/625000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((697/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c73 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((27229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3790779/10000000) (δ := 1121/100000000) (ψ := 211979/1000000) 223 152
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t73 : ((7959965211/1250000000000 : ℚ) : ℝ) ≤ stT223 73 := by
  have hc : ((6801/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7959965211/1250000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((6801/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c74 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-4033/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2166031/5000000) (δ := 7/625000) (ψ := 211979/1000000) 223 153
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t74 : ((-18758891349/1000000000000 : ℚ) : ℝ) ≤ stT223 74 := by
  have hc : ((-16137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18758891349/1000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-16137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c75 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((76329/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 787829/2500000) (δ := 11203/1000000000) (ψ := 211979/1000000) 223 153
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t75 : ((1762453251/50000000000 : ℚ) : ℝ) ≤ stT223 75 := by
  have hc : ((152633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1762453251/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((152633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c76 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-47783/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161639/312500) (δ := 11207/1000000000) (ψ := 211979/1000000) 223 154
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t76 : ((-13704152813/250000000000 : ℚ) : ℝ) ≤ stT223 76 := by
  have hc : ((-11947/25000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13704152813/250000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-11947/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c77 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((662909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132203/625000) (δ := 11307/1000000000) (ψ := 211979/1000000) 223 154
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t77 : ((151079486139/2000000000000 : ℚ) : ℝ) ≤ stT223 77 := by
  have hc : ((662859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151079486139/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((662859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c78 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-104423/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -639907/1000000) (δ := 5607/500000000) (ψ := 211979/1000000) 223 155
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t78 : ((-236485884663/2500000000000 : ℚ) : ℝ) ≤ stT223 78 := by
  have hc : ((-417717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236485884663/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-417717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c79 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((240183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 351461/5000000) (δ := 11289/1000000000) (ψ := 211979/1000000) 223 155
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t79 : ((540425414667/5000000000000 : ℚ) : ℝ) ≤ stT223 79 := by
  have hc : ((480341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540425414667/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((480341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c80 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-249617/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7715603/10000000) (δ := 11289/1000000000) (ψ := 211979/1000000) 223 155
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t80 : ((-279094268403/2500000000000 : ℚ) : ℝ) ≤ stT223 80 := by
  have hc : ((-499259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279094268403/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-499259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c81 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((455163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16669/156250) (δ := 5611/500000000) (ψ := 211979/1000000) 223 156
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t81 : ((252854419159/2500000000000 : ℚ) : ℝ) ≤ stT223 81 := by
  have hc : ((227569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252854419159/2500000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((227569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c82 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-336667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1154753/2000000) (δ := 5661/500000000) (ψ := 211979/1000000) 223 156
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t82 : ((-23238397667/312500000000 : ℚ) : ℝ) ≤ stT223 82 := by
  have hc : ((-84173/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23238397667/312500000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-84173/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c83 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((295701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1588259/5000000) (δ := 11229/1000000000) (ψ := 211979/1000000) 223 157
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t83 : ((162259477471/5000000000000 : ℚ) : ℝ) ≤ stT223 83 := by
  have hc : ((295651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162259477471/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((295651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c84 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((84947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 700037/2000000) (δ := 11237/500000000) (ψ := 211979/1000000) 223 157
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t84 : ((46328730029/2500000000000 : ℚ) : ℝ) ≤ stT223 84 := by
  have hc : ((42461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46328730029/2500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((42461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c85 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-155879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701259/1250000) (δ := 11167/1000000000) (ψ := 211979/1000000) 223 158
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t85 : ((-338176366299/5000000000000 : ℚ) : ℝ) ≤ stT223 85 := by
  have hc : ((-311783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338176366299/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-311783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c86 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((58401/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56903/625000) (δ := 11167/1000000000) (ψ := 211979/1000000) 223 158
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t86 : ((503776042841/5000000000000 : ℚ) : ℝ) ≤ stT223 86 := by
  have hc : ((467183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((503776042841/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((467183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c87 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-980199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147113/200000) (δ := 2809/250000000) (ψ := 211979/1000000) 223 158
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t87 : ((-1050937696137/10000000000000 : ℚ) : ℝ) ≤ stT223 87 := by
  have hc : ((-980249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1050937696137/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-980249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c88 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((43887/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1980813/10000000) (δ := 11243/1000000000) (ψ := 211979/1000000) 223 159
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t88 : ((374242739213/5000000000000 : ℚ) : ℝ) ≤ stT223 88 := by
  have hc : ((351071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374242739213/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((351071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c89 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-156027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2159329/5000000) (δ := 279/25000000) (ψ := 211979/1000000) 223 159
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t89 : ((-82720653923/5000000000000 : ℚ) : ℝ) ≤ stT223 89 := by
  have hc : ((-156077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82720653923/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-156077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c90 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-473517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -516019/1000000) (δ := 227/20000000) (ψ := 211979/1000000) 223 160
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t90 : ((-499183659731/10000000000000 : ℚ) : ℝ) ≤ stT223 90 := by
  have hc : ((-473567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499183659731/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-473567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c91 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((184209/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1000101/10000000) (δ := 447/20000000) (ψ := 211979/1000000) 223 160
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t91 : ((48273216129/500000000000 : ℚ) : ℝ) ≤ stT223 91 := by
  have hc : ((184199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48273216129/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((184199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c92 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-190807/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3546523/5000000) (δ := 11253/1000000000) (ψ := 211979/1000000) 223 160
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t92 : ((-198940652141/2000000000000 : ℚ) : ℝ) ≤ stT223 92 := by
  have hc : ((-190817/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198940652141/2000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-190817/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c93 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((510409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8087/31250) (δ := 11257/1000000000) (ψ := 211979/1000000) 223 161
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t93 : ((529217275409/10000000000000 : ℚ) : ℝ) ≤ stT223 93 := by
  have hc : ((510359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529217275409/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((510359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c94 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((219089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3374789/10000000) (δ := 5673/500000000) (ψ := 211979/1000000) 223 161
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t94 : ((225921424419/10000000000000 : ℚ) : ℝ) ≤ stT223 94 := by
  have hc : ((219039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225921424419/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((219039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c95 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-210727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6433653/10000000) (δ := 2233/200000000) (ψ := 211979/1000000) 223 162
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t95 : ((-432428602941/5000000000000 : ℚ) : ℝ) ≤ stT223 95 := by
  have hc : ((-421479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432428602941/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-421479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c96 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((485863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595903/10000000) (δ := 2253/200000000) (ψ := 211979/1000000) 223 162
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t96 : ((12396399489/125000000000 : ℚ) : ℝ) ≤ stT223 96 := by
  have hc : ((242919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12396399489/125000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((242919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c97 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-240479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2590679/5000000) (δ := 2253/200000000) (ψ := 211979/1000000) 223 162
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t97 : ((-30524376861/625000000000 : ℚ) : ℝ) ≤ stT223 97 := by
  have hc : ((-30063/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30524376861/625000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-30063/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c98 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-345383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4808607/10000000) (δ := 11231/1000000000) (ψ := 211979/1000000) 223 163
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t98 : ((-348940181249/10000000000000 : ℚ) : ℝ) ≤ stT223 98 := by
  have hc : ((-345433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348940181249/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-345433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c99 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((471287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212839/2500000) (δ := 11231/1000000000) (ψ := 211979/1000000) 223 163
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t99 : ((236817873347/2500000000000 : ℚ) : ℝ) ≤ stT223 99 := by
  have hc : ((235631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236817873347/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((235631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c100 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-52959/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3227199/5000000) (δ := 11331/1000000000) (ψ := 211979/1000000) 223 163
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t100 : ((-423697/5000000 : ℚ) : ℝ) ≤ stT223 100 := by
  have hc : ((-423697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-423697/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-423697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c101 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((17639/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3706217/10000000) (δ := 1403/125000000) (ψ := 211979/1000000) 223 164
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t101 : ((17541507273/2000000000000 : ℚ) : ℝ) ≤ stT223 101 := by
  have hc : ((17629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17541507273/2000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((17629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c102 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((755371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44661/250000) (δ := 2831/250000000) (ψ := 211979/1000000) 223 164
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t102 : ((747878822187/10000000000000 : ℚ) : ℝ) ≤ stT223 102 := by
  have hc : ((755321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((747878822187/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((755321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c103 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-242141/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3612733/5000000) (δ := 1403/125000000) (ψ := 211979/1000000) 223 164
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t103 : ((-47720221631/500000000000 : ℚ) : ℝ) ≤ stT223 103 := by
  have hc : ((-484307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47720221631/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-484307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c104 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((163157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -773997/2500000) (δ := 11217/1000000000) (ψ := 211979/1000000) 223 165
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t104 : ((1999549707/62500000000 : ℚ) : ℝ) ≤ stT223 104 := by
  have hc : ((40783/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1999549707/62500000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((40783/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c105 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((78131/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69969/312500) (δ := 11317/1000000000) (ψ := 211979/1000000) 223 165
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t105 : ((3049677741/50000000000 : ℚ) : ℝ) ≤ stT223 105 := by
  have hc : ((312499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3049677741/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((312499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c106 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-991269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 940423/1250000) (δ := 5643/500000000) (ψ := 211979/1000000) 223 165
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t106 : ((-481427133117/5000000000000 : ℚ) : ℝ) ≤ stT223 106 := by
  have hc : ((-991319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-481427133117/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-991319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c107 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((381011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1474883/5000000) (δ := 11193/1000000000) (ψ := 211979/1000000) 223 166
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t107 : ((23018044581/625000000000 : ℚ) : ℝ) ≤ stT223 107 := by
  have hc : ((380961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23018044581/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((380961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c108 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((312943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1118161/5000000) (δ := 11193/1000000000) (ψ := 211979/1000000) 223 166
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t108 : ((602210691/10000000000 : ℚ) : ℝ) ≤ stT223 108 := by
  have hc : ((156459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((602210691/10000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((156459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c109 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-98167/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 460911/625000) (δ := 1131/100000000) (ψ := 211979/1000000) 223 166
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t109 : ((-23507948061/250000000000 : ℚ) : ℝ) ≤ stT223 109 := by
  have hc : ((-24543/25000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23507948061/250000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-24543/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c110 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((135287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1621009/5000000) (δ := 7/625000) (ψ := 211979/1000000) 223 167
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t110 : ((32241794261/1250000000000 : ℚ) : ℝ) ≤ stT223 110 := by
  have hc : ((67631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32241794261/1250000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((67631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c111 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((375467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1803301/10000000) (δ := 11203/1000000000) (ψ := 211979/1000000) 223 167
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t111 : ((178176701197/2500000000000 : ℚ) : ℝ) ≤ stT223 111 := by
  have hc : ((187721/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178176701197/2500000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((187721/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c112 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-912977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212603/312500) (δ := 113/10000000) (ψ := 211979/1000000) 223 167
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t112 : ((-53920635539/625000000000 : ℚ) : ℝ) ≤ stT223 112 := by
  have hc : ((-913027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53920635539/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-913027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c113 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-1103/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78981/200000) (δ := 1401/125000000) (ψ := 211979/1000000) 223 168
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t113 : ((-4173979077/5000000000000 : ℚ) : ℝ) ≤ stT223 113 := by
  have hc : ((-4437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4173979077/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-4437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c114 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((115843/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 962859/10000000) (δ := 2259/200000000) (ψ := 211979/1000000) 223 168
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t114 : ((86792769999/1000000000000 : ℚ) : ℝ) ≤ stT223 114 := by
  have hc : ((463347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86792769999/1000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((463347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c115 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-690343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5831897/10000000) (δ := 2239/200000000) (ψ := 211979/1000000) 223 168
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t115 : ((-128758984893/2000000000000 : ℚ) : ℝ) ≤ stT223 115 := by
  have hc : ((-690393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128758984893/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-690393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c116 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-433971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5049231/10000000) (δ := 2243/200000000) (ψ := 211979/1000000) 223 169
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t116 : ((-402978516017/10000000000000 : ℚ) : ℝ) ≤ stT223 116 := by
  have hc : ((-434021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402978516017/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-434021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c117 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((994439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -263763/10000000) (δ := 1411/125000000) (ψ := 211979/1000000) 223 169
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t117 : ((1838625261/20000000000 : ℚ) : ℝ) ≤ stT223 117 := by
  have hc : ((994389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1838625261/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((994389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c118 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-3434/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4480953/10000000) (δ := 2263/200000000) (ψ := 211979/1000000) 223 169
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t118 : ((-4047326399/200000000000 : ℚ) : ℝ) ≤ stT223 118 := by
  have hc : ((-109913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4047326399/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-109913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c119 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-861469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326119/500000) (δ := 11281/1000000000) (ψ := 211979/1000000) 223 170
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t119 : ((-789753605781/10000000000000 : ℚ) : ℝ) ≤ stT223 119 := by
  have hc : ((-861519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-789753605781/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-861519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c120 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((184141/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -464263/2500000) (δ := 5661/500000000) (ψ := 211979/1000000) 223 170
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t120 : ((33617076759/500000000000 : ℚ) : ℝ) ≤ stT223 120 := by
  have hc : ((368257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33617076759/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((368257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c121 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((446621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2769529/10000000) (δ := 5661/500000000) (ψ := 211979/1000000) 223 170
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t121 : ((40597323039/1000000000000 : ℚ) : ℝ) ≤ stT223 121 := by
  have hc : ((446571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40597323039/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((446571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c122 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-980387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 459877/625000) (δ := 11281/1000000000) (ψ := 211979/1000000) 223 170
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t122 : ((-443823240723/5000000000000 : ℚ) : ℝ) ≤ stT223 122 := by
  have hc : ((-980437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-443823240723/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-980437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c123 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((25609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3798891/10000000) (δ := 11229/1000000000) (ψ := 211979/1000000) 223 171
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t123 : ((1441768731/312500000000 : ℚ) : ℝ) ≤ stT223 123 := by
  have hc : ((1599/31250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1441768731/312500000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((1599/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c124 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((479673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357649/5000000) (δ := 11229/1000000000) (ψ := 211979/1000000) 223 171
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t124 : ((6730255857/78125000000 : ℚ) : ℝ) ≤ stT223 124 := by
  have hc : ((14989/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6730255857/78125000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((14989/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c125 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-485123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5193249/10000000) (δ := 5637/500000000) (ψ := 211979/1000000) 223 171
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t125 : ((-108488079011/2500000000000 : ℚ) : ℝ) ≤ stT223 125 := by
  have hc : ((-485173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108488079011/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-485173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c126 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-378327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3036221/5000000) (δ := 1417/125000000) (ψ := 211979/1000000) 223 172
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t126 : ((-21066426537/312500000000 : ℚ) : ℝ) ≤ stT223 126 := by
  have hc : ((-23647/31250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21066426537/312500000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-23647/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c127 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((786213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1665349/10000000) (δ := 2809/250000000) (ψ := 211979/1000000) 223 172
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t127 : ((174401613757/2500000000000 : ℚ) : ℝ) ≤ stT223 127 := by
  have hc : ((786163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174401613757/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((786163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c128 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((234387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 541447/2000000) (δ := 2809/250000000) (ψ := 211979/1000000) 223 172
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t128 : ((103574293823/2500000000000 : ℚ) : ℝ) ≤ stT223 128 := by
  have hc : ((117181/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103574293823/2500000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((117181/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c129 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-474101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7045811/10000000) (δ := 11267/1000000000) (ψ := 211979/1000000) 223 172
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t129 : ((-208722355413/2500000000000 : ℚ) : ℝ) ≤ stT223 129 := by
  have hc : ((-237063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208722355413/2500000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-237063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c130 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-171211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4357137/10000000) (δ := 11159/1000000000) (ψ := 211979/1000000) 223 173
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t130 : ((-150206001399/10000000000000 : ℚ) : ℝ) ≤ stT223 130 := by
  have hc : ((-171261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150206001399/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-171261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c131 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((999421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8507/1000000) (δ := 2811/250000000) (ψ := 211979/1000000) 223 173
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t131 : ((109144305023/1250000000000 : ℚ) : ℝ) ≤ stT223 131 := by
  have hc : ((999371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109144305023/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((999371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c132 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-22719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2077247/5000000) (δ := 11259/1000000000) (ψ := 211979/1000000) 223 173
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t132 : ((-39570495107/5000000000000 : ℚ) : ℝ) ≤ stT223 132 := by
  have hc : ((-45463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39570495107/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-45463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c133 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-48971/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1469181/2000000) (δ := 697/62500000) (ψ := 211979/1000000) 223 174
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t133 : ((-8493082317/100000000000 : ℚ) : ℝ) ≤ stT223 133 := by
  have hc : ((-97947/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8493082317/100000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-97947/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c134 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((298241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -792467/2500000) (δ := 5613/250000000) (ψ := 211979/1000000) 223 174
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t134 : ((64399415697/2500000000000 : ℚ) : ℝ) ≤ stT223 134 := by
  have hc : ((298191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64399415697/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((298191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c135 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((924891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 975117/10000000) (δ := 697/62500000) (ψ := 211979/1000000) 223 174
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t135 : ((397987752371/5000000000000 : ℚ) : ℝ) ≤ stT223 135 := by
  have hc : ((924841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397987752371/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((924841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c136 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-224217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5089523/10000000) (δ := 11251/1000000000) (ψ := 211979/1000000) 223 174
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t136 : ((-96142972653/2500000000000 : ℚ) : ℝ) ≤ stT223 136 := by
  have hc : ((-112121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96142972653/2500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-112121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c137 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-107981/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326707/500000) (δ := 2249/200000000) (ψ := 211979/1000000) 223 175
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t137 : ((-184519541871/2500000000000 : ℚ) : ℝ) ≤ stT223 137 := by
  have hc : ((-431949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184519541871/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-431949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c138 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((547147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247961/1000000) (δ := 2269/200000000) (ψ := 211979/1000000) 223 175
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t138 : ((58214950479/1250000000000 : ℚ) : ℝ) ≤ stT223 138 := by
  have hc : ((547097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58214950479/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((547097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c139 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((6519/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 386427/2500000) (δ := 5629/500000000) (ψ := 211979/1000000) 223 175
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t139 : ((6911247871/100000000000 : ℚ) : ℝ) ≤ stT223 139 := by
  have hc : ((32593/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6911247871/100000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((32593/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c140 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-602047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2771073/5000000) (δ := 2269/200000000) (ψ := 211979/1000000) 223 175
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t140 : ((-101773058007/2000000000000 : ℚ) : ℝ) ≤ stT223 140 := by
  have hc : ((-602097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101773058007/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-602097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c141 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-78849/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3098933/5000000) (δ := 2253/200000000) (ψ := 211979/1000000) 223 176
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t141 : ((-4150440863/62500000000 : ℚ) : ℝ) ≤ stT223 141 := by
  have hc : ((-39427/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4150440863/62500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-39427/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c142 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((619131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1128951/5000000) (δ := 2253/200000000) (ψ := 211979/1000000) 223 176
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t142 : ((519521012661/10000000000000 : ℚ) : ℝ) ≤ stT223 142 := by
  have hc : ((619081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519521012661/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((619081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c143 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((788909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 165441/1000000) (δ := 2253/200000000) (ψ := 211979/1000000) 223 176
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t143 : ((329838513939/5000000000000 : ℚ) : ℝ) ≤ stT223 143 := by
  have hc : ((788859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329838513939/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((788859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c144 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-601171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1384851/2500000) (δ := 5619/500000000) (ψ := 211979/1000000) 223 176
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t144 : ((-250508950407/5000000000000 : ℚ) : ℝ) ≤ stT223 144 := by
  have hc : ((-601221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250508950407/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-601221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c145 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-815363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -315519/500000) (δ := 1409/125000000) (ψ := 211979/1000000) 223 177
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t145 : ((-135432760583/2000000000000 : ℚ) : ℝ) ≤ stT223 145 := by
  have hc : ((-815413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135432760583/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-815413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c146 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((547439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2478739/10000000) (δ := 11331/1000000000) (ψ := 211979/1000000) 223 177
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t146 : ((90604374669/2000000000000 : ℚ) : ℝ) ≤ stT223 146 := by
  have hc : ((547389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90604374669/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((547389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c147 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((862463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1326701/10000000) (δ := 1409/125000000) (ψ := 211979/1000000) 223 177
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t147 : ((355653084309/5000000000000 : ℚ) : ℝ) ≤ stT223 147 := by
  have hc : ((862413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355653084309/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((862413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c148 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-113613/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5106383/10000000) (δ := 11331/1000000000) (ψ := 211979/1000000) 223 177
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t148 : ((-37359837149/1000000000000 : ℚ) : ℝ) ≤ stT223 148 := by
  have hc : ((-227251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37359837149/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-227251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c149 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-46001/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6847319/10000000) (δ := 11179/1000000000) (ψ := 211979/1000000) 223 178
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t149 : ((-2355471207/31250000000 : ℚ) : ℝ) ≤ stT223 149 := by
  have hc : ((-92007/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2355471207/31250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-92007/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c150 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((317881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3118257/10000000) (δ := 11279/1000000000) (ψ := 211979/1000000) 223 178
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t150 : ((16219233761/625000000000 : ℚ) : ℝ) ≤ stT223 150 := by
  have hc : ((317831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16219233761/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((317831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c151 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((243161/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 586107/10000000) (δ := 1403/125000000) (ψ := 211979/1000000) 223 178
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t151 : ((98935665759/1250000000000 : ℚ) : ℝ) ≤ stT223 151 := by
  have hc : ((486297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98935665759/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((486297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c152 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-135187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4265997/10000000) (δ := 2831/250000000) (ψ := 211979/1000000) 223 178
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t152 : ((-27422953149/2500000000000 : ℚ) : ℝ) ≤ stT223 152 := by
  have hc : ((-135237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27422953149/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-135237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c153 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-999633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1557243/2000000) (δ := 11287/1000000000) (ψ := 211979/1000000) 223 179
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t153 : ((-808196720399/10000000000000 : ℚ) : ℝ) ≤ stT223 153 := by
  have hc : ((-999683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-808196720399/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-999683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c154 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-45393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -415427/1000000) (δ := 11187/1000000000) (ψ := 211979/1000000) 223 179
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t154 : ((-18299434507/2500000000000 : ℚ) : ℝ) ≤ stT223 154 := by
  have hc : ((-22709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18299434507/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-22709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c155 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((488129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -545851/10000000) (δ := 11287/1000000000) (ψ := 211979/1000000) 223 179
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t155 : ((49006800847/625000000000 : ℚ) : ℝ) ≤ stT223 155 := by
  have hc : ((61013/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49006800847/625000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((61013/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c156 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((173817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4863/16000) (δ := 2829/250000000) (ψ := 211979/1000000) 223 179
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t156 : ((6794181/244140625 : ℚ) : ℝ) ≤ stT223 156 := by
  have hc : ((5431/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6794181/244140625 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((5431/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c157 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-877143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6601689/10000000) (δ := 11187/1000000000) (ψ := 211979/1000000) 223 179
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t157 : ((-700076329791/10000000000000 : ℚ) : ℝ) ≤ stT223 157 := by
  have hc : ((-877193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-700076329791/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-877193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c158 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-609827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113319/2000000) (δ := 5647/500000000) (ψ := 211979/1000000) 223 180
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t158 : ((-242596263183/5000000000000 : ℚ) : ℝ) ≤ stT223 158 := by
  have hc : ((-609877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242596263183/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-609877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c159 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((13649/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32019/156250) (δ := 5647/500000000) (ψ := 211979/1000000) 223 180
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t159 : ((676472503/12500000000 : ℚ) : ℝ) ≤ stT223 159 := by
  have hc : ((853/1250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((676472503/12500000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((853/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c160 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((20933/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 723043/5000000) (δ := 5647/500000000) (ψ := 211979/1000000) 223 180
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t160 : ((66191970663/1000000000000 : ℚ) : ℝ) ≤ stT223 160 := by
  have hc : ((83727/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66191970663/1000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((83727/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c161 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-38669/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4919589/10000000) (δ := 11309/1000000000) (ψ := 211979/1000000) 223 180
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t161 : ((-15239702407/500000000000 : ℚ) : ℝ) ≤ stT223 161 := by
  have hc : ((-19337/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15239702407/500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-19337/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c162 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-12233/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3668167/5000000) (δ := 5601/500000000) (ψ := 211979/1000000) 223 181
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t162 : ((-3075729063/40000000000 : ℚ) : ℝ) ≤ stT223 162 := by
  have hc : ((-97869/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3075729063/40000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-97869/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c163 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((4291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781107/2000000) (δ := 5651/500000000) (ψ := 211979/1000000) 223 181
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t163 : ((83534679/125000000000 : ℚ) : ℝ) ≤ stT223 163 := by
  have hc : ((2133/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83534679/125000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((2133/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c164 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((980403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495753/10000000) (δ := 11201/1000000000) (ψ := 211979/1000000) 223 181
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t164 : ((191381571601/2500000000000 : ℚ) : ℝ) ≤ stT223 164 := by
  have hc : ((980353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191381571601/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((980353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c165 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((401799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2893289/10000000) (δ := 5651/500000000) (ψ := 211979/1000000) 223 181
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t165 : ((156380396501/5000000000000 : ℚ) : ℝ) ≤ stT223 165 := by
  have hc : ((401749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156380396501/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((401749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c166 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-803977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391367/625000) (δ := 11301/1000000000) (ψ := 211979/1000000) 223 181
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t166 : ((-624046360077/10000000000000 : ℚ) : ℝ) ≤ stT223 166 := by
  have hc : ((-804027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-624046360077/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-804027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c167 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-763219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6097691/10000000) (δ := 2239/200000000) (ψ := 211979/1000000) 223 182
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t167 : ((-9228685479/156250000000 : ℚ) : ℝ) ≤ stT223 167 := by
  have hc : ((-763269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9228685479/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-763269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c168 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((446681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34617/125000) (δ := 1401/125000000) (ψ := 211979/1000000) 223 182
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t168 : ((86145740649/2500000000000 : ℚ) : ℝ) ≤ stT223 168 := by
  have hc : ((446631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86145740649/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((446631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c169 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((976823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 539291/10000000) (δ := 1401/125000000) (ψ := 211979/1000000) 223 182
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t169 : ((75136309479/1000000000000 : ℚ) : ℝ) ≤ stT223 169 := by
  have hc : ((976773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75136309479/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((976773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c170 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((9859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1914187/5000000) (δ := 2827/250000000) (ψ := 211979/1000000) 223 182
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t170 : ((3775955513/1250000000000 : ℚ) : ℝ) ≤ stT223 170 := by
  have hc : ((19693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3775955513/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((19693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c171 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-954647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7098167/10000000) (δ := 1401/125000000) (ψ := 211979/1000000) 223 182
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t171 : ((-9125948623/125000000000 : ℚ) : ℝ) ≤ stT223 171 := by
  have hc : ((-954697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9125948623/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-954697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c172 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-271007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -535907/1000000) (δ := 1411/125000000) (ψ := 211979/1000000) 223 183
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t172 : ((-25832500347/625000000000 : ℚ) : ℝ) ≤ stT223 172 := by
  have hc : ((-33879/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25832500347/625000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-33879/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c173 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((329663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1063593/5000000) (δ := 2263/200000000) (ψ := 211979/1000000) 223 183
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t173 : ((25061882683/500000000000 : ℚ) : ℝ) ≤ stT223 173 := by
  have hc : ((164819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25061882683/500000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((164819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c174 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((90711/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271519/2500000) (δ := 1411/125000000) (ψ := 211979/1000000) 223 183
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t174 : ((17191009297/250000000000 : ℚ) : ℝ) ≤ stT223 174 := by
  have hc : ((45353/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17191009297/250000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((45353/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c175 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-35277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2140471/5000000) (δ := 2263/200000000) (ψ := 211979/1000000) 223 183
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t175 : ((-53352712891/5000000000000 : ℚ) : ℝ) ≤ stT223 175 := by
  have hc : ((-70579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53352712891/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-70579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c176 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-197491/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7457577/10000000) (δ := 2263/200000000) (ψ := 211979/1000000) 223 183
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t176 : ((-148872106279/2000000000000 : ℚ) : ℝ) ≤ stT223 176 := by
  have hc : ((-197501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148872106279/2000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-197501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c177 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-224607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5091703/10000000) (δ := 11223/1000000000) (ψ := 211979/1000000) 223 184
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t177 : ((-21105496113/625000000000 : ℚ) : ℝ) ≤ stT223 177 := by
  have hc : ((-28079/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21105496113/625000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-28079/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c178 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((44417/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97543/500000) (δ := 141/12500000) (ψ := 211979/1000000) 223 184
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t178 : ((266316609141/5000000000000 : ℚ) : ℝ) ≤ stT223 178 := by
  have hc : ((355311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266316609141/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((355311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c179 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((178407/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1172423/10000000) (δ := 11323/1000000000) (ψ := 211979/1000000) 223 184
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t179 : ((26668032339/400000000000 : ℚ) : ℝ) ≤ stT223 179 := by
  have hc : ((178397/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26668032339/400000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((178397/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c180 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-35011/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 855651/2000000) (δ := 559/50000000) (ψ := 211979/1000000) 223 184
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t180 : ((-13052487933/1250000000000 : ℚ) : ℝ) ≤ stT223 180 := by
  have hc : ((-70047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13052487933/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-70047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c181 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-981081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7366917/10000000) (δ := 11323/1000000000) (ψ := 211979/1000000) 223 184
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t181 : ((-145853953329/2000000000000 : ℚ) : ℝ) ≤ stT223 181 := by
  have hc : ((-981131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145853953329/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-981131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c182 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-102309/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053889/2000000) (δ := 11273/1000000000) (ψ := 211979/1000000) 223 185
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t182 : ((-60675167/1600000000 : ℚ) : ℝ) ≤ stT223 182 := by
  have hc : ((-102319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60675167/1600000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-102319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c183 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((79079/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2214623/10000000) (δ := 1133/100000000) (ψ := 211979/1000000) 223 185
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t183 : ((233808949311/5000000000000 : ℚ) : ℝ) ≤ stT223 183 := by
  have hc : ((316291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233808949311/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((316291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c184 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((946233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 823529/10000000) (δ := 1133/100000000) (ψ := 211979/1000000) 223 185
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t184 : ((697534623247/10000000000000 : ℚ) : ℝ) ≤ stT223 184 := by
  have hc : ((946183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((697534623247/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((946183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c185 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((32697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1922617/5000000) (δ := 11273/1000000000) (ψ := 211979/1000000) 223 185
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t185 : ((12001265729/5000000000000 : ℚ) : ℝ) ≤ stT223 185 := by
  have hc : ((32647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12001265729/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((32647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c186 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-460267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1370121/2000000) (δ := 11273/1000000000) (ψ := 211979/1000000) 223 185
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t186 : ((-21093916557/312500000000 : ℚ) : ℝ) ≤ stT223 186 := by
  have hc : ((-115073/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21093916557/312500000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-115073/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c187 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-70073/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5868043/10000000) (δ := 5583/500000000) (ψ := 211979/1000000) 223 186
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t187 : ((-25623074647/500000000000 : ℚ) : ℝ) ≤ stT223 187 := by
  have hc : ((-35039/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25623074647/500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-35039/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c188 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((50159/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361841/1250000) (δ := 11237/1000000000) (ψ := 211979/1000000) 223 186
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t188 : ((36577604241/1250000000000 : ℚ) : ℝ) ≤ stT223 188 := by
  have hc : ((200611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36577604241/1250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((200611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c189 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((249921/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12573/2000000) (δ := 5583/500000000) (ψ := 211979/1000000) 223 186
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t189 : ((11361340227/156250000000 : ℚ) : ℝ) ≤ stT223 189 := by
  have hc : ((499817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11361340227/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((499817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c190 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((36057/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3004793/10000000) (δ := 11337/1000000000) (ψ := 211979/1000000) 223 186
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t190 : ((1634678797/62500000000 : ℚ) : ℝ) ≤ stT223 190 := by
  have hc : ((9013/25000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1634678797/62500000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((9013/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c191 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-143713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5931333/10000000) (δ := 5583/500000000) (ψ := 211979/1000000) 223 186
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t191 : ((-4159774789/80000000000 : ℚ) : ℝ) ≤ stT223 191 := by
  have hc : ((-143723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4159774789/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-143723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c192 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-922833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6865421/10000000) (δ := 11159/1000000000) (ψ := 211979/1000000) 223 187
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t192 : ((-83254198313/1250000000000 : ℚ) : ℝ) ≤ stT223 192 := by
  have hc : ((-922883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83254198313/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-922883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c193 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-16931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -99233/250000) (δ := 11159/1000000000) (ψ := 211979/1000000) 223 187
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t193 : ((-1527899437/1250000000000 : ℚ) : ℝ) ≤ stT223 193 := by
  have hc : ((-16981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1527899437/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-16981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c194 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((906759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6801/62500) (δ := 11159/1000000000) (ψ := 211979/1000000) 223 187
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t194 : ((325489490111/5000000000000 : ℚ) : ℝ) ≤ stT223 194 := by
  have hc : ((906709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325489490111/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((906709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c195 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((378767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1778171/10000000) (δ := 709/62500000) (ψ := 211979/1000000) 223 187
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t195 : ((67805612147/1250000000000 : ℚ) : ℝ) ≤ stT223 195 := by
  have hc : ((189371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67805612147/1250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((189371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c196 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-5549/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4629839/10000000) (δ := 2811/250000000) (ψ := 211979/1000000) 223 187
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t196 : ((-39642873/2000000000 : ℚ) : ℝ) ≤ stT223 196 := by
  have hc : ((-111/400 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39642873/2000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-111/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c197 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-247011/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1866753/2500000) (δ := 11159/1000000000) (ψ := 211979/1000000) 223 187
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t197 : ((-351994160137/5000000000000 : ℚ) : ℝ) ≤ stT223 197 := by
  have hc : ((-494047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351994160137/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-494047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c198 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-140431/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5418161/10000000) (δ := 11351/1000000000) (ψ := 211979/1000000) 223 188
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t198 : ((-19961796429/500000000000 : ℚ) : ℝ) ≤ stT223 198 := by
  have hc : ((-280887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19961796429/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-280887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c199 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((502909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -652397/2500000) (δ := 697/62500000) (ψ := 211979/1000000) 223 188
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t199 : ((356467190779/10000000000000 : ℚ) : ℝ) ≤ stT223 199 := by
  have hc : ((502859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356467190779/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((502859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c200 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((997267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184881/10000000) (δ := 11251/1000000000) (ψ := 211979/1000000) 223 188
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t200 : ((352569062001/5000000000000 : ℚ) : ℝ) ≤ stT223 200 := by
  have hc : ((997217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352569062001/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((997217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c201 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((375197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 741367/2500000) (δ := 11251/1000000000) (ψ := 211979/1000000) 223 188
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t201 : ((52921612143/2000000000000 : ℚ) : ℝ) ≤ stT223 201 := by
  have hc : ((375147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52921612143/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((375147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c202 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-330471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5732173/10000000) (δ := 697/62500000) (ψ := 211979/1000000) 223 188
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t202 : ((-454172509/9765625000 : ℚ) : ℝ) ≤ stT223 202 := by
  have hc : ((-10328/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454172509/9765625000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-10328/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c203 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-968287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225709/312500) (δ := 5579/500000000) (ψ := 211979/1000000) 223 189
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t203 : ((-679639911831/10000000000000 : ℚ) : ℝ) ≤ stT223 203 := by
  have hc : ((-968337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-679639911831/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-968337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c204 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-220627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4483133/10000000) (δ := 5579/500000000) (ψ := 211979/1000000) 223 189
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t204 : ((-154505015457/10000000000000 : ℚ) : ℝ) ≤ stT223 204 := by
  have hc : ((-220677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154505015457/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-220677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c205 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((381523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -878479/5000000) (δ := 5579/500000000) (ψ := 211979/1000000) 223 189
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t205 : ((13322482407/250000000000 : ℚ) : ℝ) ≤ stT223 205 := by
  have hc : ((190749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13322482407/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((190749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c206 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((46389/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 238987/2500000) (δ := 2269/200000000) (ψ := 211979/1000000) 223 189
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t206 : ((64638010609/1000000000000 : ℚ) : ℝ) ≤ stT223 206 := by
  have hc : ((92773/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64638010609/1000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((92773/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c207 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((6769/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1827849/5000000) (δ := 5579/500000000) (ψ := 211979/1000000) 223 189
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t207 : ((4702607887/625000000000 : ℚ) : ℝ) ≤ stT223 207 := by
  have hc : ((54127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4702607887/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((54127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c208 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-205681/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3171229/5000000) (δ := 5629/500000000) (ψ := 211979/1000000) 223 189
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t208 : ((-2228483379/39062500000 : ℚ) : ℝ) ≤ stT223 208 := by
  have hc : ((-411387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2228483379/39062500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-411387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c209 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-893847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -836453/1250000) (δ := 5583/500000000) (ψ := 211979/1000000) 223 190
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t209 : ((-123664392671/2000000000000 : ℚ) : ℝ) ≤ stT223 209 := by
  have hc : ((-893897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123664392671/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-893897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c210 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-8279/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4030509/10000000) (δ := 5633/500000000) (ψ := 211979/1000000) 223 190
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t210 : ((-2859978537/1000000000000 : ℚ) : ℝ) ≤ stT223 210 := by
  have hc : ((-8289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2859978537/1000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-8289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c211 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((851047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27641/200000) (δ := 11237/1000000000) (ψ := 211979/1000000) 223 190
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t211 : ((146462540679/2500000000000 : ℚ) : ℝ) ≤ stT223 211 := by
  have hc : ((850997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146462540679/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((850997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c212 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((21921/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 626933/5000000) (δ := 5583/500000000) (ψ := 211979/1000000) 223 190
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t212 : ((30109056279/500000000000 : ℚ) : ℝ) ≤ stT223 212 := by
  have hc : ((87679/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30109056279/500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((87679/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c213 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((19833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 775481/2000000) (δ := 11237/1000000000) (ψ := 211979/1000000) 223 190
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t213 : ((3388768551/2500000000000 : ℚ) : ℝ) ≤ stT223 213 := by
  have hc : ((19783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3388768551/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((19783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c214 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-427273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6488679/10000000) (δ := 11337/1000000000) (ψ := 211979/1000000) 223 190
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t214 : ((-73023732657/1250000000000 : ℚ) : ℝ) ≤ stT223 214 := by
  have hc : ((-213649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73023732657/1250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-213649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c215 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-440339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6620219/10000000) (δ := 1123/100000000) (ψ := 211979/1000000) 223 191
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t215 : ((-15016302309/250000000000 : ℚ) : ℝ) ≤ stT223 215 := by
  have hc : ((-110091/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15016302309/250000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-110091/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c216 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-42469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1008299/2500000) (δ := 1123/100000000) (ψ := 211979/1000000) 223 191
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t216 : ((-14465261433/5000000000000 : ℚ) : ℝ) ≤ stT223 216 := by
  have hc : ((-42519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14465261433/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-42519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c217 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((83467/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1458159/10000000) (δ := 11173/1000000000) (ψ := 211979/1000000) 223 191
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t217 : ((7082209741/125000000000 : ℚ) : ℝ) ≤ stT223 217 := by
  have hc : ((41731/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7082209741/125000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((41731/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c218 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((56493/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1105059/10000000) (δ := 11273/1000000000) (ψ := 211979/1000000) 223 191
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t218 : ((61215591983/1000000000000 : ℚ) : ℝ) ≤ stT223 218 := by
  have hc : ((451919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61215591983/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((451919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c219 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((53979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3656569/10000000) (δ := 11173/1000000000) (ψ := 211979/1000000) 223 191
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t219 : ((18229357049/2500000000000 : ℚ) : ℝ) ≤ stT223 219 := by
  have hc : ((26977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18229357049/2500000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((26977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c220 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-98517/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6196427/10000000) (δ := 1133/100000000) (ψ := 211979/1000000) 223 191
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t220 : ((-1328487503/25000000000 : ℚ) : ℝ) ≤ stT223 220 := by
  have hc : ((-394093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1328487503/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-394093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c221 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-187989/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3491581/5000000) (δ := 11223/1000000000) (ψ := 211979/1000000) 223 192
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t221 : ((-126461851327/2000000000000 : ℚ) : ℝ) ≤ stT223 221 := by
  have hc : ((-187999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126461851327/2000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-187999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c222 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-214043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139571/312500) (δ := 141/12500000) (ψ := 211979/1000000) 223 192
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t222 : ((-143690015601/10000000000000 : ℚ) : ℝ) ≤ stT223 222 := by
  have hc : ((-214093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143690015601/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-214093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c223 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((707913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -490161/2500000) (δ := 141/12500000) (ψ := 211979/1000000) 223 192
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t223 : ((474019750087/10000000000000 : ℚ) : ℝ) ≤ stT223 223 := by
  have hc : ((707863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474019750087/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((707863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c224 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((977293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266889/5000000) (δ := 559/50000000) (ψ := 211979/1000000) 223 192
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t224 : ((652947842179/10000000000000 : ℚ) : ℝ) ≤ stT223 224 := by
  have hc : ((977243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((652947842179/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((977243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c225 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((88993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1508553/5000000) (δ := 559/50000000) (ψ := 211979/1000000) 223 192
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t225 : ((59320274013/2500000000000 : ℚ) : ℝ) ≤ stT223 225 := by
  have hc : ((177961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59320274013/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((177961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c226 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-585057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 686171/1250000) (δ := 281/12500000) (ψ := 211979/1000000) 223 192
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t226 : ((-389207910437/10000000000000 : ℚ) : ℝ) ≤ stT223 226 := by
  have hc : ((-585107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389207910437/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-585107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c227 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-999251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1551441/2000000) (δ := 11287/1000000000) (ψ := 211979/1000000) 223 193
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t227 : ((-165815014231/2500000000000 : ℚ) : ℝ) ≤ stT223 227 := by
  have hc : ((-999301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165815014231/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-999301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c228 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-262139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2653329/5000000) (δ := 11287/1000000000) (ψ := 211979/1000000) 223 193
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t228 : ((-43405641447/1250000000000 : ℚ) : ℝ) ≤ stT223 228 := by
  have hc : ((-65541/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43405641447/1250000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-65541/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c229 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((205737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -573363/2000000) (δ := 11287/1000000000) (ψ := 211979/1000000) 223 193
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t229 : ((4248068513/156250000000 : ℚ) : ℝ) ≤ stT223 229 := by
  have hc : ((12857/31250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4248068513/156250000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((12857/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c230 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((492359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -437621/10000000) (δ := 2829/250000000) (ψ := 211979/1000000) 223 193
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t230 : ((8115879823/125000000000 : ℚ) : ℝ) ≤ stT223 230 := by
  have hc : ((246167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8115879823/125000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((246167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c231 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((43883/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1981037/10000000) (δ := 2829/250000000) (ψ := 211979/1000000) 223 193
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t231 : ((230966461089/5000000000000 : ℚ) : ℝ) ≤ stT223 231 := by
  have hc : ((351039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230966461089/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((351039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c232 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-91919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2194607/5000000) (δ := 2829/250000000) (ψ := 211979/1000000) 223 193
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t232 : ((-7545533769/625000000000 : ℚ) : ℝ) ≤ stT223 232 := by
  have hc : ((-11493/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7545533769/625000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-11493/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c233 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-910311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3393539/5000000) (δ := 11287/1000000000) (ψ := 211979/1000000) 223 193
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t233 : ((-298198759521/5000000000000 : ℚ) : ℝ) ≤ stT223 233 := by
  have hc : ((-910361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298198759521/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-910361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c234 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-34547/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40833/62500) (δ := 5647/500000000) (ψ := 211979/1000000) 223 194
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t234 : ((-22585406829/400000000000 : ℚ) : ℝ) ≤ stT223 234 := by
  have hc : ((-34549/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22585406829/400000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-34549/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c235 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-91427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4155877/10000000) (δ := 5647/500000000) (ψ := 211979/1000000) 223 194
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t235 : ((-59673099933/10000000000000 : ℚ) : ℝ) ≤ stT223 235 := by
  have hc : ((-91477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59673099933/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-91477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c236 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((377407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -357713/2000000) (δ := 5597/500000000) (ψ := 211979/1000000) 223 194
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t236 : ((1919176161/39062500000 : ℚ) : ℝ) ≤ stT223 236 := by
  have hc : ((188691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1919176161/39062500000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((188691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c237 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((974237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71089/1250000) (δ := 11209/1000000000) (ψ := 211979/1000000) 223 194
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t237 : ((632801675403/10000000000000 : ℚ) : ℝ) ≤ stT223 237 := by
  have hc : ((974187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((632801675403/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((974187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c238 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((2459/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1458033/5000000) (δ := 5597/500000000) (ψ := 211979/1000000) 223 194
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t238 : ((25499657817/1000000000000 : ℚ) : ℝ) ≤ stT223 238 := by
  have hc : ((39339/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25499657817/1000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((39339/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c239 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-506091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 656701/1250000) (δ := 5647/500000000) (ψ := 211979/1000000) 223 194
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t239 : ((-327395787427/10000000000000 : ℚ) : ℝ) ≤ stT223 239 := by
  have hc : ((-506141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327395787427/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-506141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c240 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-497031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7581393/10000000) (δ := 11209/1000000000) (ψ := 211979/1000000) 223 194
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t240 : ((-5013260217/78125000000 : ℚ) : ℝ) ≤ stT223 240 := by
  have hc : ((-15533/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5013260217/78125000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-15533/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c241 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-683537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1161697/2000000) (δ := 5601/500000000) (ψ := 211979/1000000) 223 195
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t241 : ((-440337351159/10000000000000 : ℚ) : ℝ) ≤ stT223 241 := by
  have hc : ((-683587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-440337351159/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-683587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c242 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((169971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3499989/10000000) (δ := 5601/500000000) (ψ := 211979/1000000) 223 195
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t242 : ((13653662113/1250000000000 : ℚ) : ℝ) ≤ stT223 242 := by
  have hc : ((169921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13653662113/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((169921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c243 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((177361/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -600513/5000000) (δ := 5651/500000000) (ψ := 211979/1000000) 223 195
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t243 : ((227541333/4000000000 : ℚ) : ℝ) ≤ stT223 243 := by
  have hc : ((177351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227541333/4000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((177351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c244 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((906699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 217703/2000000) (δ := 5651/500000000) (ψ := 211979/1000000) 223 195
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t244 : ((72552772927/1250000000000 : ℚ) : ℝ) ≤ stT223 244 := by
  have hc : ((906649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72552772927/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((906649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c245 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((5537/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1684331/5000000) (δ := 11201/500000000) (ψ := 211979/1000000) 223 195
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t245 : ((3536657817/250000000000 : ℚ) : ℝ) ≤ stT223 245 := by
  have hc : ((22143/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3536657817/250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((22143/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c246 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-632693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2819777/5000000) (δ := 11301/1000000000) (ψ := 211979/1000000) 223 195
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t246 : ((-403422383711/10000000000000 : ℚ) : ℝ) ≤ stT223 246 := by
  have hc : ((-632743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403422383711/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-632743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c247 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-999821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7806743/10000000) (δ := 5597/500000000) (ψ := 211979/1000000) 223 196
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t247 : ((-127240583847/2000000000000 : ℚ) : ℝ) ≤ stT223 247 := by
  have hc : ((-999871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127240583847/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-999871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c248 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-75737/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277711/500000) (δ := 5597/500000000) (ψ := 211979/1000000) 223 196
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t248 : ((-192388157973/5000000000000 : ℚ) : ℝ) ≤ stT223 248 := by
  have hc : ((-302973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192388157973/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-302973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c249 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((48799/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51731/156250) (δ := 11209/1000000000) (ψ := 211979/1000000) 223 196
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t249 : ((7729690059/500000000000 : ℚ) : ℝ) ≤ stT223 249 := by
  have hc : ((48789/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7729690059/500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((48789/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_c250 :
    |Real.cos (((223 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((454377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269067/2500000) (δ := 11309/1000000000) (ψ := 211979/1000000) 223 196
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223_t250 : ((3591964927/62500000000 : ℚ) : ℝ) ≤ stT223 250 := by
  have hc : ((28397/31250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3591964927/62500000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((28397/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223_p1 : ((488783/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT223 (i+1) := by
  rw [Finset.sum_range_one]
  exact st223_t1

theorem st223_p2 : ((166199110073/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT223 (i+1))
      = (∑ i ∈ Finset.range 1, stT223 (i+1)) + stT223 2 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 1
    simpa using h
  have hprev := st223_p1
  have hstep := st223_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p3 : ((555914873887/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT223 (i+1))
      = (∑ i ∈ Finset.range 2, stT223 (i+1)) + stT223 3 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 2
    simpa using h
  have hprev := st223_p2
  have hstep := st223_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p4 : ((709874873887/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT223 (i+1))
      = (∑ i ∈ Finset.range 3, stT223 (i+1)) + stT223 4 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 3
    simpa using h
  have hprev := st223_p3
  have hstep := st223_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p5 : ((236996189423/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT223 (i+1))
      = (∑ i ∈ Finset.range 4, stT223 (i+1)) + stT223 5 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 4
    simpa using h
  have hprev := st223_p4
  have hstep := st223_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p6 : ((454342344703/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT223 (i+1))
      = (∑ i ∈ Finset.range 5, stT223 (i+1)) + stT223 6 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 5
    simpa using h
  have hprev := st223_p5
  have hstep := st223_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p7 : ((3014536497767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT223 (i+1))
      = (∑ i ∈ Finset.range 6, stT223 (i+1)) + stT223 7 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 6
    simpa using h
  have hprev := st223_p6
  have hstep := st223_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p8 : ((7745367258677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT223 (i+1))
      = (∑ i ∈ Finset.range 7, stT223 (i+1)) + stT223 8 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 7
    simpa using h
  have hprev := st223_p7
  have hstep := st223_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p9 : ((746214301369/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT223 (i+1))
      = (∑ i ∈ Finset.range 8, stT223 (i+1)) + stT223 9 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 8
    simpa using h
  have hprev := st223_p8
  have hstep := st223_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p10 : ((17464905332013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT223 (i+1))
      = (∑ i ∈ Finset.range 9, stT223 (i+1)) + stT223 10 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 9
    simpa using h
  have hprev := st223_p9
  have hstep := st223_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p11 : ((4036487747873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT223 (i+1))
      = (∑ i ∈ Finset.range 10, stT223 (i+1)) + stT223 11 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 10
    simpa using h
  have hprev := st223_p10
  have hstep := st223_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p12 : ((2173740159927/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT223 (i+1))
      = (∑ i ∈ Finset.range 11, stT223 (i+1)) + stT223 12 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 11
    simpa using h
  have hprev := st223_p11
  have hstep := st223_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p13 : ((2451075737727/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT223 (i+1))
      = (∑ i ∈ Finset.range 12, stT223 (i+1)) + stT223 13 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 12
    simpa using h
  have hprev := st223_p12
  have hstep := st223_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p14 : ((22687278961791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT223 (i+1))
      = (∑ i ∈ Finset.range 13, stT223 (i+1)) + stT223 14 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 13
    simpa using h
  have hprev := st223_p13
  have hstep := st223_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p15 : ((4991244314539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT223 (i+1))
      = (∑ i ∈ Finset.range 14, stT223 (i+1)) + stT223 15 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 14
    simpa using h
  have hprev := st223_p14
  have hstep := st223_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p16 : ((4649539177857/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT223 (i+1))
      = (∑ i ∈ Finset.range 15, stT223 (i+1)) + stT223 16 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 15
    simpa using h
  have hprev := st223_p15
  have hstep := st223_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p17 : ((20844113744431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT223 (i+1))
      = (∑ i ∈ Finset.range 16, stT223 (i+1)) + stT223 17 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 16
    simpa using h
  have hprev := st223_p16
  have hstep := st223_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p18 : ((18602528302879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT223 (i+1))
      = (∑ i ∈ Finset.range 17, stT223 (i+1)) + stT223 18 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 17
    simpa using h
  have hprev := st223_p17
  have hstep := st223_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p19 : ((16351716124131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT223 (i+1))
      = (∑ i ∈ Finset.range 18, stT223 (i+1)) + stT223 19 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 18
    simpa using h
  have hprev := st223_p18
  have hstep := st223_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p20 : ((15803000689407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT223 (i+1))
      = (∑ i ∈ Finset.range 19, stT223 (i+1)) + stT223 20 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 19
    simpa using h
  have hprev := st223_p19
  have hstep := st223_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p21 : ((17965938425981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT223 (i+1))
      = (∑ i ∈ Finset.range 20, stT223 (i+1)) + stT223 21 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 20
    simpa using h
  have hprev := st223_p20
  have hstep := st223_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p22 : ((678565849717/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT223 (i+1))
      = (∑ i ∈ Finset.range 21, stT223 (i+1)) + stT223 22 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 21
    simpa using h
  have hprev := st223_p21
  have hstep := st223_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p23 : ((16966391943013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT223 (i+1))
      = (∑ i ∈ Finset.range 22, stT223 (i+1)) + stT223 23 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 22
    simpa using h
  have hprev := st223_p22
  have hstep := st223_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p24 : ((4274661497161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT223 (i+1))
      = (∑ i ∈ Finset.range 23, stT223 (i+1)) + stT223 24 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 23
    simpa using h
  have hprev := st223_p23
  have hstep := st223_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p25 : ((4401526497161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT223 (i+1))
      = (∑ i ∈ Finset.range 24, stT223 (i+1)) + stT223 25 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 24
    simpa using h
  have hprev := st223_p24
  have hstep := st223_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p26 : ((64111545457/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT223 (i+1))
      = (∑ i ∈ Finset.range 25, stT223 (i+1)) + stT223 26 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 25
    simpa using h
  have hprev := st223_p25
  have hstep := st223_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p27 : ((71279715211/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT223 (i+1))
      = (∑ i ∈ Finset.range 26, stT223 (i+1)) + stT223 27 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 26
    simpa using h
  have hprev := st223_p26
  have hstep := st223_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p28 : ((1804048992837/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT223 (i+1))
      = (∑ i ∈ Finset.range 27, stT223 (i+1)) + stT223 28 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 27
    simpa using h
  have hprev := st223_p27
  have hstep := st223_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p29 : ((8101552254811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT223 (i+1))
      = (∑ i ∈ Finset.range 28, stT223 (i+1)) + stT223 29 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 28
    simpa using h
  have hprev := st223_p28
  have hstep := st223_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p30 : ((7713012448307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT223 (i+1))
      = (∑ i ∈ Finset.range 29, stT223 (i+1)) + stT223 30 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 29
    simpa using h
  have hprev := st223_p29
  have hstep := st223_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p31 : ((16424244213219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT223 (i+1))
      = (∑ i ∈ Finset.range 30, stT223 (i+1)) + stT223 31 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 30
    simpa using h
  have hprev := st223_p30
  have hstep := st223_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p32 : ((18161869802919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT223 (i+1))
      = (∑ i ∈ Finset.range 31, stT223 (i+1)) + stT223 32 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 31
    simpa using h
  have hprev := st223_p31
  have hstep := st223_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p33 : ((19769030800263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT223 (i+1))
      = (∑ i ∈ Finset.range 32, stT223 (i+1)) + stT223 33 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 32
    simpa using h
  have hprev := st223_p32
  have hstep := st223_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p34 : ((10501113389599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT223 (i+1))
      = (∑ i ∈ Finset.range 33, stT223 (i+1)) + stT223 34 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 33
    simpa using h
  have hprev := st223_p33
  have hstep := st223_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p35 : ((10993172190247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT223 (i+1))
      = (∑ i ∈ Finset.range 34, stT223 (i+1)) + stT223 35 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 34
    simpa using h
  have hprev := st223_p34
  have hstep := st223_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p36 : ((2295815399177/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT223 (i+1))
      = (∑ i ∈ Finset.range 35, stT223 (i+1)) + stT223 36 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 35
    simpa using h
  have hprev := st223_p35
  have hstep := st223_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p37 : ((12066283562861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT223 (i+1))
      = (∑ i ∈ Finset.range 36, stT223 (i+1)) + stT223 37 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 36
    simpa using h
  have hprev := st223_p36
  have hstep := st223_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p38 : ((12800497619261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT223 (i+1))
      = (∑ i ∈ Finset.range 37, stT223 (i+1)) + stT223 38 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 37
    simpa using h
  have hprev := st223_p37
  have hstep := st223_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p39 : ((2720004725537/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT223 (i+1))
      = (∑ i ∈ Finset.range 38, stT223 (i+1)) + stT223 39 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 38
    simpa using h
  have hprev := st223_p38
  have hstep := st223_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p40 : ((1421014130059/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT223 (i+1))
      = (∑ i ∈ Finset.range 39, stT223 (i+1)) + stT223 40 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 39
    simpa using h
  have hprev := st223_p39
  have hstep := st223_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p41 : ((14291884176907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT223 (i+1))
      = (∑ i ∈ Finset.range 40, stT223 (i+1)) + stT223 41 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 40
    simpa using h
  have hprev := st223_p40
  have hstep := st223_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p42 : ((13735981489863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT223 (i+1))
      = (∑ i ∈ Finset.range 41, stT223 (i+1)) + stT223 42 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 41
    simpa using h
  have hprev := st223_p41
  have hstep := st223_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p43 : ((13000990087387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT223 (i+1))
      = (∑ i ∈ Finset.range 42, stT223 (i+1)) + stT223 43 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 42
    simpa using h
  have hprev := st223_p42
  have hstep := st223_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p44 : ((25784543721107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT223 (i+1))
      = (∑ i ∈ Finset.range 43, stT223 (i+1)) + stT223 44 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 43
    simpa using h
  have hprev := st223_p43
  have hstep := st223_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p45 : ((27130813769473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT223 (i+1))
      = (∑ i ∈ Finset.range 44, stT223 (i+1)) + stT223 45 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 44
    simpa using h
  have hprev := st223_p44
  have hstep := st223_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p46 : ((2800252419391/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT223 (i+1))
      = (∑ i ∈ Finset.range 45, stT223 (i+1)) + stT223 46 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 45
    simpa using h
  have hprev := st223_p45
  have hstep := st223_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p47 : ((672553439909/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT223 (i+1))
      = (∑ i ∈ Finset.range 46, stT223 (i+1)) + stT223 47 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 46
    simpa using h
  have hprev := st223_p46
  have hstep := st223_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p48 : ((3246710567623/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT223 (i+1))
      = (∑ i ∈ Finset.range 47, stT223 (i+1)) + stT223 48 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 47
    simpa using h
  have hprev := st223_p47
  have hstep := st223_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p49 : ((27165131326407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT223 (i+1))
      = (∑ i ∈ Finset.range 48, stT223 (i+1)) + stT223 49 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 48
    simpa using h
  have hprev := st223_p48
  have hstep := st223_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p50 : ((3460742766713/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT223 (i+1))
      = (∑ i ∈ Finset.range 49, stT223 (i+1)) + stT223 50 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 49
    simpa using h
  have hprev := st223_p49
  have hstep := st223_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p51 : ((6572539709069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT223 (i+1))
      = (∑ i ∈ Finset.range 50, stT223 (i+1)) + stT223 51 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 50
    simpa using h
  have hprev := st223_p50
  have hstep := st223_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p52 : ((13350853010263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT223 (i+1))
      = (∑ i ∈ Finset.range 51, stT223 (i+1)) + stT223 52 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 51
    simpa using h
  have hprev := st223_p51
  have hstep := st223_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p53 : ((6922894495129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT223 (i+1))
      = (∑ i ∈ Finset.range 52, stT223 (i+1)) + stT223 53 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 52
    simpa using h
  have hprev := st223_p52
  have hstep := st223_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p54 : ((3297084910793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT223 (i+1))
      = (∑ i ∈ Finset.range 53, stT223 (i+1)) + stT223 54 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 53
    simpa using h
  have hprev := st223_p53
  have hstep := st223_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p55 : ((2685136157991/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT223 (i+1))
      = (∑ i ∈ Finset.range 54, stT223 (i+1)) + stT223 55 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 54
    simpa using h
  have hprev := st223_p54
  have hstep := st223_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p56 : ((1375574503119/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT223 (i+1))
      = (∑ i ∈ Finset.range 55, stT223 (i+1)) + stT223 56 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 55
    simpa using h
  have hprev := st223_p55
  have hstep := st223_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p57 : ((13113811437273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT223 (i+1))
      = (∑ i ∈ Finset.range 56, stT223 (i+1)) + stT223 57 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 56
    simpa using h
  have hprev := st223_p56
  have hstep := st223_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p58 : ((13693632925329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT223 (i+1))
      = (∑ i ∈ Finset.range 57, stT223 (i+1)) + stT223 58 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 57
    simpa using h
  have hprev := st223_p57
  have hstep := st223_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p59 : ((3358203558891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT223 (i+1))
      = (∑ i ∈ Finset.range 58, stT223 (i+1)) + stT223 59 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 58
    simpa using h
  have hprev := st223_p58
  have hstep := st223_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p60 : ((13308219017119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT223 (i+1))
      = (∑ i ∈ Finset.range 59, stT223 (i+1)) + stT223 60 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 59
    simpa using h
  have hprev := st223_p59
  have hstep := st223_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p61 : ((13739207530703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT223 (i+1))
      = (∑ i ∈ Finset.range 60, stT223 (i+1)) + stT223 61 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 60
    simpa using h
  have hprev := st223_p60
  have hstep := st223_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p62 : ((13142166890483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT223 (i+1))
      = (∑ i ∈ Finset.range 61, stT223 (i+1)) + stT223 62 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 61
    simpa using h
  have hprev := st223_p61
  have hstep := st223_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p63 : ((27540239856411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT223 (i+1))
      = (∑ i ∈ Finset.range 62, stT223 (i+1)) + stT223 63 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 62
    simpa using h
  have hprev := st223_p62
  have hstep := st223_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p64 : ((13207066352763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT223 (i+1))
      = (∑ i ∈ Finset.range 63, stT223 (i+1)) + stT223 64 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 63
    simpa using h
  have hprev := st223_p63
  have hstep := st223_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p65 : ((27308875619181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT223 (i+1))
      = (∑ i ∈ Finset.range 64, stT223 (i+1)) + stT223 65 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 64
    simpa using h
  have hprev := st223_p64
  have hstep := st223_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p66 : ((26673019395801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT223 (i+1))
      = (∑ i ∈ Finset.range 65, stT223 (i+1)) + stT223 66 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 65
    simpa using h
  have hprev := st223_p65
  have hstep := st223_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p67 : ((27069908682193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT223 (i+1))
      = (∑ i ∈ Finset.range 66, stT223 (i+1)) + stT223 67 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 66
    simpa using h
  have hprev := st223_p66
  have hstep := st223_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p68 : ((13433088698757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT223 (i+1))
      = (∑ i ∈ Finset.range 67, stT223 (i+1)) + stT223 68 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 67
    simpa using h
  have hprev := st223_p67
  have hstep := st223_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p69 : ((6733017039357/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT223 (i+1))
      = (∑ i ∈ Finset.range 68, stT223 (i+1)) + stT223 69 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 68
    simpa using h
  have hprev := st223_p68
  have hstep := st223_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p70 : ((6736670253739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT223 (i+1))
      = (∑ i ∈ Finset.range 69, stT223 (i+1)) + stT223 70 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 69
    simpa using h
  have hprev := st223_p69
  have hstep := st223_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p71 : ((2690645741263/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT223 (i+1))
      = (∑ i ∈ Finset.range 70, stT223 (i+1)) + stT223 71 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 70
    simpa using h
  have hprev := st223_p70
  have hstep := st223_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p72 : ((13459800083651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT223 (i+1))
      = (∑ i ∈ Finset.range 71, stT223 (i+1)) + stT223 72 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 71
    simpa using h
  have hprev := st223_p71
  have hstep := st223_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p73 : ((2698327988899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT223 (i+1))
      = (∑ i ∈ Finset.range 72, stT223 (i+1)) + stT223 73 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 72
    simpa using h
  have hprev := st223_p72
  have hstep := st223_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p74 : ((53591381951/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT223 (i+1))
      = (∑ i ∈ Finset.range 73, stT223 (i+1)) + stT223 74 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 73
    simpa using h
  have hprev := st223_p73
  have hstep := st223_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p75 : ((271481816257/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT223 (i+1))
      = (∑ i ∈ Finset.range 74, stT223 (i+1)) + stT223 75 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 74
    simpa using h
  have hprev := st223_p74
  have hstep := st223_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p76 : ((1330000775659/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT223 (i+1))
      = (∑ i ∈ Finset.range 75, stT223 (i+1)) + stT223 76 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 75
    simpa using h
  have hprev := st223_p75
  have hstep := st223_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p77 : ((218843303551/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT223 (i+1))
      = (∑ i ∈ Finset.range 76, stT223 (i+1)) + stT223 77 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 76
    simpa using h
  have hprev := st223_p76
  have hstep := st223_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p78 : ((26409469405223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT223 (i+1))
      = (∑ i ∈ Finset.range 77, stT223 (i+1)) + stT223 78 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 77
    simpa using h
  have hprev := st223_p77
  have hstep := st223_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p79 : ((27490320234557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT223 (i+1))
      = (∑ i ∈ Finset.range 78, stT223 (i+1)) + stT223 79 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 78
    simpa using h
  have hprev := st223_p78
  have hstep := st223_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p80 : ((5274788632189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT223 (i+1))
      = (∑ i ∈ Finset.range 79, stT223 (i+1)) + stT223 80 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 79
    simpa using h
  have hprev := st223_p79
  have hstep := st223_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p81 : ((27385360837581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT223 (i+1))
      = (∑ i ∈ Finset.range 80, stT223 (i+1)) + stT223 81 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 80
    simpa using h
  have hprev := st223_p80
  have hstep := st223_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p82 : ((26641732112237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT223 (i+1))
      = (∑ i ∈ Finset.range 81, stT223 (i+1)) + stT223 82 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 81
    simpa using h
  have hprev := st223_p81
  have hstep := st223_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p83 : ((26966251067179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT223 (i+1))
      = (∑ i ∈ Finset.range 82, stT223 (i+1)) + stT223 83 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 82
    simpa using h
  have hprev := st223_p82
  have hstep := st223_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p84 : ((5430313197459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT223 (i+1))
      = (∑ i ∈ Finset.range 83, stT223 (i+1)) + stT223 84 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 83
    simpa using h
  have hprev := st223_p83
  have hstep := st223_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p85 : ((26475213254697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT223 (i+1))
      = (∑ i ∈ Finset.range 84, stT223 (i+1)) + stT223 85 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 84
    simpa using h
  have hprev := st223_p84
  have hstep := st223_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p86 : ((27482765340379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT223 (i+1))
      = (∑ i ∈ Finset.range 85, stT223 (i+1)) + stT223 86 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 85
    simpa using h
  have hprev := st223_p85
  have hstep := st223_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p87 : ((13215913822121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT223 (i+1))
      = (∑ i ∈ Finset.range 86, stT223 (i+1)) + stT223 87 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 86
    simpa using h
  have hprev := st223_p86
  have hstep := st223_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p88 : ((6795078280667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT223 (i+1))
      = (∑ i ∈ Finset.range 87, stT223 (i+1)) + stT223 88 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 87
    simpa using h
  have hprev := st223_p87
  have hstep := st223_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p89 : ((13507435907411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT223 (i+1))
      = (∑ i ∈ Finset.range 88, stT223 (i+1)) + stT223 89 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 88
    simpa using h
  have hprev := st223_p88
  have hstep := st223_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p90 : ((26515688155091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT223 (i+1))
      = (∑ i ∈ Finset.range 89, stT223 (i+1)) + stT223 90 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 89
    simpa using h
  have hprev := st223_p89
  have hstep := st223_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p91 : ((27481152477671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT223 (i+1))
      = (∑ i ∈ Finset.range 90, stT223 (i+1)) + stT223 91 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 90
    simpa using h
  have hprev := st223_p90
  have hstep := st223_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p92 : ((13243224608483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT223 (i+1))
      = (∑ i ∈ Finset.range 91, stT223 (i+1)) + stT223 92 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 91
    simpa using h
  have hprev := st223_p91
  have hstep := st223_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p93 : ((216125331939/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT223 (i+1))
      = (∑ i ∈ Finset.range 92, stT223 (i+1)) + stT223 93 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 92
    simpa using h
  have hprev := st223_p92
  have hstep := st223_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p94 : ((13620793958397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT223 (i+1))
      = (∑ i ∈ Finset.range 93, stT223 (i+1)) + stT223 94 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 93
    simpa using h
  have hprev := st223_p93
  have hstep := st223_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p95 : ((206068208679/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT223 (i+1))
      = (∑ i ∈ Finset.range 94, stT223 (i+1)) + stT223 95 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 94
    simpa using h
  have hprev := st223_p94
  have hstep := st223_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p96 : ((1710527666877/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT223 (i+1))
      = (∑ i ∈ Finset.range 95, stT223 (i+1)) + stT223 96 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 95
    simpa using h
  have hprev := st223_p95
  have hstep := st223_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p97 : ((52500102813/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT223 (i+1))
      = (∑ i ∈ Finset.range 96, stT223 (i+1)) + stT223 97 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 96
    simpa using h
  have hprev := st223_p96
  have hstep := st223_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p98 : ((26531112459007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT223 (i+1))
      = (∑ i ∈ Finset.range 97, stT223 (i+1)) + stT223 98 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 97
    simpa using h
  have hprev := st223_p97
  have hstep := st223_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p99 : ((5495676790479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT223 (i+1))
      = (∑ i ∈ Finset.range 98, stT223 (i+1)) + stT223 99 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 98
    simpa using h
  have hprev := st223_p98
  have hstep := st223_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p100 : ((5326197990479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT223 (i+1))
      = (∑ i ∈ Finset.range 99, stT223 (i+1)) + stT223 100 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 99
    simpa using h
  have hprev := st223_p99
  have hstep := st223_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p101 : ((667967437219/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT223 (i+1))
      = (∑ i ∈ Finset.range 100, stT223 (i+1)) + stT223 101 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 100
    simpa using h
  have hprev := st223_p100
  have hstep := st223_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p102 : ((27466576310947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT223 (i+1))
      = (∑ i ∈ Finset.range 101, stT223 (i+1)) + stT223 102 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 101
    simpa using h
  have hprev := st223_p101
  have hstep := st223_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p103 : ((26512171878327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT223 (i+1))
      = (∑ i ∈ Finset.range 102, stT223 (i+1)) + stT223 103 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 102
    simpa using h
  have hprev := st223_p102
  have hstep := st223_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p104 : ((26832099831447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT223 (i+1))
      = (∑ i ∈ Finset.range 103, stT223 (i+1)) + stT223 104 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 103
    simpa using h
  have hprev := st223_p103
  have hstep := st223_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p105 : ((27442035379647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT223 (i+1))
      = (∑ i ∈ Finset.range 104, stT223 (i+1)) + stT223 105 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 104
    simpa using h
  have hprev := st223_p104
  have hstep := st223_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p106 : ((26479181113413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT223 (i+1))
      = (∑ i ∈ Finset.range 105, stT223 (i+1)) + stT223 106 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 105
    simpa using h
  have hprev := st223_p105
  have hstep := st223_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p107 : ((26847469826709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT223 (i+1))
      = (∑ i ∈ Finset.range 106, stT223 (i+1)) + stT223 107 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 106
    simpa using h
  have hprev := st223_p106
  have hstep := st223_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p108 : ((27449680517709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT223 (i+1))
      = (∑ i ∈ Finset.range 107, stT223 (i+1)) + stT223 108 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 107
    simpa using h
  have hprev := st223_p107
  have hstep := st223_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p109 : ((26509362595269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT223 (i+1))
      = (∑ i ∈ Finset.range 108, stT223 (i+1)) + stT223 109 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 108
    simpa using h
  have hprev := st223_p108
  have hstep := st223_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p110 : ((26767296949357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT223 (i+1))
      = (∑ i ∈ Finset.range 109, stT223 (i+1)) + stT223 110 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 109
    simpa using h
  have hprev := st223_p109
  have hstep := st223_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p111 : ((5496000750829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT223 (i+1))
      = (∑ i ∈ Finset.range 110, stT223 (i+1)) + stT223 111 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 110
    simpa using h
  have hprev := st223_p110
  have hstep := st223_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p112 : ((26617273585521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT223 (i+1))
      = (∑ i ∈ Finset.range 111, stT223 (i+1)) + stT223 112 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 111
    simpa using h
  have hprev := st223_p111
  have hstep := st223_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p113 : ((26608925627367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT223 (i+1))
      = (∑ i ∈ Finset.range 112, stT223 (i+1)) + stT223 113 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 112
    simpa using h
  have hprev := st223_p112
  have hstep := st223_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p114 : ((27476853327357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT223 (i+1))
      = (∑ i ∈ Finset.range 113, stT223 (i+1)) + stT223 114 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 113
    simpa using h
  have hprev := st223_p113
  have hstep := st223_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p115 : ((6708264600723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT223 (i+1))
      = (∑ i ∈ Finset.range 114, stT223 (i+1)) + stT223 115 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 114
    simpa using h
  have hprev := st223_p114
  have hstep := st223_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p116 : ((42288127819/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT223 (i+1))
      = (∑ i ∈ Finset.range 115, stT223 (i+1)) + stT223 116 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 115
    simpa using h
  have hprev := st223_p115
  have hstep := st223_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p117 : ((218795140139/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT223 (i+1))
      = (∑ i ∈ Finset.range 116, stT223 (i+1)) + stT223 117 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 116
    simpa using h
  have hprev := st223_p116
  have hstep := st223_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p118 : ((1085881047897/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT223 (i+1))
      = (∑ i ∈ Finset.range 117, stT223 (i+1)) + stT223 118 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 117
    simpa using h
  have hprev := st223_p117
  have hstep := st223_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p119 : ((6589318147911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT223 (i+1))
      = (∑ i ∈ Finset.range 118, stT223 (i+1)) + stT223 119 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 118
    simpa using h
  have hprev := st223_p118
  have hstep := st223_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p120 : ((3378701765853/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT223 (i+1))
      = (∑ i ∈ Finset.range 119, stT223 (i+1)) + stT223 120 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 119
    simpa using h
  have hprev := st223_p119
  have hstep := st223_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p121 : ((13717793678607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT223 (i+1))
      = (∑ i ∈ Finset.range 120, stT223 (i+1)) + stT223 121 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 120
    simpa using h
  have hprev := st223_p120
  have hstep := st223_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p122 : ((3318492609471/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT223 (i+1))
      = (∑ i ∈ Finset.range 121, stT223 (i+1)) + stT223 122 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 121
    simpa using h
  have hprev := st223_p121
  have hstep := st223_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p123 : ((664851936879/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT223 (i+1))
      = (∑ i ∈ Finset.range 122, stT223 (i+1)) + stT223 123 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 122
    simpa using h
  have hprev := st223_p122
  have hstep := st223_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p124 : ((3431943778107/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT223 (i+1))
      = (∑ i ∈ Finset.range 123, stT223 (i+1)) + stT223 124 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 123
    simpa using h
  have hprev := st223_p123
  have hstep := st223_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p125 : ((6755399477203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT223 (i+1))
      = (∑ i ∈ Finset.range 124, stT223 (i+1)) + stT223 125 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 124
    simpa using h
  have hprev := st223_p124
  have hstep := st223_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p126 : ((6586868064907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT223 (i+1))
      = (∑ i ∈ Finset.range 125, stT223 (i+1)) + stT223 126 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 125
    simpa using h
  have hprev := st223_p125
  have hstep := st223_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p127 : ((845158709833/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT223 (i+1))
      = (∑ i ∈ Finset.range 126, stT223 (i+1)) + stT223 127 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 126
    simpa using h
  have hprev := st223_p126
  have hstep := st223_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p128 : ((6864843972487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT223 (i+1))
      = (∑ i ∈ Finset.range 127, stT223 (i+1)) + stT223 128 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 127
    simpa using h
  have hprev := st223_p127
  have hstep := st223_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p129 : ((3328060808537/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT223 (i+1))
      = (∑ i ∈ Finset.range 128, stT223 (i+1)) + stT223 129 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 128
    simpa using h
  have hprev := st223_p128
  have hstep := st223_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p130 : ((26474280466897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT223 (i+1))
      = (∑ i ∈ Finset.range 129, stT223 (i+1)) + stT223 130 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 129
    simpa using h
  have hprev := st223_p129
  have hstep := st223_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p131 : ((27347434907081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT223 (i+1))
      = (∑ i ∈ Finset.range 130, stT223 (i+1)) + stT223 131 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 130
    simpa using h
  have hprev := st223_p130
  have hstep := st223_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p132 : ((27268293916867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT223 (i+1))
      = (∑ i ∈ Finset.range 131, stT223 (i+1)) + stT223 132 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 131
    simpa using h
  have hprev := st223_p131
  have hstep := st223_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p133 : ((26418985685167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT223 (i+1))
      = (∑ i ∈ Finset.range 132, stT223 (i+1)) + stT223 133 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 132
    simpa using h
  have hprev := st223_p132
  have hstep := st223_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p134 : ((5335316669591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT223 (i+1))
      = (∑ i ∈ Finset.range 133, stT223 (i+1)) + stT223 134 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 133
    simpa using h
  have hprev := st223_p133
  have hstep := st223_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p135 : ((27472558852697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT223 (i+1))
      = (∑ i ∈ Finset.range 134, stT223 (i+1)) + stT223 135 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 134
    simpa using h
  have hprev := st223_p134
  have hstep := st223_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p136 : ((5417597392417/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT223 (i+1))
      = (∑ i ∈ Finset.range 135, stT223 (i+1)) + stT223 136 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 135
    simpa using h
  have hprev := st223_p135
  have hstep := st223_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p137 : ((26349908794601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT223 (i+1))
      = (∑ i ∈ Finset.range 136, stT223 (i+1)) + stT223 137 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 136
    simpa using h
  have hprev := st223_p136
  have hstep := st223_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p138 : ((26815628398433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT223 (i+1))
      = (∑ i ∈ Finset.range 137, stT223 (i+1)) + stT223 138 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 137
    simpa using h
  have hprev := st223_p137
  have hstep := st223_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p139 : ((27506753185533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT223 (i+1))
      = (∑ i ∈ Finset.range 138, stT223 (i+1)) + stT223 139 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 138
    simpa using h
  have hprev := st223_p138
  have hstep := st223_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p140 : ((13498943947749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT223 (i+1))
      = (∑ i ∈ Finset.range 139, stT223 (i+1)) + stT223 140 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 139
    simpa using h
  have hprev := st223_p139
  have hstep := st223_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p141 : ((13166908678709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT223 (i+1))
      = (∑ i ∈ Finset.range 140, stT223 (i+1)) + stT223 141 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 140
    simpa using h
  have hprev := st223_p140
  have hstep := st223_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p142 : ((26853338370079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT223 (i+1))
      = (∑ i ∈ Finset.range 141, stT223 (i+1)) + stT223 142 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 141
    simpa using h
  have hprev := st223_p141
  have hstep := st223_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p143 : ((27513015397957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT223 (i+1))
      = (∑ i ∈ Finset.range 142, stT223 (i+1)) + stT223 143 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 142
    simpa using h
  have hprev := st223_p142
  have hstep := st223_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p144 : ((27011997497143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT223 (i+1))
      = (∑ i ∈ Finset.range 143, stT223 (i+1)) + stT223 144 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 143
    simpa using h
  have hprev := st223_p143
  have hstep := st223_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p145 : ((6583708423557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT223 (i+1))
      = (∑ i ∈ Finset.range 144, stT223 (i+1)) + stT223 145 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 144
    simpa using h
  have hprev := st223_p144
  have hstep := st223_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p146 : ((26787855567573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT223 (i+1))
      = (∑ i ∈ Finset.range 145, stT223 (i+1)) + stT223 146 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 145
    simpa using h
  have hprev := st223_p145
  have hstep := st223_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p147 : ((27499161736191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT223 (i+1))
      = (∑ i ∈ Finset.range 146, stT223 (i+1)) + stT223 147 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 146
    simpa using h
  have hprev := st223_p146
  have hstep := st223_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p148 : ((27125563364701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT223 (i+1))
      = (∑ i ∈ Finset.range 147, stT223 (i+1)) + stT223 148 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 147
    simpa using h
  have hprev := st223_p147
  have hstep := st223_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p149 : ((26371812578461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT223 (i+1))
      = (∑ i ∈ Finset.range 148, stT223 (i+1)) + stT223 149 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 148
    simpa using h
  have hprev := st223_p148
  have hstep := st223_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p150 : ((26631320318637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT223 (i+1))
      = (∑ i ∈ Finset.range 149, stT223 (i+1)) + stT223 150 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 149
    simpa using h
  have hprev := st223_p149
  have hstep := st223_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p151 : ((27422805644709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT223 (i+1))
      = (∑ i ∈ Finset.range 150, stT223 (i+1)) + stT223 151 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 150
    simpa using h
  have hprev := st223_p150
  have hstep := st223_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p152 : ((27313113832113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT223 (i+1))
      = (∑ i ∈ Finset.range 151, stT223 (i+1)) + stT223 152 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 151
    simpa using h
  have hprev := st223_p151
  have hstep := st223_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p153 : ((13252458555857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT223 (i+1))
      = (∑ i ∈ Finset.range 152, stT223 (i+1)) + stT223 153 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 152
    simpa using h
  have hprev := st223_p152
  have hstep := st223_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p154 : ((13215859686843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT223 (i+1))
      = (∑ i ∈ Finset.range 153, stT223 (i+1)) + stT223 154 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 153
    simpa using h
  have hprev := st223_p153
  have hstep := st223_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p155 : ((13607914093619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT223 (i+1))
      = (∑ i ∈ Finset.range 154, stT223 (i+1)) + stT223 155 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 154
    simpa using h
  have hprev := st223_p154
  have hstep := st223_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p156 : ((13747058920499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT223 (i+1))
      = (∑ i ∈ Finset.range 155, stT223 (i+1)) + stT223 156 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 155
    simpa using h
  have hprev := st223_p155
  have hstep := st223_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p157 : ((26794041511207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT223 (i+1))
      = (∑ i ∈ Finset.range 156, stT223 (i+1)) + stT223 157 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 156
    simpa using h
  have hprev := st223_p156
  have hstep := st223_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p158 : ((26308848984841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT223 (i+1))
      = (∑ i ∈ Finset.range 157, stT223 (i+1)) + stT223 158 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 157
    simpa using h
  have hprev := st223_p157
  have hstep := st223_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p159 : ((26850026987241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT223 (i+1))
      = (∑ i ∈ Finset.range 158, stT223 (i+1)) + stT223 159 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 158
    simpa using h
  have hprev := st223_p158
  have hstep := st223_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p160 : ((27511946693871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT223 (i+1))
      = (∑ i ∈ Finset.range 159, stT223 (i+1)) + stT223 160 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 159
    simpa using h
  have hprev := st223_p159
  have hstep := st223_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p161 : ((27207152645731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT223 (i+1))
      = (∑ i ∈ Finset.range 160, stT223 (i+1)) + stT223 161 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 160
    simpa using h
  have hprev := st223_p160
  have hstep := st223_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p162 : ((26438220379981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT223 (i+1))
      = (∑ i ∈ Finset.range 161, stT223 (i+1)) + stT223 162 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 161
    simpa using h
  have hprev := st223_p161
  have hstep := st223_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p163 : ((26444903154301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT223 (i+1))
      = (∑ i ∈ Finset.range 162, stT223 (i+1)) + stT223 163 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 162
    simpa using h
  have hprev := st223_p162
  have hstep := st223_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p164 : ((5442085888141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT223 (i+1))
      = (∑ i ∈ Finset.range 163, stT223 (i+1)) + stT223 164 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 163
    simpa using h
  have hprev := st223_p163
  have hstep := st223_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p165 : ((27523190233707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT223 (i+1))
      = (∑ i ∈ Finset.range 164, stT223 (i+1)) + stT223 165 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 164
    simpa using h
  have hprev := st223_p164
  have hstep := st223_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p166 : ((2689914387363/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT223 (i+1))
      = (∑ i ∈ Finset.range 165, stT223 (i+1)) + stT223 166 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 165
    simpa using h
  have hprev := st223_p165
  have hstep := st223_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p167 : ((13154254001487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT223 (i+1))
      = (∑ i ∈ Finset.range 166, stT223 (i+1)) + stT223 167 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 166
    simpa using h
  have hprev := st223_p166
  have hstep := st223_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p168 : ((2665309096557/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT223 (i+1))
      = (∑ i ∈ Finset.range 167, stT223 (i+1)) + stT223 168 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 167
    simpa using h
  have hprev := st223_p167
  have hstep := st223_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p169 : ((685111351509/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT223 (i+1))
      = (∑ i ∈ Finset.range 168, stT223 (i+1)) + stT223 169 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 168
    simpa using h
  have hprev := st223_p168
  have hstep := st223_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p170 : ((1714666356529/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT223 (i+1))
      = (∑ i ∈ Finset.range 169, stT223 (i+1)) + stT223 170 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 169
    simpa using h
  have hprev := st223_p169
  have hstep := st223_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p171 : ((834518306707/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT223 (i+1))
      = (∑ i ∈ Finset.range 170, stT223 (i+1)) + stT223 171 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 170
    simpa using h
  have hprev := st223_p170
  have hstep := st223_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p172 : ((1643204113067/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT223 (i+1))
      = (∑ i ∈ Finset.range 171, stT223 (i+1)) + stT223 172 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 171
    simpa using h
  have hprev := st223_p171
  have hstep := st223_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p173 : ((6698125865683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT223 (i+1))
      = (∑ i ∈ Finset.range 172, stT223 (i+1)) + stT223 173 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 172
    simpa using h
  have hprev := st223_p172
  have hstep := st223_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p174 : ((6870035958653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT223 (i+1))
      = (∑ i ∈ Finset.range 173, stT223 (i+1)) + stT223 174 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 173
    simpa using h
  have hprev := st223_p173
  have hstep := st223_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p175 : ((2737343840883/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT223 (i+1))
      = (∑ i ∈ Finset.range 174, stT223 (i+1)) + stT223 175 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 174
    simpa using h
  have hprev := st223_p174
  have hstep := st223_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p176 : ((5325815575487/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT223 (i+1))
      = (∑ i ∈ Finset.range 175, stT223 (i+1)) + stT223 176 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 175
    simpa using h
  have hprev := st223_p175
  have hstep := st223_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p177 : ((26291389939627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT223 (i+1))
      = (∑ i ∈ Finset.range 176, stT223 (i+1)) + stT223 177 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 176
    simpa using h
  have hprev := st223_p176
  have hstep := st223_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p178 : ((26824023157909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT223 (i+1))
      = (∑ i ∈ Finset.range 177, stT223 (i+1)) + stT223 178 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 177
    simpa using h
  have hprev := st223_p177
  have hstep := st223_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p179 : ((1718170247899/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT223 (i+1))
      = (∑ i ∈ Finset.range 178, stT223 (i+1)) + stT223 179 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 178
    simpa using h
  have hprev := st223_p178
  have hstep := st223_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p180 : ((684657601573/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT223 (i+1))
      = (∑ i ∈ Finset.range 179, stT223 (i+1)) + stT223 180 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 179
    simpa using h
  have hprev := st223_p179
  have hstep := st223_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p181 : ((1066281371851/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT223 (i+1))
      = (∑ i ∈ Finset.range 180, stT223 (i+1)) + stT223 181 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 180
    simpa using h
  have hprev := st223_p180
  have hstep := st223_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p182 : ((1051112580101/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT223 (i+1))
      = (∑ i ∈ Finset.range 181, stT223 (i+1)) + stT223 182 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 181
    simpa using h
  have hprev := st223_p181
  have hstep := st223_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p183 : ((26745432401147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT223 (i+1))
      = (∑ i ∈ Finset.range 182, stT223 (i+1)) + stT223 183 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 182
    simpa using h
  have hprev := st223_p182
  have hstep := st223_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p184 : ((13721483512197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT223 (i+1))
      = (∑ i ∈ Finset.range 183, stT223 (i+1)) + stT223 184 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 183
    simpa using h
  have hprev := st223_p183
  have hstep := st223_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p185 : ((6866742388963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT223 (i+1))
      = (∑ i ∈ Finset.range 184, stT223 (i+1)) + stT223 185 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 184
    simpa using h
  have hprev := st223_p184
  have hstep := st223_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p186 : ((6697991056507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT223 (i+1))
      = (∑ i ∈ Finset.range 185, stT223 (i+1)) + stT223 186 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 185
    simpa using h
  have hprev := st223_p185
  have hstep := st223_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p187 : ((821234460409/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT223 (i+1))
      = (∑ i ∈ Finset.range 186, stT223 (i+1)) + stT223 187 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 186
    simpa using h
  have hprev := st223_p186
  have hstep := st223_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p188 : ((3321515445877/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT223 (i+1))
      = (∑ i ∈ Finset.range 187, stT223 (i+1)) + stT223 188 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 187
    simpa using h
  have hprev := st223_p187
  have hstep := st223_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p189 : ((3412406167693/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT223 (i+1))
      = (∑ i ∈ Finset.range 188, stT223 (i+1)) + stT223 189 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 188
    simpa using h
  have hprev := st223_p188
  have hstep := st223_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p190 : ((3445099743633/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT223 (i+1))
      = (∑ i ∈ Finset.range 189, stT223 (i+1)) + stT223 190 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 189
    simpa using h
  have hprev := st223_p189
  have hstep := st223_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p191 : ((27040826100439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT223 (i+1))
      = (∑ i ∈ Finset.range 190, stT223 (i+1)) + stT223 191 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 190
    simpa using h
  have hprev := st223_p190
  have hstep := st223_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p192 : ((5274958502787/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT223 (i+1))
      = (∑ i ∈ Finset.range 191, stT223 (i+1)) + stT223 192 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 191
    simpa using h
  have hprev := st223_p191
  have hstep := st223_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p193 : ((26362569318439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT223 (i+1))
      = (∑ i ∈ Finset.range 192, stT223 (i+1)) + stT223 193 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 192
    simpa using h
  have hprev := st223_p192
  have hstep := st223_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p194 : ((27013548298661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT223 (i+1))
      = (∑ i ∈ Finset.range 193, stT223 (i+1)) + stT223 194 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 193
    simpa using h
  have hprev := st223_p193
  have hstep := st223_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p195 : ((27555993195837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT223 (i+1))
      = (∑ i ∈ Finset.range 194, stT223 (i+1)) + stT223 195 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 194
    simpa using h
  have hprev := st223_p194
  have hstep := st223_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p196 : ((27357778830837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT223 (i+1))
      = (∑ i ∈ Finset.range 195, stT223 (i+1)) + stT223 196 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 195
    simpa using h
  have hprev := st223_p195
  have hstep := st223_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p197 : ((26653790510563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT223 (i+1))
      = (∑ i ∈ Finset.range 196, stT223 (i+1)) + stT223 197 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 196
    simpa using h
  have hprev := st223_p196
  have hstep := st223_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p198 : ((26254554581983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT223 (i+1))
      = (∑ i ∈ Finset.range 197, stT223 (i+1)) + stT223 198 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 197
    simpa using h
  have hprev := st223_p197
  have hstep := st223_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p199 : ((13305510886381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT223 (i+1))
      = (∑ i ∈ Finset.range 198, stT223 (i+1)) + stT223 199 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 198
    simpa using h
  have hprev := st223_p198
  have hstep := st223_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p200 : ((6829039974191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT223 (i+1))
      = (∑ i ∈ Finset.range 199, stT223 (i+1)) + stT223 200 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 199
    simpa using h
  have hprev := st223_p199
  have hstep := st223_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p201 : ((27580767957479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT223 (i+1))
      = (∑ i ∈ Finset.range 200, stT223 (i+1)) + stT223 201 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 200
    simpa using h
  have hprev := st223_p200
  have hstep := st223_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p202 : ((27115695308263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT223 (i+1))
      = (∑ i ∈ Finset.range 201, stT223 (i+1)) + stT223 202 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 201
    simpa using h
  have hprev := st223_p201
  have hstep := st223_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p203 : ((1652253462277/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT223 (i+1))
      = (∑ i ∈ Finset.range 202, stT223 (i+1)) + stT223 203 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 202
    simpa using h
  have hprev := st223_p202
  have hstep := st223_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p204 : ((1051262015239/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT223 (i+1))
      = (∑ i ∈ Finset.range 203, stT223 (i+1)) + stT223 204 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 203
    simpa using h
  have hprev := st223_p203
  have hstep := st223_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p205 : ((5362889935451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT223 (i+1))
      = (∑ i ∈ Finset.range 204, stT223 (i+1)) + stT223 205 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 204
    simpa using h
  have hprev := st223_p204
  have hstep := st223_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p206 : ((5492165956669/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT223 (i+1))
      = (∑ i ∈ Finset.range 205, stT223 (i+1)) + stT223 206 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 205
    simpa using h
  have hprev := st223_p205
  have hstep := st223_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p207 : ((27536071509537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT223 (i+1))
      = (∑ i ∈ Finset.range 206, stT223 (i+1)) + stT223 207 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 206
    simpa using h
  have hprev := st223_p206
  have hstep := st223_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p208 : ((26965579764513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT223 (i+1))
      = (∑ i ∈ Finset.range 207, stT223 (i+1)) + stT223 208 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 207
    simpa using h
  have hprev := st223_p207
  have hstep := st223_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p209 : ((13173628900579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT223 (i+1))
      = (∑ i ∈ Finset.range 208, stT223 (i+1)) + stT223 209 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 208
    simpa using h
  have hprev := st223_p208
  have hstep := st223_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p210 : ((6579664503947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT223 (i+1))
      = (∑ i ∈ Finset.range 209, stT223 (i+1)) + stT223 210 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 209
    simpa using h
  have hprev := st223_p209
  have hstep := st223_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p211 : ((3363063522313/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT223 (i+1))
      = (∑ i ∈ Finset.range 210, stT223 (i+1)) + stT223 211 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 210
    simpa using h
  have hprev := st223_p210
  have hstep := st223_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p212 : ((6876672326021/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT223 (i+1))
      = (∑ i ∈ Finset.range 211, stT223 (i+1)) + stT223 212 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 211
    simpa using h
  have hprev := st223_p211
  have hstep := st223_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p213 : ((1720015273643/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT223 (i+1))
      = (∑ i ∈ Finset.range 212, stT223 (i+1)) + stT223 213 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 212
    simpa using h
  have hprev := st223_p212
  have hstep := st223_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p214 : ((3367006814629/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT223 (i+1))
      = (∑ i ∈ Finset.range 213, stT223 (i+1)) + stT223 214 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 213
    simpa using h
  have hprev := st223_p213
  have hstep := st223_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p215 : ((822981325771/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT223 (i+1))
      = (∑ i ∈ Finset.range 214, stT223 (i+1)) + stT223 215 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 214
    simpa using h
  have hprev := st223_p214
  have hstep := st223_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p216 : ((13153235950903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT223 (i+1))
      = (∑ i ∈ Finset.range 215, stT223 (i+1)) + stT223 216 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 215
    simpa using h
  have hprev := st223_p215
  have hstep := st223_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p217 : ((13436524340543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT223 (i+1))
      = (∑ i ∈ Finset.range 216, stT223 (i+1)) + stT223 217 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 216
    simpa using h
  have hprev := st223_p216
  have hstep := st223_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p218 : ((6871301150229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT223 (i+1))
      = (∑ i ∈ Finset.range 217, stT223 (i+1)) + stT223 218 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 217
    simpa using h
  have hprev := st223_p217
  have hstep := st223_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p219 : ((3444765253639/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT223 (i+1))
      = (∑ i ∈ Finset.range 218, stT223 (i+1)) + stT223 219 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 218
    simpa using h
  have hprev := st223_p218
  have hstep := st223_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p220 : ((3378340878489/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT223 (i+1))
      = (∑ i ∈ Finset.range 219, stT223 (i+1)) + stT223 220 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 219
    simpa using h
  have hprev := st223_p219
  have hstep := st223_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p221 : ((26394417771277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT223 (i+1))
      = (∑ i ∈ Finset.range 220, stT223 (i+1)) + stT223 221 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 220
    simpa using h
  have hprev := st223_p220
  have hstep := st223_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p222 : ((6562681938919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT223 (i+1))
      = (∑ i ∈ Finset.range 221, stT223 (i+1)) + stT223 222 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 221
    simpa using h
  have hprev := st223_p221
  have hstep := st223_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p223 : ((26724747505763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT223 (i+1))
      = (∑ i ∈ Finset.range 222, stT223 (i+1)) + stT223 223 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 222
    simpa using h
  have hprev := st223_p222
  have hstep := st223_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p224 : ((13688847673971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT223 (i+1))
      = (∑ i ∈ Finset.range 223, stT223 (i+1)) + stT223 224 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 223
    simpa using h
  have hprev := st223_p223
  have hstep := st223_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p225 : ((13807488221997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT223 (i+1))
      = (∑ i ∈ Finset.range 224, stT223 (i+1)) + stT223 225 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 224
    simpa using h
  have hprev := st223_p224
  have hstep := st223_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p226 : ((27225768533557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT223 (i+1))
      = (∑ i ∈ Finset.range 225, stT223 (i+1)) + stT223 226 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 225
    simpa using h
  have hprev := st223_p225
  have hstep := st223_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p227 : ((26562508476633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT223 (i+1))
      = (∑ i ∈ Finset.range 226, stT223 (i+1)) + stT223 227 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 226
    simpa using h
  have hprev := st223_p226
  have hstep := st223_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p228 : ((26215263345057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT223 (i+1))
      = (∑ i ∈ Finset.range 227, stT223 (i+1)) + stT223 228 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 227
    simpa using h
  have hprev := st223_p227
  have hstep := st223_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p229 : ((26487139729889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT223 (i+1))
      = (∑ i ∈ Finset.range 228, stT223 (i+1)) + stT223 229 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 228
    simpa using h
  have hprev := st223_p228
  have hstep := st223_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p230 : ((27136410115729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT223 (i+1))
      = (∑ i ∈ Finset.range 229, stT223 (i+1)) + stT223 230 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 229
    simpa using h
  have hprev := st223_p229
  have hstep := st223_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p231 : ((27598343037907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT223 (i+1))
      = (∑ i ∈ Finset.range 230, stT223 (i+1)) + stT223 231 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 230
    simpa using h
  have hprev := st223_p230
  have hstep := st223_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p232 : ((27477614497603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT223 (i+1))
      = (∑ i ∈ Finset.range 231, stT223 (i+1)) + stT223 232 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 231
    simpa using h
  have hprev := st223_p231
  have hstep := st223_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p233 : ((26881216978561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT223 (i+1))
      = (∑ i ∈ Finset.range 232, stT223 (i+1)) + stT223 233 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 232
    simpa using h
  have hprev := st223_p232
  have hstep := st223_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p234 : ((6579145451959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT223 (i+1))
      = (∑ i ∈ Finset.range 233, stT223 (i+1)) + stT223 234 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 233
    simpa using h
  have hprev := st223_p233
  have hstep := st223_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p235 : ((26256908707903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT223 (i+1))
      = (∑ i ∈ Finset.range 234, stT223 (i+1)) + stT223 235 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 234
    simpa using h
  have hprev := st223_p234
  have hstep := st223_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p236 : ((26748217805119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT223 (i+1))
      = (∑ i ∈ Finset.range 235, stT223 (i+1)) + stT223 236 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 235
    simpa using h
  have hprev := st223_p235
  have hstep := st223_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p237 : ((13690509740261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT223 (i+1))
      = (∑ i ∈ Finset.range 236, stT223 (i+1)) + stT223 237 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 236
    simpa using h
  have hprev := st223_p236
  have hstep := st223_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p238 : ((6909004014673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT223 (i+1))
      = (∑ i ∈ Finset.range 237, stT223 (i+1)) + stT223 238 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 237
    simpa using h
  have hprev := st223_p237
  have hstep := st223_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p239 : ((5461724054253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT223 (i+1))
      = (∑ i ∈ Finset.range 238, stT223 (i+1)) + stT223 239 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 238
    simpa using h
  have hprev := st223_p238
  have hstep := st223_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p240 : ((26666922963489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT223 (i+1))
      = (∑ i ∈ Finset.range 239, stT223 (i+1)) + stT223 240 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 239
    simpa using h
  have hprev := st223_p239
  have hstep := st223_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p241 : ((2622658561233/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT223 (i+1))
      = (∑ i ∈ Finset.range 240, stT223 (i+1)) + stT223 241 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 240
    simpa using h
  have hprev := st223_p240
  have hstep := st223_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p242 : ((13167907454617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT223 (i+1))
      = (∑ i ∈ Finset.range 241, stT223 (i+1)) + stT223 242 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 241
    simpa using h
  have hprev := st223_p241
  have hstep := st223_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p243 : ((13452334120867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT223 (i+1))
      = (∑ i ∈ Finset.range 242, stT223 (i+1)) + stT223 243 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 242
    simpa using h
  have hprev := st223_p242
  have hstep := st223_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p244 : ((549701808503/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT223 (i+1))
      = (∑ i ∈ Finset.range 243, stT223 (i+1)) + stT223 244 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 243
    simpa using h
  have hprev := st223_p243
  have hstep := st223_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p245 : ((2762655673783/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT223 (i+1))
      = (∑ i ∈ Finset.range 244, stT223 (i+1)) + stT223 245 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 244
    simpa using h
  have hprev := st223_p244
  have hstep := st223_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p246 : ((27223134354119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT223 (i+1))
      = (∑ i ∈ Finset.range 245, stT223 (i+1)) + stT223 246 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 245
    simpa using h
  have hprev := st223_p245
  have hstep := st223_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p247 : ((6646732858721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT223 (i+1))
      = (∑ i ∈ Finset.range 246, stT223 (i+1)) + stT223 247 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 246
    simpa using h
  have hprev := st223_p246
  have hstep := st223_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p248 : ((13101077559469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT223 (i+1))
      = (∑ i ∈ Finset.range 247, stT223 (i+1)) + stT223 248 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 247
    simpa using h
  have hprev := st223_p247
  have hstep := st223_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p249 : ((13178374460059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT223 (i+1))
      = (∑ i ∈ Finset.range 248, stT223 (i+1)) + stT223 249 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 248
    simpa using h
  have hprev := st223_p248
  have hstep := st223_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_p250 : ((13465731654219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT223 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT223 (i+1))
      = (∑ i ∈ Finset.range 249, stT223 (i+1)) + stT223 250 := by
    have h := Finset.sum_range_succ (fun i => stT223 (i+1)) 249
    simpa using h
  have hprev := st223_p249
  have hstep := st223_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223_s250 :
    |Real.sin (((223 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))
      - ((-104333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -269067/2500000) (δ := 11309/1000000000) (ψ := 211979/1000000) 223 196
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 223`** (evaluated boundary). -/
theorem station_223_sign : hardyG ((((223:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 223 250 (by norm_num) (by norm_num)
    ((211979/1000000 : ℚ) : ℝ)
  have hchain := st223_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT223 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((223 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((211979/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st223_c250
  have hsinb := abs_le.mp st223_s250
  have hbdy_lo : ((2928250332661/99458500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((223 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((211979/1000000 : ℚ) : ℝ))) / 2
          - ((((223:ℕ)):ℝ))
            * Real.sin (((223 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((211979/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((223:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((223:ℝ) * Real.log (250:ℝ) - ((211979/1000000 : ℚ) : ℝ))) / 2
        - ((223:ℝ)) * Real.sin ((223:ℝ) * Real.log (250:ℝ) - ((211979/1000000 : ℚ) : ℝ))
        ≥ ((23149871/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((223:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((23149871/250000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((23149871/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((23149871/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((223:ℕ)):ℝ))+1) * (((((223:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1719568807/1562500000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((13465731654219/5000000000000 : ℚ) : ℝ) + ((2928250332661/99458500000000 : ℚ) : ℝ)
      - ((1719568807/1562500000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((211979/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((223:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((211979/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((223:ℕ)):ℝ)))).re
      - Real.sin ((211979/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((223:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((223:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((223:ℕ)):ℝ))
      = (((((223:ℕ)):ℝ)) * (Real.log ((((223:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((223:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_223
  have hl30 : ((34011973/10000000 : ℚ) : ℝ) ≤ Real.log (30:ℝ)
      ∧ Real.log (30:ℝ) ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := log_br_30
    norm_num at h ⊢
    exact h
  have hl2 : ((6931471/10000000 : ℚ) : ℝ) ≤ Real.log (2:ℝ)
      ∧ Real.log (2:ℝ) ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := log_br_2
    norm_num at h ⊢
    exact h
  have hlπ := log_pi_enclosure
  have hπ6l := Real.pi_gt_d6
  have hπ6u := Real.pi_lt_d6
  have hθb := abs_le.mp hθ30
  have hincb := abs_le.mp hinc
  have hθwin : |(((211979/1000000 : ℚ) : ℝ) + ((46:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((223:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((223:ℕ)):ℝ)))
    (φ := ((211979/1000000 : ℚ) : ℝ) + ((46:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((211979/1000000 : ℚ) : ℝ) + ((46:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((211979/1000000 : ℚ)) : ℝ) - Real.pi) + ((46:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((211979/1000000 : ℚ)) : ℝ) - Real.pi) 46).1,
    (cos_sin_shift ((((211979/1000000 : ℚ)) : ℝ) - Real.pi) 46).2]
  exact cos_sin_flip ((211979/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_223_sign
end AxiomAudit
