import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 304` (rung-309; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT304 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((304 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((142517/250000 : ℚ) : ℝ))

theorem st304_c1 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((105233/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142517/1000000) (δ := 1/1000000000) (ψ := 142517/250000) 304 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t1 : ((210441/250000 : ℚ) : ℝ) ≤ stT304 1 := by
  have hc : ((210441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210441/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((210441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c2 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-942741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1750969/2500000) (δ := 3053/200000000) (ψ := 142517/250000) 304 33
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t2 : ((-1666723206047/2500000000000 : ℚ) : ℝ) ≤ stT304 2 := by
  have hc : ((-942841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1666723206047/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-942841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c3 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((921359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 998087/10000000) (δ := 7641/500000000) (ψ := 142517/250000) 304 53
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t3 : ((2659445339509/5000000000000 : ℚ) : ℝ) ≤ stT304 3 := by
  have hc : ((921259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2659445339509/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((921259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c4 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((248489/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275003/10000000) (δ := 761/50000000) (ψ := 142517/250000) 304 67
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t4 : ((15529/31250 : ℚ) : ℝ) ≤ stT304 4 := by
  have hc : ((15529/15625 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15529/31250 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((15529/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c5 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((90209/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3473463/10000000) (δ := 15241/1000000000) (ψ := 142517/250000) 304 78
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t5 : ((80640643893/1000000000000 : ℚ) : ℝ) ≤ stT304 5 := by
  have hc : ((90159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80640643893/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((90159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c6 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-404227/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -785099/1250000) (δ := 7663/500000000) (ψ := 142517/250000) 304 87
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t6 : ((-1650453979791/5000000000000 : ℚ) : ℝ) ≤ stT304 6 := by
  have hc : ((-404277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1650453979791/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-404277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c7 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((933337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 917997/10000000) (δ := 3819/250000000) (ψ := 142517/250000) 304 94
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t7 : ((881825906907/2500000000000 : ℚ) : ℝ) ≤ stT304 7 := by
  have hc : ((933237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((881825906907/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((933237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c8 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-248201/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3776941/5000000) (δ := 15227/1000000000) (ψ := 142517/250000) 304 101
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t8 : ((-219402865671/625000000000 : ℚ) : ℝ) ≤ stT304 8 := by
  have hc : ((-124113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219402865671/625000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-124113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c9 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((50217/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1710691/5000000) (δ := 15363/1000000000) (ψ := 142517/250000) 304 106
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t9 : ((10456665621/156250000000 : ℚ) : ℝ) ≤ stT304 9 := by
  have hc : ((3137/15625 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10456665621/156250000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((3137/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c10 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-399913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 991109/2000000) (δ := 3061/200000000) (ψ := 142517/250000) 304 111
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t10 : ((-632476154807/5000000000000 : ℚ) : ℝ) ≤ stT304 10 := by
  have hc : ((-400013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-632476154807/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-400013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c11 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((179263/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1148519/10000000) (δ := 7617/500000000) (ψ := 142517/250000) 304 116
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t11 : ((540437899459/2000000000000 : ℚ) : ℝ) ≤ stT304 11 := by
  have hc : ((179243/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540437899459/2000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((179243/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c12 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((130591/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 537073/2500000) (δ := 15263/1000000000) (ψ := 142517/250000) 304 120
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t12 : ((376925964821/2000000000000 : ℚ) : ℝ) ≤ stT304 12 := by
  have hc : ((130571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376925964821/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((130571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c13 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((998227/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148891/10000000) (δ := 3823/250000000) (ψ := 142517/250000) 304 124
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t13 : ((5536610469/20000000000 : ℚ) : ℝ) ≤ stT304 13 := by
  have hc : ((998127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5536610469/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((998127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c14 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-826891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3180441/5000000) (δ := 383/25000000) (ψ := 142517/250000) 304 128
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t14 : ((-2210226897483/10000000000000 : ℚ) : ℝ) ≤ stT304 14 := by
  have hc : ((-826991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2210226897483/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-826991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c15 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((456531/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131271/1250000) (δ := 7621/500000000) (ψ := 142517/250000) 304 131
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t15 : ((294657116057/1250000000000 : ℚ) : ℝ) ≤ stT304 15 := by
  have hc : ((456481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294657116057/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((456481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c16 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((187869/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 437601/5000000) (δ := 15239/1000000000) (ψ := 142517/250000) 304 134
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t16 : ((187849/800000 : ℚ) : ℝ) ≤ stT304 16 := by
  have hc : ((187849/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187849/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((187849/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c17 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((997579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21749/1250000) (δ := 7659/500000000) (ψ := 142517/250000) 304 137
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t17 : ((604810419381/2500000000000 : ℚ) : ℝ) ≤ stT304 17 := by
  have hc : ((997479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((604810419381/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((997479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c18 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((13897/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1928749/5000000) (δ := 3849/250000000) (ψ := 142517/250000) 304 140
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t18 : ((16318841817/2500000000000 : ℚ) : ℝ) ≤ stT304 18 := by
  have hc : ((13847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16318841817/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((13847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c19 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-10722/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363603/625000) (δ := 15221/1000000000) (ψ := 142517/250000) 304 142
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t19 : ((-196812373583/1250000000000 : ℚ) : ℝ) ≤ stT304 19 := by
  have hc : ((-171577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196812373583/1250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-171577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c20 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((18699/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1161667/5000000) (δ := 763/50000000) (ψ := 142517/250000) 304 145
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t20 : ((334441832989/2500000000000 : ℚ) : ℝ) ≤ stT304 20 := by
  have hc : ((149567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334441832989/2500000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((149567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c21 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((116071/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835323/2500000) (δ := 15357/1000000000) (ψ := 142517/250000) 304 147
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t21 : ((126589236869/2500000000000 : ℚ) : ℝ) ≤ stT304 21 := by
  have hc : ((116021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126589236869/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((116021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c22 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-973811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1456113/2000000) (δ := 119/7812500) (ψ := 142517/250000) 304 149
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t22 : ((-259548255411/1250000000000 : ℚ) : ℝ) ≤ stT304 22 := by
  have hc : ((-973911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259548255411/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-973911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c23 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-37669/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6059957/10000000) (δ := 1531/100000000) (ψ := 142517/250000) 304 152
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t23 : ((-7855575273/50000000000 : ℚ) : ℝ) ≤ stT304 23 := by
  have hc : ((-18837/25000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7855575273/50000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-18837/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c24 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-92611/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5130587/10000000) (δ := 15307/1000000000) (ψ := 142517/250000) 304 154
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t24 : ((-94541143851/1000000000000 : ℚ) : ℝ) ≤ stT304 24 := by
  have hc : ((-92631/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94541143851/1000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-92631/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c25 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-595527/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2760897/5000000) (δ := 15281/1000000000) (ψ := 142517/250000) 304 156
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t25 : ((-1191254595627/10000000000000 : ℚ) : ℝ) ≤ stT304 25 := by
  have hc : ((-595627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1191254595627/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-595627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c26 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-958359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1782497/2500000) (δ := 1917/125000000) (ψ := 142517/250000) 304 158
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t26 : ((-939846684679/5000000000000 : ℚ) : ℝ) ≤ stT304 26 := by
  have hc : ((-958459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-939846684679/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-958459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c27 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-43377/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1461169/2500000) (δ := 6/390625) (ψ := 142517/250000) 304 159
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t27 : ((-333964432033/2500000000000 : ℚ) : ℝ) ≤ stT304 27 := by
  have hc : ((-173533/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333964432033/2500000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-173533/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c28 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((8461/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1034101/5000000) (δ := 15257/1000000000) (ψ := 142517/250000) 304 161
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t28 : ((31974843329/250000000000 : ℚ) : ℝ) ≤ stT304 28 := by
  have hc : ((33839/50000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31974843329/250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((33839/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c29 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((478953/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2678337/10000000) (δ := 15331/1000000000) (ψ := 142517/250000) 304 163
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t29 : ((889207514909/10000000000000 : ℚ) : ℝ) ≤ stT304 29 := by
  have hc : ((478853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((889207514909/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((478853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c30 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-490997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184471/250000) (δ := 1903/125000000) (ψ := 142517/250000) 304 164
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t30 : ((-448262565937/2500000000000 : ℚ) : ℝ) ≤ stT304 30 := by
  have hc : ((-491047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448262565937/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-491047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c31 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((469119/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441619/5000000) (δ := 15393/1000000000) (ψ := 142517/250000) 304 166
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t31 : ((842472784657/5000000000000 : ℚ) : ℝ) ≤ stT304 31 := by
  have hc : ((469069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((842472784657/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((469069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c32 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-209099/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6403677/10000000) (δ := 1901/125000000) (ψ := 142517/250000) 304 168
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t32 : ((-92420626527/625000000000 : ℚ) : ℝ) ≤ stT304 32 := by
  have hc : ((-52281/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92420626527/625000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-52281/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c33 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((218197/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159347/1250000) (δ := 3063/200000000) (ψ := 142517/250000) 304 169
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t33 : ((11868393171/78125000000 : ℚ) : ℝ) ≤ stT304 33 := by
  have hc : ((54543/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11868393171/78125000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((54543/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c34 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-246789/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7452871/10000000) (δ := 7637/500000000) (ψ := 142517/250000) 304 171
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t34 : ((-105820638651/625000000000 : ℚ) : ℝ) ≤ stT304 34 := by
  have hc : ((-123407/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105820638651/625000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-123407/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c35 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((899517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -565167/5000000) (δ := 3809/250000000) (ψ := 142517/250000) 304 172
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t35 : ((380072937609/2500000000000 : ℚ) : ℝ) ≤ stT304 35 := by
  have hc : ((899417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380072937609/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((899417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c36 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-254991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4571587/10000000) (δ := 959/62500000) (ψ := 142517/250000) 304 173
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t36 : ((-425151751697/10000000000000 : ℚ) : ℝ) ≤ stT304 36 := by
  have hc : ((-255091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425151751697/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-255091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c37 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-185767/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60211/100000) (δ := 3049/200000000) (ψ := 142517/250000) 304 175
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t37 : ((-477250297/3906250000 : ℚ) : ℝ) ≤ stT304 37 := by
  have hc : ((-11612/15625 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-477250297/3906250000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-11612/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c38 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((104249/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1461231/10000000) (δ := 3053/200000000) (ψ := 142517/250000) 304 176
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t38 : ((169093909611/1250000000000 : ℚ) : ℝ) ≤ stT304 38 := by
  have hc : ((208473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169093909611/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((208473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c39 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((515783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1286093/5000000) (δ := 3843/250000000) (ψ := 142517/250000) 304 177
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t39 : ((825753389923/10000000000000 : ℚ) : ℝ) ≤ stT304 39 := by
  have hc : ((515683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((825753389923/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((515683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c40 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-382649/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24423/40000) (δ := 3831/250000000) (ψ := 142517/250000) 304 178
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t40 : ((-605100314161/5000000000000 : ℚ) : ℝ) ≤ stT304 40 := by
  have hc : ((-382699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-605100314161/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-382699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c41 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-216447/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32719/50000) (δ := 7647/500000000) (ψ := 142517/250000) 304 180
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t41 : ((-21129534271/156250000000 : ℚ) : ℝ) ≤ stT304 41 := by
  have hc : ((-27059/31250 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21129534271/156250000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-27059/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c42 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-2119/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3937587/10000000) (δ := 15401/1000000000) (ψ := 142517/250000) 304 181
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t42 : ((-1673420373/2500000000000 : ℚ) : ℝ) ≤ stT304 42 := by
  have hc : ((-2169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1673420373/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-2169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c43 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((152329/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1762371/10000000) (δ := 3059/200000000) (ψ := 142517/250000) 304 182
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t43 : ((46453788073/400000000000 : ℚ) : ℝ) ≤ stT304 43 := by
  have hc : ((152309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46453788073/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((152309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c44 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 843/5000000) (δ := 3043/200000000) (ψ := 142517/250000) 304 183
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t44 : ((3768513111/25000000000 : ℚ) : ℝ) ≤ stT304 44 := by
  have hc : ((9999/10000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3768513111/25000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((9999/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c45 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((213233/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1373051/10000000) (δ := 15323/1000000000) (ψ := 142517/250000) 304 184
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t45 : ((39728938861/312500000000 : ℚ) : ℝ) ≤ stT304 45 := by
  have hc : ((26651/31250 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39728938861/312500000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((26651/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c46 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((583617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2369051/10000000) (δ := 15373/1000000000) (ψ := 142517/250000) 304 185
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t46 : ((860348551623/10000000000000 : ℚ) : ℝ) ≤ stT304 46 := by
  have hc : ((583517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860348551623/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((583517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c47 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((180083/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 751469/2500000) (δ := 7633/500000000) (ψ := 142517/250000) 304 186
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t47 : ((262604955417/5000000000000 : ℚ) : ℝ) ≤ stT304 47 := by
  have hc : ((180033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262604955417/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((180033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c48 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((124379/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3298497/10000000) (δ := 3811/250000000) (ψ := 142517/250000) 304 187
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t48 : ((1435626963/40000000000 : ℚ) : ℝ) ≤ stT304 48 := by
  have hc : ((124329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1435626963/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((124329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c49 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((32901/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1630563/5000000) (δ := 15351/1000000000) (ψ := 142517/250000) 304 188
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t49 : ((93967114667/2500000000000 : ℚ) : ℝ) ≤ stT304 49 := by
  have hc : ((65777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93967114667/2500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((65777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c50 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((49583/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290729/1000000) (δ := 3069/200000000) (ψ := 142517/250000) 304 189
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t50 : ((140206491033/2500000000000 : ℚ) : ℝ) ≤ stT304 50 := by
  have hc : ((99141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140206491033/2500000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((99141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c51 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((155457/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2249303/10000000) (δ := 15237/1000000000) (ψ := 142517/250000) 304 190
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t51 : ((680151003/7812500000 : ℚ) : ℝ) ≤ stT304 51 := by
  have hc : ((19429/31250 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680151003/7812500000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((19429/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c52 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((867999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162387/1250000) (δ := 15273/1000000000) (ψ := 142517/250000) 304 191
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t52 : ((4814235753/40000000000 : ℚ) : ℝ) ≤ stT304 52 := by
  have hc : ((867899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4814235753/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((867899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c53 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((999633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13553/2000000) (δ := 769/50000000) (ψ := 142517/250000) 304 192
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t53 : ((274592705293/2000000000000 : ℚ) : ℝ) ≤ stT304 53 := by
  have hc : ((999533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274592705293/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((999533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c54 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((839909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1434203/10000000) (δ := 3829/250000000) (ψ := 142517/250000) 304 193
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t54 : ((1142834762043/10000000000000 : ℚ) : ℝ) ≤ stT304 54 := by
  have hc : ((839809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1142834762043/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((839809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c55 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((143961/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63937/200000) (δ := 15209/1000000000) (ψ := 142517/250000) 304 194
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t55 : ((194049448489/5000000000000 : ℚ) : ℝ) ≤ stT304 55 := by
  have hc : ((143911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194049448489/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((143911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c56 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-491233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5210753/10000000) (δ := 7651/500000000) (ψ := 142517/250000) 304 195
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t56 : ((-656571727231/10000000000000 : ℚ) : ℝ) ≤ stT304 56 := by
  have hc : ((-491333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-656571727231/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-491333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c57 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-197609/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7467021/10000000) (δ := 7697/500000000) (ψ := 142517/250000) 304 196
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t57 : ((-261766132257/2000000000000 : ℚ) : ℝ) ≤ stT304 57 := by
  have hc : ((-197629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261766132257/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-197629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c58 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-666499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5750747/10000000) (δ := 7697/500000000) (ψ := 142517/250000) 304 196
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t58 : ((-175057563187/2000000000000 : ℚ) : ℝ) ≤ stT304 58 := by
  have hc : ((-666599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175057563187/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-666599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c59 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((349451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94829/312500) (δ := 15287/1000000000) (ψ := 142517/250000) 304 197
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t59 : ((454816224039/10000000000000 : ℚ) : ℝ) ≤ stT304 59 := by
  have hc : ((349351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454816224039/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((349351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c60 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((999201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99961/10000000) (δ := 15223/1000000000) (ψ := 142517/250000) 304 198
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t60 : ((644916698197/5000000000000 : ℚ) : ℝ) ≤ stT304 60 := by
  have hc : ((999101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((644916698197/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((999101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c61 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((10789/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1522867/5000000) (δ := 1533/100000000) (ψ := 142517/250000) 304 199
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t61 : ((6904944601/156250000000 : ℚ) : ℝ) ≤ stT304 61 := by
  have hc : ((86287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6904944601/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((86287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c62 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-834647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3197859/5000000) (δ := 7683/500000000) (ψ := 142517/250000) 304 200
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t62 : ((-530065179747/5000000000000 : ℚ) : ℝ) ≤ stT304 62 := by
  have hc : ((-834747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-530065179747/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-834747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c63 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-134123/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2882293/5000000) (δ := 7683/500000000) (ψ := 142517/250000) 304 200
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t63 : ((-84502175563/1000000000000 : ℚ) : ℝ) ≤ stT304 63 := by
  have hc : ((-134143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84502175563/1000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-134143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c64 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((689403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2025331/10000000) (δ := 7629/500000000) (ψ := 142517/250000) 304 201
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t64 : ((689303/8000000 : ℚ) : ℝ) ≤ stT304 64 := by
  have hc : ((689303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((689303/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((689303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c65 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((72499/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23743/125000) (δ := 3813/250000000) (ψ := 142517/250000) 304 202
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t65 : ((89911513683/1000000000000 : ℚ) : ℝ) ≤ stT304 65 := by
  have hc : ((72489/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89911513683/1000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((72489/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c66 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-738501/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6004103/10000000) (δ := 15359/1000000000) (ψ := 142517/250000) 304 203
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t66 : ((-181831009983/2000000000000 : ℚ) : ℝ) ≤ stT304 66 := by
  have hc : ((-738601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181831009983/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-738601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c67 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-281943/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5424701/10000000) (δ := 15359/1000000000) (ψ := 142517/250000) 304 203
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t67 : ((-68901887627/1000000000000 : ℚ) : ℝ) ≤ stT304 67 := by
  have hc : ((-281993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68901887627/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-281993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c68 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((231181/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976213/10000000) (δ := 15337/1000000000) (ψ := 142517/250000) 304 204
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t68 : ((35039724471/312500000000 : ℚ) : ℝ) ≤ stT304 68 := by
  have hc : ((57789/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35039724471/312500000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((57789/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c69 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((115871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1818331/5000000) (δ := 1523/100000000) (ψ := 142517/250000) 304 205
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t69 : ((69685922259/5000000000000 : ℚ) : ℝ) ≤ stT304 69 := by
  have hc : ((115771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69685922259/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((115771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c70 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-975439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5839/8000) (δ := 1523/100000000) (ψ := 142517/250000) 304 205
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t70 : ((-1165992503431/10000000000000 : ℚ) : ℝ) ≤ stT304 70 := by
  have hc : ((-975539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1165992503431/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-975539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c71 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((582957/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2371083/10000000) (δ := 191/12500000) (ψ := 142517/250000) 304 206
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t71 : ((691723613317/10000000000000 : ℚ) : ℝ) ≤ stT304 71 := by
  have hc : ((582857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((691723613317/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((582857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c72 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((234377/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -676823/2500000) (δ := 3847/250000000) (ψ := 142517/250000) 304 207
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t72 : ((276156947097/5000000000000 : ℚ) : ℝ) ≤ stT304 72 := by
  have hc : ((234327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276156947097/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((234327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c73 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-999509/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60747/78125) (δ := 3847/250000000) (ψ := 142517/250000) 304 207
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t73 : ((-292488592227/2500000000000 : ℚ) : ℝ) ≤ stT304 73 := by
  have hc : ((-999609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292488592227/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-999609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c74 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((285463/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 601977/2500000) (δ := 3827/250000000) (ψ := 142517/250000) 304 208
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t74 : ((82946440647/1250000000000 : ℚ) : ℝ) ≤ stT304 74 := by
  have hc : ((285413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82946440647/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((285413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c75 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((81341/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3098499/10000000) (δ := 7601/500000000) (ψ := 142517/250000) 304 209
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t75 : ((234738963/6250000000 : ℚ) : ℝ) ≤ stT304 75 := by
  have hc : ((20329/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234738963/6250000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((20329/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c76 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-937837/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6967853/10000000) (δ := 7601/500000000) (ψ := 142517/250000) 304 209
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t76 : ((-1075887836023/10000000000000 : ℚ) : ℝ) ≤ stT304 76 := by
  have hc : ((-937937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1075887836023/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-937937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c77 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((443987/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 597343/5000000) (δ := 15309/1000000000) (ψ := 142517/250000) 304 210
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t77 : ((101182564977/1000000000000 : ℚ) : ℝ) ≤ stT304 77 := by
  have hc : ((443937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101182564977/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((443937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c78 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-6137/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2353347/5000000) (δ := 15387/1000000000) (ψ := 142517/250000) 304 211
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t78 : ((-3475527321/100000000000 : ℚ) : ℝ) ≤ stT304 78 := by
  have hc : ((-6139/20000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3475527321/100000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-6139/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c79 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-407013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2487473/5000000) (δ := 15387/1000000000) (ψ := 142517/250000) 304 211
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t79 : ((-14313685967/312500000000 : ℚ) : ℝ) ≤ stT304 79 := by
  have hc : ((-407113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14313685967/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-407113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c80 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((891907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1173129/10000000) (δ := 15279/1000000000) (ψ := 142517/250000) 304 212
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t80 : ((997069655631/10000000000000 : ℚ) : ℝ) ≤ stT304 80 := by
  have hc : ((891807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((997069655631/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((891807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c81 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-12329/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -929999/1250000) (δ := 15231/1000000000) (ψ := 142517/250000) 304 213
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t81 : ((-6850144369/62500000000 : ℚ) : ℝ) ≤ stT304 81 := by
  have hc : ((-49321/50000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6850144369/62500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-49321/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c82 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((728879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 471321/2500000) (δ := 15231/1000000000) (ψ := 142517/250000) 304 213
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t82 : ((160960316277/2000000000000 : ℚ) : ℝ) ≤ stT304 82 := by
  have hc : ((728779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160960316277/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((728779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c83 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-134989/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922083/2000000) (δ := 7669/500000000) (ψ := 142517/250000) 304 214
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t83 : ((-148224613077/5000000000000 : ℚ) : ℝ) ≤ stT304 83 := by
  have hc : ((-135039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148224613077/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-135039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c84 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-111937/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4491459/10000000) (δ := 15269/500000000) (ψ := 142517/250000) 304 214
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t84 : ((-12218789583/500000000000 : ℚ) : ℝ) ≤ stT304 84 := by
  have hc : ((-111987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12218789583/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-111987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c85 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((157561/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2222323/10000000) (δ := 7679/500000000) (ψ := 142517/250000) 304 215
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t85 : ((1334935449/19531250000 : ℚ) : ℝ) ≤ stT304 85 := by
  have hc : ((9846/15625 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1334935449/19531250000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((9846/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c86 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-889321/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6666637/10000000) (δ := 7679/500000000) (ψ := 142517/250000) 304 215
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t86 : ((-119885946011/1250000000000 : ℚ) : ℝ) ≤ stT304 86 := by
  have hc : ((-889421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119885946011/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-889421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c87 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((994801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127521/5000000) (δ := 15251/1000000000) (ψ := 142517/250000) 304 216
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t87 : ((66651929907/625000000000 : ℚ) : ℝ) ≤ stT304 87 := by
  have hc : ((994701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66651929907/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((994701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c88 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-973503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7277193/10000000) (δ := 15259/1000000000) (ψ := 142517/250000) 304 217
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t88 : ((-259466173103/2500000000000 : ℚ) : ℝ) ≤ stT304 88 := by
  have hc : ((-973603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259466173103/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-973603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c89 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((865739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1310427/10000000) (δ := 15259/1000000000) (ψ := 142517/250000) 304 217
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t89 : ((917574743083/10000000000000 : ℚ) : ℝ) ≤ stT304 89 := by
  have hc : ((865639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((917574743083/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((865639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c90 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-711433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1476457/2500000) (δ := 15367/1000000000) (ψ := 142517/250000) 304 218
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t90 : ((-750021954569/10000000000000 : ℚ) : ℝ) ≤ stT304 90 := by
  have hc : ((-711533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750021954569/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-711533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c91 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((542973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1246029/5000000) (δ := 30567/1000000000) (ψ := 142517/250000) 304 218
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t91 : ((142271269983/2500000000000 : ℚ) : ℝ) ≤ stT304 91 := by
  have hc : ((542873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142271269983/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((542873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c92 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-191543/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1227457/2500000) (δ := 15329/1000000000) (ψ := 142517/250000) 304 219
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t92 : ((-199749688789/5000000000000 : ℚ) : ℝ) ≤ stT304 92 := by
  have hc : ((-191593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199749688789/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-191593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c93 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((245673/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 413307/1250000) (δ := 15329/1000000000) (ψ := 142517/250000) 304 219
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t93 : ((254647167923/10000000000000 : ℚ) : ℝ) ≤ stT304 93 := by
  have hc : ((245573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254647167923/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((245573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c94 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-68997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4273079/10000000) (δ := 7611/500000000) (ψ := 142517/250000) 304 220
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t94 : ((-35608297417/2500000000000 : ℚ) : ℝ) ≤ stT304 94 := by
  have hc : ((-69047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35608297417/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-69047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c95 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((15757/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3769317/10000000) (δ := 7611/500000000) (ψ := 142517/250000) 304 220
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t95 : ((2017585737/312500000000 : ℚ) : ℝ) ≤ stT304 95 := by
  have hc : ((3933/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2017585737/312500000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((3933/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c96 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-4277/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1990229/5000000) (δ := 1911/125000000) (ψ := 142517/250000) 304 221
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t96 : ((-4385608437/2000000000000 : ℚ) : ℝ) ≤ stT304 96 := by
  have hc : ((-4297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4385608437/2000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-4297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c97 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((793/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 389527/1000000) (δ := 1911/125000000) (ψ := 142517/250000) 304 221
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t97 : ((1597646931/1250000000000 : ℚ) : ℝ) ≤ stT304 97 := by
  have hc : ((3147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1597646931/1250000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((3147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c98 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-36297/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4017753/10000000) (δ := 3079/200000000) (ψ := 142517/250000) 304 222
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t98 : ((-36766538741/10000000000000 : ℚ) : ℝ) ≤ stT304 98 := by
  have hc : ((-36397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36766538741/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-36397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c99 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((1143/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3698071/10000000) (δ := 3079/200000000) (ψ := 142517/250000) 304 222
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t99 : ((4590003979/500000000000 : ℚ) : ℝ) ≤ stT304 99 := by
  have hc : ((4567/50000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4590003979/500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((4567/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c100 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-176933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -874333/2000000) (δ := 153/10000000) (ψ := 142517/250000) 304 223
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t100 : ((-177033/10000000 : ℚ) : ℝ) ≤ stT304 100 := by
  have hc : ((-177033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177033/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-177033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c101 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((2903/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3190639/10000000) (δ := 153/10000000) (ψ := 142517/250000) 304 223
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t101 : ((1443798687/50000000000 : ℚ) : ℝ) ≤ stT304 101 := by
  have hc : ((1451/5000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1443798687/50000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((1451/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c102 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-683/1600 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628697/1250000) (δ := 1521/100000000) (ψ := 142517/250000) 304 224
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t102 : ((-4227684423/100000000000 : ℚ) : ℝ) ≤ stT304 102 := by
  have hc : ((-17079/40000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4227684423/100000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-17079/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c103 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((115681/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119253/500000) (δ := 1521/100000000) (ψ := 142517/250000) 304 224
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t103 : ((113964137469/2000000000000 : ℚ) : ℝ) ≤ stT304 103 := by
  have hc : ((115661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113964137469/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((115661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c104 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-91491/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5979859/10000000) (δ := 15317/1000000000) (ψ := 142517/250000) 304 225
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t104 : ((-179453187067/2500000000000 : ℚ) : ℝ) ≤ stT304 104 := by
  have hc : ((-183007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179453187067/2500000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-183007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c105 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((173843/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1292961/10000000) (δ := 15317/1000000000) (ψ := 142517/250000) 304 225
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t105 : ((1696338657/20000000000 : ℚ) : ℝ) ≤ stT304 105 := by
  have hc : ((173823/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1696338657/20000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((173823/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c106 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-967127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7211191/10000000) (δ := 15379/1000000000) (ψ := 142517/250000) 304 226
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t106 : ((-469727021961/5000000000000 : ℚ) : ℝ) ≤ stT304 106 := by
  have hc : ((-967227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469727021961/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-967227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c107 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((999551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74943/10000000) (δ := 15379/1000000000) (ψ := 142517/250000) 304 226
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t107 : ((60387828871/625000000000 : ℚ) : ℝ) ≤ stT304 107 := by
  have hc : ((999451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60387828871/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((999451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c108 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-470767/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6994881/10000000) (δ := 15379/1000000000) (ψ := 142517/250000) 304 226
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t108 : ((-453044129067/5000000000000 : ℚ) : ℝ) ≤ stT304 108 := by
  have hc : ((-470817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453044129067/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-470817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c109 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((775439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -854233/5000000) (δ := 1909/125000000) (ψ := 142517/250000) 304 227
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t109 : ((371319926507/5000000000000 : ℚ) : ℝ) ≤ stT304 109 := by
  have hc : ((775339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371319926507/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((775339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c110 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-498699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2616117/5000000) (δ := 1909/125000000) (ψ := 142517/250000) 304 227
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t110 : ((-475586390937/10000000000000 : ℚ) : ℝ) ≤ stT304 110 := by
  have hc : ((-498799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475586390937/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-498799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c111 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((65647/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -719561/2000000) (δ := 7619/500000000) (ψ := 142517/250000) 304 228
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t111 : ((62261851729/5000000000000 : ℚ) : ℝ) ≤ stT304 111 := by
  have hc : ((65597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62261851729/5000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((65597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c112 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((279683/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3218331/10000000) (δ := 7619/500000000) (ψ := 142517/250000) 304 228
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t112 : ((264181052113/10000000000000 : ℚ) : ℝ) ≤ stT304 112 := by
  have hc : ((279583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264181052113/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((279583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c113 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-661487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -716749/1250000) (δ := 7673/500000000) (ψ := 142517/250000) 304 229
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t113 : ((-622368784227/10000000000000 : ℚ) : ℝ) ≤ stT304 113 := by
  have hc : ((-661587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-622368784227/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-661587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c114 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((57929/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60129/625000) (δ := 7673/500000000) (ψ := 142517/250000) 304 229
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t114 : ((43399663047/500000000000 : ℚ) : ℝ) ≤ stT304 114 := by
  have hc : ((231691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43399663047/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((231691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c115 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-994831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1899919/2500000) (δ := 7673/500000000) (ψ := 142517/250000) 304 229
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t115 : ((-185555626431/2000000000000 : ℚ) : ℝ) ≤ stT304 115 := by
  have hc : ((-994931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185555626431/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-994931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c116 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((25591/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95513/625000) (δ := 307/20000000) (ψ := 142517/250000) 304 230
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t116 : ((47515455657/625000000000 : ℚ) : ℝ) ≤ stT304 116 := by
  have hc : ((204703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47515455657/625000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((204703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c117 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-207251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124887/250000) (δ := 307/20000000) (ψ := 142517/250000) 304 230
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t117 : ((-191649981801/5000000000000 : ℚ) : ℝ) ≤ stT304 117 := by
  have hc : ((-207301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191649981801/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-207301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c118 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-126603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4244351/10000000) (δ := 15243/1000000000) (ψ := 142517/250000) 304 231
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t118 : ((-4665584569/400000000000 : ℚ) : ℝ) ≤ stT304 118 := by
  have hc : ((-126703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4665584569/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-126703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c119 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((646617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2169137/10000000) (δ := 15243/1000000000) (ψ := 142517/250000) 304 231
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t119 : ((296330420433/5000000000000 : ℚ) : ℝ) ≤ stT304 119 := by
  have hc : ((646517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296330420433/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((646517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c120 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-240941/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3589459/5000000) (δ := 15267/1000000000) (ψ := 142517/250000) 304 232
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t120 : ((-109985436693/1250000000000 : ℚ) : ℝ) ≤ stT304 120 := by
  have hc : ((-120483/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109985436693/1250000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-120483/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c121 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((939807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87183/1000000) (δ := 15267/1000000000) (ψ := 142517/250000) 304 232
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t121 : ((85427823663/1000000000000 : ℚ) : ℝ) ≤ stT304 121 := by
  have hc : ((939707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85427823663/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((939707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c122 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-11003/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107667/200000) (δ := 15267/1000000000) (ψ := 142517/250000) 304 232
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t122 : ((-996346479/20000000000 : ℚ) : ℝ) ≤ stT304 122 := by
  have hc : ((-2201/4000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-996346479/20000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-2201/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c123 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-4833/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -824101/2000000) (δ := 7687/500000000) (ψ := 142517/250000) 304 233
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t123 : ((-1745362619/250000000000 : ℚ) : ℝ) ≤ stT304 123 := by
  have hc : ((-19357/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1745362619/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-19357/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c124 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((687071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2033367/10000000) (δ := 7687/500000000) (ψ := 142517/250000) 304 233
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t124 : ((308458909623/5000000000000 : ℚ) : ℝ) ≤ stT304 124 := by
  have hc : ((686971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308458909623/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((686971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c125 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-993561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60561/80000) (δ := 15321/1000000000) (ψ := 142517/250000) 304 234
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t125 : ((-222189555227/2500000000000 : ℚ) : ℝ) ≤ stT304 125 := by
  have hc : ((-993661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222189555227/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-993661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c126 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((411047/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1514293/10000000) (δ := 15321/1000000000) (ψ := 142517/250000) 304 234
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t126 : ((36614489739/500000000000 : ℚ) : ℝ) ≤ stT304 126 := by
  have hc : ((410997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36614489739/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((410997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c127 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-112351/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4493583/10000000) (δ := 15321/1000000000) (ψ := 142517/250000) 304 234
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t127 : ((-99739814157/5000000000000 : ℚ) : ℝ) ≤ stT304 127 := by
  have hc : ((-112401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99739814157/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-112401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c128 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-506071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1313387/2500000) (δ := 7607/500000000) (ψ := 142517/250000) 304 235
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t128 : ((-111849112041/2500000000000 : ℚ) : ℝ) ≤ stT304 128 := by
  have hc : ((-506171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111849112041/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-506171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c129 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((965257/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 165231/2500000) (δ := 7607/500000000) (ψ := 142517/250000) 304 235
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t129 : ((16995449613/200000000000 : ℚ) : ℝ) ≤ stT304 129 := by
  have hc : ((965157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16995449613/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((965157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c130 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-862941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1632411/2500000) (δ := 7607/500000000) (ψ := 142517/250000) 304 235
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t130 : ((-756937876419/10000000000000 : ℚ) : ℝ) ≤ stT304 130 := by
  have hc : ((-863041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-756937876419/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-863041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c131 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((113497/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670903/2000000) (δ := 239/15625000) (ψ := 142517/250000) 304 236
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t131 : ((12389887211/625000000000 : ℚ) : ℝ) ≤ stT304 131 := by
  have hc : ((113447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12389887211/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((113447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c132 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((282653/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2424981/10000000) (δ := 239/15625000) (ψ := 142517/250000) 304 236
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t132 : ((61493564991/1250000000000 : ℚ) : ℝ) ≤ stT304 132 := by
  have hc : ((282603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61493564991/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((282603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c133 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-248119/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7547111/10000000) (δ := 77/5000000) (ψ := 142517/250000) 304 237
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t133 : ((-1344800899/15625000000 : ℚ) : ℝ) ≤ stT304 133 := by
  have hc : ((-15509/15625 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1344800899/15625000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-15509/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c134 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((73733/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1854217/10000000) (δ := 153/5000000) (ψ := 142517/250000) 304 237
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t134 : ((15921735141/250000000000 : ℚ) : ℝ) ≤ stT304 134 := by
  have hc : ((73723/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15921735141/250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((73723/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c135 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((10447/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 759269/2000000) (δ := 77/5000000) (ψ := 142517/250000) 304 237
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t135 : ((4487061337/1000000000000 : ℚ) : ℝ) ≤ stT304 135 := by
  have hc : ((10427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4487061337/1000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((10427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c136 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-81359/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3151371/5000000) (δ := 15293/1000000000) (ψ := 142517/250000) 304 238
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t136 : ((-69773347917/1000000000000 : ℚ) : ℝ) ≤ stT304 136 := by
  have hc : ((-81369/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69773347917/1000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-81369/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c137 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((957103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367453/5000000) (δ := 15293/1000000000) (ψ := 142517/250000) 304 238
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t137 : ((817622212071/10000000000000 : ℚ) : ℝ) ≤ stT304 137 := by
  have hc : ((957003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((817622212071/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((957003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c138 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-339271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2396173/5000000) (δ := 15293/1000000000) (ψ := 142517/250000) 304 238
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t138 : ((-288891939347/10000000000000 : ℚ) : ℝ) ≤ stT304 138 := by
  have hc : ((-339371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288891939347/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-339371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c139 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-282519/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5428189/10000000) (δ := 15217/1000000000) (ψ := 142517/250000) 304 239
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t139 : ((-239671917541/5000000000000 : ℚ) : ℝ) ≤ stT304 139 := by
  have hc : ((-282569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239671917541/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-282569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c140 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((31249/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19871/10000000) (δ := 15217/1000000000) (ψ := 142517/250000) 304 239
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t140 : ((105630304959/1250000000000 : ℚ) : ℝ) ≤ stT304 140 := by
  have hc : ((249967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105630304959/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((249967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c141 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-565337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1085819/2000000) (δ := 15217/1000000000) (ψ := 142517/250000) 304 239
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t141 : ((-59522987553/1250000000000 : ℚ) : ℝ) ≤ stT304 141 := by
  have hc : ((-565437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59522987553/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-565437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c142 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-76467/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1226949/2500000) (δ := 613/40000000) (ψ := 142517/250000) 304 240
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t142 : ((-32093256817/1000000000000 : ℚ) : ℝ) ≤ stT304 142 := by
  have hc : ((-76487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32093256817/1000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-76487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c143 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((197109/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21279/500000) (δ := 613/40000000) (ψ := 142517/250000) 304 240
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t143 : ((82407049769/1000000000000 : ℚ) : ℝ) ≤ stT304 143 := by
  have hc : ((197089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82407049769/1000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((197089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c144 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-657797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1430429/2500000) (δ := 613/40000000) (ψ := 142517/250000) 304 240
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t144 : ((-274123969299/5000000000000 : ℚ) : ℝ) ≤ stT304 144 := by
  have hc : ((-657897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274123969299/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-657897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c145 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-78611/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1181667/2500000) (δ := 15371/1000000000) (ψ := 142517/250000) 304 241
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t145 : ((-3265182969/125000000000 : ℚ) : ℝ) ≤ stT304 145 := by
  have hc : ((-19659/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3265182969/125000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-19659/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c146 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((39213/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15523/312500) (δ := 15371/1000000000) (ψ := 142517/250000) 304 241
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t146 : ((6489912889/80000000000 : ℚ) : ℝ) ≤ stT304 146 := by
  have hc : ((39209/40000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6489912889/80000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((39209/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c147 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-80811/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284221/500000) (δ := 15371/1000000000) (ψ := 142517/250000) 304 241
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t147 : ((-133324344189/2500000000000 : ℚ) : ℝ) ≤ stT304 147 := by
  have hc : ((-161647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133324344189/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-161647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c148 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-368683/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4870971/10000000) (δ := 477/31250000) (ψ := 142517/250000) 304 242
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t148 : ((-60627556417/2000000000000 : ℚ) : ℝ) ≤ stT304 148 := by
  have hc : ((-368783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60627556417/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-368783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c149 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((7961/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49389/2000000) (δ := 477/31250000) (ψ := 142517/250000) 304 242
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t149 : ((32606213031/400000000000 : ℚ) : ℝ) ≤ stT304 149 := by
  have hc : ((39801/40000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32606213031/400000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((39801/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c150 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-266189/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5330509/10000000) (δ := 477/31250000) (ψ := 142517/250000) 304 242
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t150 : ((-217383344783/5000000000000 : ℚ) : ℝ) ≤ stT304 150 := by
  have hc : ((-266239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217383344783/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-266239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c151 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-265689/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2663779/5000000) (δ := 7623/500000000) (ψ := 142517/250000) 304 243
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t151 : ((-216255475071/5000000000000 : ℚ) : ℝ) ≤ stT304 151 := by
  have hc : ((-265739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216255475071/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-265739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c152 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((992271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155513/5000000) (δ := 7623/500000000) (ψ := 142517/250000) 304 243
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t152 : ((804756843297/10000000000000 : ℚ) : ℝ) ≤ stT304 152 := by
  have hc : ((992171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((804756843297/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((992171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c153 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-293841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2336299/5000000) (δ := 7623/500000000) (ψ := 142517/250000) 304 243
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t153 : ((-237637483273/10000000000000 : ℚ) : ℝ) ≤ stT304 153 := by
  have hc : ((-293941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237637483273/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-293941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c154 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-759719/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6084193/10000000) (δ := 15353/1000000000) (ψ := 142517/250000) 304 244
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t154 : ((-612279626037/10000000000000 : ℚ) : ℝ) ≤ stT304 154 := by
  have hc : ((-759819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-612279626037/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-759819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c155 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((223339/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1165093/10000000) (δ := 15353/1000000000) (ψ := 142517/250000) 304 244
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t155 : ((89685023883/1250000000000 : ℚ) : ℝ) ≤ stT304 155 := by
  have hc : ((111657/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89685023883/1250000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((111657/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c156 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((81749/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3722391/10000000) (δ := 15353/1000000000) (ψ := 142517/250000) 304 244
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t156 : ((102142899/15625000000 : ℚ) : ℝ) ≤ stT304 156 := by
  have hc : ((81649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102142899/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((81649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c157 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-958283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -285173/400000) (δ := 15343/1000000000) (ψ := 142517/250000) 304 245
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t157 : ((-764873013321/10000000000000 : ℚ) : ℝ) ≤ stT304 157 := by
  have hc : ((-958383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-764873013321/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-958383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c158 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((75571/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2303933/10000000) (δ := 15343/1000000000) (ψ := 142517/250000) 304 245
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t158 : ((120222187169/2500000000000 : ℚ) : ℝ) ≤ stT304 158 := by
  have hc : ((151117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120222187169/2500000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((151117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c159 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((135827/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2491059/10000000) (δ := 15343/1000000000) (ψ := 142517/250000) 304 245
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t159 : ((53848955951/1250000000000 : ℚ) : ℝ) ≤ stT304 159 := by
  have hc : ((67901/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53848955951/1250000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((67901/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c160 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-38861/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1451191/2000000) (δ := 15343/1000000000) (ψ := 142517/250000) 304 245
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t160 : ((-614510061/8000000000 : ℚ) : ℝ) ≤ stT304 160 := by
  have hc : ((-7773/8000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-614510061/8000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-7773/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c161 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((41983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -929207/2500000) (δ := 3047/200000000) (ψ := 142517/250000) 304 246
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t161 : ((3304781663/500000000000 : ℚ) : ℝ) ≤ stT304 161 := by
  have hc : ((41933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3304781663/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((41933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c162 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((922751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 247273/2500000) (δ := 3047/200000000) (ψ := 142517/250000) 304 246
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t162 : ((362451450887/5000000000000 : ℚ) : ℝ) ≤ stT304 162 := by
  have hc : ((922651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362451450887/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((922651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c163 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-320433/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 708257/1250000) (δ := 3047/200000000) (ψ := 142517/250000) 304 246
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t163 : ((-251021835063/5000000000000 : ℚ) : ℝ) ≤ stT304 163 := by
  have hc : ((-320483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251021835063/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-320483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c164 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-553567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1078719/2000000) (δ := 611/40000000) (ψ := 142517/250000) 304 247
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t164 : ((-432341396623/10000000000000 : ℚ) : ℝ) ≤ stT304 164 := by
  have hc : ((-553667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432341396623/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-553667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c165 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((95251/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154711/2000000) (δ := 611/40000000) (ψ := 142517/250000) 304 247
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t165 : ((37072464009/500000000000 : ℚ) : ℝ) ≤ stT304 165 := by
  have hc : ((95241/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37072464009/500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((95241/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c166 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((21673/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3818593/10000000) (δ := 611/40000000) (ψ := 142517/250000) 304 247
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t166 : ((335653829/100000000000 : ℚ) : ℝ) ≤ stT304 166 := by
  have hc : ((21623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335653829/100000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((21623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c167 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-39107/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3662367/5000000) (δ := 7691/500000000) (ψ := 142517/250000) 304 248
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t167 : ((-472891101/6250000000 : ℚ) : ℝ) ≤ stT304 167 := by
  have hc : ((-39111/40000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472891101/6250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-39111/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c168 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((440193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1393729/5000000) (δ := 7691/500000000) (ψ := 142517/250000) 304 248
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t168 : ((84884697747/2500000000000 : ℚ) : ℝ) ≤ stT304 168 := by
  have hc : ((440093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84884697747/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((440093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c169 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((385879/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172299/1000000) (δ := 7691/500000000) (ψ := 142517/250000) 304 248
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t169 : ((29679124167/500000000000 : ℚ) : ℝ) ≤ stT304 169 := by
  have hc : ((385829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29679124167/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((385829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c170 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-395337/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3103381/5000000) (δ := 7691/500000000) (ψ := 142517/250000) 304 248
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t170 : ((-60649598091/1000000000000 : ℚ) : ℝ) ≤ stT304 170 := by
  have hc : ((-395387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60649598091/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-395387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c171 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-215993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2521863/5000000) (δ := 7657/500000000) (ψ := 142517/250000) 304 249
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t171 : ((-2065155037/62500000000 : ℚ) : ℝ) ≤ stT304 171 := by
  have hc : ((-216043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2065155037/62500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-216043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c172 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((485081/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -306121/5000000) (δ := 7657/500000000) (ψ := 142517/250000) 304 249
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t172 : ((92458064313/1250000000000 : ℚ) : ℝ) ≤ stT304 172 := by
  have hc : ((485031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92458064313/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((485031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c173 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((53349/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1896777/5000000) (δ := 7657/500000000) (ψ := 142517/250000) 304 249
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t173 : ((8096883193/2000000000000 : ℚ) : ℝ) ≤ stT304 173 := by
  have hc : ((53249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8096883193/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((53249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c174 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-49591/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7533997/10000000) (δ := 15207/1000000000) (ψ := 142517/250000) 304 250
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t174 : ((-9399669501/125000000000 : ℚ) : ℝ) ≤ stT304 174 := by
  have hc : ((-12399/12500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9399669501/125000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-12399/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c175 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((1843/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -635733/2000000) (δ := 15207/1000000000) (ψ := 142517/250000) 304 250
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t175 : ((1392702849/62500000000 : ℚ) : ℝ) ≤ stT304 175 := by
  have hc : ((14739/50000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1392702849/62500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((14739/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c176 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((89573/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230363/2000000) (δ := 15207/1000000000) (ψ := 142517/250000) 304 250
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t176 : ((33755309507/500000000000 : ℚ) : ℝ) ≤ stT304 176 := by
  have hc : ((89563/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33755309507/500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((89563/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c177 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-287389/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5457823/10000000) (δ := 15207/1000000000) (ψ := 142517/250000) 304 250
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t177 : ((-216052662033/5000000000000 : ℚ) : ℝ) ≤ stT304 177 := by
  have hc : ((-287439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216052662033/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-287439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c178 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-728811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1492113/2500000) (δ := 1913/125000000) (ψ := 142517/250000) 304 251
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t178 : ((-136585529913/2500000000000 : ℚ) : ℝ) ≤ stT304 178 := by
  have hc : ((-728911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136585529913/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-728911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c179 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((774873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106919/625000) (δ := 1913/125000000) (ψ := 142517/250000) 304 251
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t179 : ((115818491451/2000000000000 : ℚ) : ℝ) ≤ stT304 179 := by
  have hc : ((774773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115818491451/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((774773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c180 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((532451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 315407/1250000) (δ := 1913/125000000) (ψ := 142517/250000) 304 251
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t180 : ((79358095921/2000000000000 : ℚ) : ℝ) ≤ stT304 180 := by
  have hc : ((532351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79358095921/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((532351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c181 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-180257/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420863/625000) (δ := 1913/125000000) (ψ := 142517/250000) 304 251
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t181 : ((-26799798543/400000000000 : ℚ) : ℝ) ≤ stT304 181 := by
  have hc : ((-180277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26799798543/400000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-180277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c182 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-168603/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239343/500000) (δ := 481/31250000) (ψ := 142517/250000) 304 252
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t182 : ((-100011229/4000000000 : ℚ) : ℝ) ≤ stT304 182 := by
  have hc : ((-168653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100011229/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-168653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c183 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((193833/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15561/250000) (δ := 481/31250000) (ψ := 142517/250000) 304 252
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t183 : ((143270639673/2000000000000 : ℚ) : ℝ) ≤ stT304 183 := by
  have hc : ((193813/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143270639673/2000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((193813/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c184 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((40593/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 439907/1250000) (δ := 481/31250000) (ψ := 142517/250000) 304 252
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t184 : ((3738386839/312500000000 : ℚ) : ℝ) ≤ stT304 184 := by
  have hc : ((5071/31250 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3738386839/312500000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((5071/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c185 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-996289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909633/2500000) (δ := 481/31250000) (ψ := 142517/250000) 304 252
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t185 : ((-146512027727/2000000000000 : ℚ) : ℝ) ≤ stT304 185 := by
  have hc : ((-996389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146512027727/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-996389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c186 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-4543/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3972423/10000000) (δ := 3057/200000000) (ψ := 142517/250000) 304 253
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t186 : ((-104669439/78125000000 : ℚ) : ℝ) ≤ stT304 186 := by
  have hc : ((-571/31250 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104669439/78125000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-571/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c187 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((249789/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102697/10000000) (δ := 3057/200000000) (ψ := 142517/250000) 304 253
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t187 : ((5707669369/78125000000 : ℚ) : ℝ) ≤ stT304 187 := by
  have hc : ((62441/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5707669369/78125000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((62441/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c188 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-45739/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 831201/2000000) (δ := 3057/200000000) (ψ := 142517/250000) 304 253
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t188 : ((-1335802497/200000000000 : ℚ) : ℝ) ≤ stT304 188 := by
  have hc : ((-45789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1335802497/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-45789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c189 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-495547/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3760041/5000000) (δ := 609/40000000) (ψ := 142517/250000) 304 254
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t189 : ((-360493788621/5000000000000 : ℚ) : ℝ) ≤ stT304 189 := by
  have hc : ((-495597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-360493788621/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-495597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c190 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((166197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1754781/5000000) (δ := 609/40000000) (ψ := 142517/250000) 304 254
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t190 : ((30124846793/2500000000000 : ℚ) : ℝ) ≤ stT304 190 := by
  have hc : ((166097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30124846793/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((166097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c191 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((490813/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239991/5000000) (δ := 609/40000000) (ψ := 142517/250000) 304 254
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t191 : ((177551673481/2500000000000 : ℚ) : ℝ) ≤ stT304 191 := by
  have hc : ((490763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177551673481/2500000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((490763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c192 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-207143/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2224313/5000000) (δ := 609/40000000) (ψ := 142517/250000) 304 254
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t192 : ((-18695598273/1250000000000 : ℚ) : ℝ) ≤ stT304 192 := by
  have hc : ((-207243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18695598273/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-207243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c193 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-976531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7311289/10000000) (δ := 3833/250000000) (ψ := 142517/250000) 304 255
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t193 : ((-87874327487/1250000000000 : ℚ) : ℝ) ≤ stT304 193 := by
  have hc : ((-976631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87874327487/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-976631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c194 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((43129/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3383609/10000000) (δ := 3833/250000000) (ψ := 142517/250000) 304 255
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t194 : ((15475225711/1000000000000 : ℚ) : ℝ) ≤ stT304 194 := by
  have hc : ((43109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15475225711/1000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((43109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c195 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((489063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104771/2000000) (δ := 3833/250000000) (ψ := 142517/250000) 304 255
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t195 : ((175094527741/2500000000000 : ℚ) : ℝ) ≤ stT304 195 := by
  have hc : ((489013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175094527741/2500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((489013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c196 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-96263/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4411331/10000000) (δ := 3833/250000000) (ψ := 142517/250000) 304 255
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t196 : ((-34397513759/2500000000000 : ℚ) : ℝ) ≤ stT304 196 := by
  have hc : ((-96313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34397513759/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-96313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c197 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-49279/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7428917/10000000) (δ := 3841/250000000) (ψ := 142517/250000) 304 256
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t197 : ((-8778355191/125000000000 : ℚ) : ℝ) ≤ stT304 197 := by
  have hc : ((-12321/12500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8778355191/125000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-12321/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c198 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((138031/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3580809/10000000) (δ := 3841/250000000) (ψ := 142517/250000) 304 256
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t198 : ((98023285839/10000000000000 : ℚ) : ℝ) ≤ stT304 198 := by
  have hc : ((137931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98023285839/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((137931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c199 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((995087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 247919/10000000) (δ := 3841/250000000) (ψ := 142517/250000) 304 256
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t199 : ((705327379547/10000000000000 : ℚ) : ℝ) ≤ stT304 199 := by
  have hc : ((994987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((705327379547/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((994987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c200 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-13037/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4057419/10000000) (δ := 3841/250000000) (ψ := 142517/250000) 304 256
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t200 : ((-4618115817/1250000000000 : ℚ) : ℝ) ≤ stT304 200 := by
  have hc : ((-6531/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4618115817/1250000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-6531/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c201 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-999997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1569599/2000000) (δ := 3841/250000000) (ψ := 142517/250000) 304 256
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t201 : ((-352707209281/5000000000000 : ℚ) : ℝ) ≤ stT304 201 := by
  have hc : ((-1000097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352707209281/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-1000097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c202 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-12897/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1022079/2500000) (δ := 1907/125000000) (ψ := 142517/250000) 304 257
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t202 : ((-4544187683/1000000000000 : ℚ) : ℝ) ≤ stT304 202 := by
  have hc : ((-12917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4544187683/1000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-12917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c203 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((61939/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41901/1250000) (δ := 1907/125000000) (ψ := 142517/250000) 304 257
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t203 : ((86936487561/1250000000000 : ℚ) : ℝ) ≤ stT304 203 := by
  have hc : ((247731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86936487561/1250000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((247731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c204 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((209461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 424929/1250000) (δ := 1907/125000000) (ψ := 142517/250000) 304 257
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t204 : ((7329100527/500000000000 : ℚ) : ℝ) ≤ stT304 204 := by
  have hc : ((209361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7329100527/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((209361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c205 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-956727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 889479/1250000) (δ := 1907/125000000) (ψ := 142517/250000) 304 257
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t205 : ((-668277638437/10000000000000 : ℚ) : ℝ) ≤ stT304 205 := by
  have hc : ((-956827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-668277638437/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-956827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c206 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-377163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4893819/10000000) (δ := 7627/500000000) (ψ := 142517/250000) 304 258
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t206 : ((-131425979521/5000000000000 : ℚ) : ℝ) ≤ stT304 206 := by
  have hc : ((-377263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131425979521/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-377263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c207 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((884499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1213443/10000000) (δ := 7627/500000000) (ψ := 142517/250000) 304 258
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t207 : ((76837469519/1250000000000 : ℚ) : ℝ) ≤ stT304 207 := by
  have hc : ((884399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76837469519/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((884399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c208 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((3483/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97969/400000) (δ := 7627/500000000) (ψ := 142517/250000) 304 258
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t208 : ((154533873/4000000000 : ℚ) : ℝ) ≤ stT304 208 := by
  have hc : ((27859/50000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154533873/4000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((27859/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c209 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-762351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6094337/10000000) (δ := 7627/500000000) (ψ := 142517/250000) 304 258
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t209 : ((-105479758693/2000000000000 : ℚ) : ℝ) ≤ stT304 209 := by
  have hc : ((-762451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105479758693/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-762451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c210 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-733577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2992959/5000000) (δ := 15361/1000000000) (ψ := 142517/250000) 304 259
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t210 : ((-253142776341/5000000000000 : ℚ) : ℝ) ≤ stT304 210 := by
  have hc : ((-733677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253142776341/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-733677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c211 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((581533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1187731/5000000) (δ := 15361/1000000000) (ψ := 142517/250000) 304 259
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t211 : ((100068689331/2500000000000 : ℚ) : ℝ) ≤ stT304 211 := by
  have hc : ((581433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100068689331/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((581433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c212 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((883667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608947/5000000) (δ := 15361/1000000000) (ψ := 142517/250000) 304 259
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t212 : ((303417791367/5000000000000 : ℚ) : ℝ) ≤ stT304 212 := by
  have hc : ((883567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303417791367/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((883567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c213 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-85009/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2397189/5000000) (δ := 15361/1000000000) (ψ := 142517/250000) 304 259
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t213 : ((-29132180713/1250000000000 : ℚ) : ℝ) ≤ stT304 213 := by
  have hc : ((-42517/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29132180713/1250000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-42517/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c214 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-490027/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3676911/5000000) (δ := 3067/200000000) (ψ := 142517/250000) 304 260
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t214 : ((-167504888061/2500000000000 : ℚ) : ℝ) ≤ stT304 214 := by
  have hc : ((-490077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167504888061/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-490077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c215 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((46499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1905351/5000000) (δ := 3067/200000000) (ψ := 142517/250000) 304 260
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t215 : ((15821919803/5000000000000 : ℚ) : ℝ) ≤ stT304 215 := by
  have hc : ((46399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15821919803/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((46399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c216 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((198711/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141999/5000000) (δ := 3067/200000000) (ψ := 142517/250000) 304 260
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t216 : ((135191939383/2000000000000 : ℚ) : ℝ) ≤ stT304 216 := by
  have hc : ((198691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135191939383/2000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((198691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c217 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((69149/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1613183/5000000) (δ := 3067/200000000) (ψ := 142517/250000) 304 260
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t217 : ((2932775791/156250000000 : ℚ) : ℝ) ≤ stT304 217 := by
  have hc : ((17281/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2932775791/156250000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((17281/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c218 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-898987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3360309/5000000) (δ := 3067/200000000) (ψ := 142517/250000) 304 260
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t218 : ((-304469518941/5000000000000 : ℚ) : ℝ) ≤ stT304 218 := by
  have hc : ((-899087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304469518941/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-899087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c219 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-23657/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5509053/10000000) (δ := 3807/250000000) (ψ := 142517/250000) 304 261
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t219 : ((-7994318409/200000000000 : ℚ) : ℝ) ≤ stT304 219 := by
  have hc : ((-23661/40000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7994318409/200000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-23661/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c220 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((341601/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409329/2000000) (δ := 3807/250000000) (ψ := 142517/250000) 304 261
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t220 : ((230273342649/5000000000000 : ℚ) : ℝ) ≤ stT304 220 := by
  have hc : ((341551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230273342649/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((341551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c221 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((13238/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1400107/10000000) (δ := 3807/250000000) (ψ := 142517/250000) 304 261
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t221 : ((4451890443/78125000000 : ℚ) : ℝ) ≤ stT304 221 := by
  have hc : ((211783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4451890443/78125000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((211783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c222 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-353851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4831203/10000000) (δ := 3807/250000000) (ψ := 142517/250000) 304 261
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t222 : ((-237556691307/10000000000000 : ℚ) : ℝ) ≤ stT304 222 := by
  have hc : ((-353951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237556691307/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-353951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c223 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-123459/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932627/1250000) (δ := 15283/1000000000) (ψ := 142517/250000) 304 262
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t223 : ((-3307307599/50000000000 : ℚ) : ℝ) ≤ stT304 223 := by
  have hc : ((-246943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3307307599/50000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-246943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c224 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-53397/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1015137/2500000) (δ := 15283/1000000000) (ψ := 142517/250000) 304 262
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t224 : ((-17872117269/5000000000000 : ℚ) : ℝ) ≤ stT304 224 := by
  have hc : ((-53497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17872117269/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-53497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c225 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((963749/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168801/2500000) (δ := 15283/1000000000) (ψ := 142517/250000) 304 262
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t225 : ((321216012117/5000000000000 : ℚ) : ℝ) ≤ stT304 225 := by
  have hc : ((963649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321216012117/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((963649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c226 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((29567/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1347527/5000000) (δ := 30483/1000000000) (ψ := 142517/250000) 304 262
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t226 : ((7865406117/250000000000 : ℚ) : ℝ) ≤ stT304 226 := by
  have hc : ((118243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7865406117/250000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((118243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c227 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-150177/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1512623/2500000) (δ := 15283/1000000000) (ψ := 142517/250000) 304 262
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t227 : ((-24922338407/500000000000 : ℚ) : ℝ) ≤ stT304 227 := by
  have hc : ((-150197/200000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24922338407/500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-150197/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c228 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-16337/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263363/2000000) (δ := 1539/100000000) (ψ := 142517/250000) 304 263
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t228 : ((-10820780513/200000000000 : ℚ) : ℝ) ≤ stT304 228 := by
  have hc : ((-16339/20000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10820780513/200000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-16339/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c229 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((365803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2990751/10000000) (δ := 1539/100000000) (ψ := 142517/250000) 304 263
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t229 : ((120831562527/5000000000000 : ℚ) : ℝ) ≤ stT304 229 := by
  have hc : ((365703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120831562527/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((365703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c230 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((495889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 320797/10000000) (δ := 1539/100000000) (ψ := 142517/250000) 304 263
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t230 : ((16347315991/250000000000 : ℚ) : ℝ) ≤ stT304 230 := by
  have hc : ((495839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16347315991/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((495839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c231 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((123289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3617981/10000000) (δ := 1539/100000000) (ψ := 142517/250000) 304 263
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t231 : ((81052325739/10000000000000 : ℚ) : ℝ) ≤ stT304 231 := by
  have hc : ((123189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81052325739/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((123189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c232 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-928203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6900877/10000000) (δ := 1539/100000000) (ψ := 142517/250000) 304 263
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t232 : ((-609461553499/10000000000000 : ℚ) : ℝ) ≤ stT304 232 := by
  have hc : ((-928303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-609461553499/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-928303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c233 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-300401/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5538251/10000000) (δ := 7653/500000000) (ψ := 142517/250000) 304 264
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t233 : ((-98416030011/2500000000000 : ℚ) : ℝ) ≤ stT304 233 := by
  have hc : ((-300451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98416030011/2500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-300451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c234 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((61109/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2283399/10000000) (δ := 7653/500000000) (ψ := 142517/250000) 304 264
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t234 : ((998540957/25000000000 : ℚ) : ℝ) ≤ stT304 234 := by
  have hc : ((61099/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((998540957/25000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((61099/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c235 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((927541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191509/2000000) (δ := 7653/500000000) (ψ := 142517/250000) 304 264
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t235 : ((75624466581/1250000000000 : ℚ) : ℝ) ≤ stT304 235 := by
  have hc : ((927441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75624466581/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((927441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c236 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-51457/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4184733/10000000) (δ := 7653/500000000) (ψ := 142517/250000) 304 264
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t236 : ((-6705644823/1000000000000 : ℚ) : ℝ) ≤ stT304 236 := by
  have hc : ((-51507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6705644823/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-51507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c237 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-98343/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7398241/10000000) (δ := 7653/500000000) (ψ := 142517/250000) 304 264
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t237 : ((-6388715821/100000000000 : ℚ) : ℝ) ≤ stT304 237 := by
  have hc : ((-98353/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6388715821/100000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-98353/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c238 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-14239/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2554871/5000000) (δ := 3801/250000000) (ψ := 142517/250000) 304 265
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t238 : ((-18463604787/625000000000 : ℚ) : ℝ) ≤ stT304 238 := by
  have hc : ((-113937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18463604787/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-113937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c239 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((718429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -961569/5000000) (δ := 3801/250000000) (ψ := 142517/250000) 304 265
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t239 : ((232324120167/5000000000000 : ℚ) : ℝ) ≤ stT304 239 := by
  have hc : ((718329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232324120167/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((718329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c240 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((877551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 625083/5000000) (δ := 3801/250000000) (ψ := 142517/250000) 304 265
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t240 : ((566391988147/10000000000000 : ℚ) : ℝ) ≤ stT304 240 := by
  have hc : ((877451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((566391988147/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((877451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c241 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-192101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2205123/5000000) (δ := 3801/250000000) (ψ := 142517/250000) 304 265
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t241 : ((-123807619557/10000000000000 : ℚ) : ℝ) ≤ stT304 241 := by
  have hc : ((-192201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123807619557/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-192201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c242 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-248241/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3778627/5000000) (δ := 3801/250000000) (ψ := 142517/250000) 304 265
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t242 : ((-3191831829/50000000000 : ℚ) : ℝ) ≤ stT304 242 := by
  have hc : ((-124133/125000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3191831829/50000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-124133/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c243 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-422211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5016697/10000000) (δ := 15311/1000000000) (ψ := 142517/250000) 304 266
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t243 : ((-270912928811/10000000000000 : ℚ) : ℝ) ≤ stT304 243 := by
  have hc : ((-422311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270912928811/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-422311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c244 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((726067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1895529/10000000) (δ := 15311/1000000000) (ψ := 142517/250000) 304 266
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t244 : ((58094057241/1250000000000 : ℚ) : ℝ) ≤ stT304 244 := by
  have hc : ((725967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58094057241/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((725967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c245 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((884613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1212833/10000000) (δ := 30511/1000000000) (ψ := 142517/250000) 304 266
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t245 : ((141273531847/2500000000000 : ℚ) : ℝ) ≤ stT304 245 := by
  have hc : ((884513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141273531847/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((884513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c246 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-152043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4308579/10000000) (δ := 15311/1000000000) (ψ := 142517/250000) 304 266
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t246 : ((-97002877511/10000000000000 : ℚ) : ℝ) ≤ stT304 246 := by
  have hc : ((-152143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97002877511/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-152143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c247 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-245739/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7391747/10000000) (δ := 15311/1000000000) (ψ := 142517/250000) 304 266
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t247 : ((-7818797337/125000000000 : ℚ) : ℝ) ≤ stT304 247 := by
  have hc : ((-61441/62500 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7818797337/125000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-61441/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c248 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((-7864/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5245513/10000000) (δ := 3077/200000000) (ψ := 142517/250000) 304 267
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t248 : ((-79914240849/2500000000000 : ℚ) : ℝ) ≤ stT304 248 := by
  have hc : ((-125849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79914240849/2500000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-125849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c249 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((64109/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2187197/10000000) (δ := 3077/200000000) (ψ := 142517/250000) 304 267
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t249 : ((10155268669/250000000000 : ℚ) : ℝ) ≤ stT304 249 := by
  have hc : ((64099/100000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10155268669/250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((64099/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_c250 :
    |Real.cos (((304 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((470777/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 858959/10000000) (δ := 3077/200000000) (ψ := 142517/250000) 304 267
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st304_t250 : ((59542728957/1000000000000 : ℚ) : ℝ) ≤ stT304 250 := by
  have hc : ((470727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((304 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((142517/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st304_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59542728957/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((470727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st304_p1 : ((210441/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT304 (i+1) := by
  rw [Finset.sum_range_one]
  exact st304_t1

theorem st304_p2 : ((437686793953/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT304 (i+1))
      = (∑ i ∈ Finset.range 1, stT304 (i+1)) + stT304 2 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 1
    simpa using h
  have hprev := st304_p1
  have hstep := st304_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p3 : ((706963785483/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT304 (i+1))
      = (∑ i ∈ Finset.range 2, stT304 (i+1)) + stT304 3 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 2
    simpa using h
  have hprev := st304_p2
  have hstep := st304_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p4 : ((1203891785483/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT304 (i+1))
      = (∑ i ∈ Finset.range 3, stT304 (i+1)) + stT304 4 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 3
    simpa using h
  have hprev := st304_p3
  have hstep := st304_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p5 : ((20070819209/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT304 (i+1))
      = (∑ i ∈ Finset.range 4, stT304 (i+1)) + stT304 5 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 4
    simpa using h
  have hprev := st304_p4
  have hstep := st304_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p6 : ((4772208167089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT304 (i+1))
      = (∑ i ∈ Finset.range 5, stT304 (i+1)) + stT304 6 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 5
    simpa using h
  have hprev := st304_p5
  have hstep := st304_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p7 : ((6535859980903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT304 (i+1))
      = (∑ i ∈ Finset.range 6, stT304 (i+1)) + stT304 7 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 6
    simpa using h
  have hprev := st304_p6
  have hstep := st304_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p8 : ((956127411107/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT304 (i+1))
      = (∑ i ∈ Finset.range 7, stT304 (i+1)) + stT304 8 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 7
    simpa using h
  have hprev := st304_p7
  have hstep := st304_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p9 : ((5115250355407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT304 (i+1))
      = (∑ i ∈ Finset.range 8, stT304 (i+1)) + stT304 9 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 8
    simpa using h
  have hprev := st304_p8
  have hstep := st304_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p10 : ((22413871003/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT304 (i+1))
      = (∑ i ∈ Finset.range 9, stT304 (i+1)) + stT304 10 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 9
    simpa using h
  have hprev := st304_p9
  have hstep := st304_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p11 : ((2333547579699/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT304 (i+1))
      = (∑ i ∈ Finset.range 10, stT304 (i+1)) + stT304 11 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 10
    simpa using h
  have hprev := st304_p10
  have hstep := st304_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p12 : ((67761838613/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT304 (i+1))
      = (∑ i ∈ Finset.range 11, stT304 (i+1)) + stT304 12 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 11
    simpa using h
  have hprev := st304_p11
  have hstep := st304_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p13 : ((163206729571/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT304 (i+1))
      = (∑ i ∈ Finset.range 12, stT304 (i+1)) + stT304 13 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 12
    simpa using h
  have hprev := st304_p12
  have hstep := st304_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p14 : ((14110446059617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT304 (i+1))
      = (∑ i ∈ Finset.range 13, stT304 (i+1)) + stT304 14 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 13
    simpa using h
  have hprev := st304_p13
  have hstep := st304_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p15 : ((16467702988073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT304 (i+1))
      = (∑ i ∈ Finset.range 14, stT304 (i+1)) + stT304 15 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 14
    simpa using h
  have hprev := st304_p14
  have hstep := st304_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p16 : ((18815815488073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT304 (i+1))
      = (∑ i ∈ Finset.range 15, stT304 (i+1)) + stT304 16 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 15
    simpa using h
  have hprev := st304_p15
  have hstep := st304_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p17 : ((21235057165597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT304 (i+1))
      = (∑ i ∈ Finset.range 16, stT304 (i+1)) + stT304 17 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 16
    simpa using h
  have hprev := st304_p16
  have hstep := st304_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p18 : ((4260066506573/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT304 (i+1))
      = (∑ i ∈ Finset.range 17, stT304 (i+1)) + stT304 18 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 17
    simpa using h
  have hprev := st304_p17
  have hstep := st304_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p19 : ((19725833544201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT304 (i+1))
      = (∑ i ∈ Finset.range 18, stT304 (i+1)) + stT304 19 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 18
    simpa using h
  have hprev := st304_p18
  have hstep := st304_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p20 : ((21063600876157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT304 (i+1))
      = (∑ i ∈ Finset.range 19, stT304 (i+1)) + stT304 20 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 19
    simpa using h
  have hprev := st304_p19
  have hstep := st304_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p21 : ((21569957823633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT304 (i+1))
      = (∑ i ∈ Finset.range 20, stT304 (i+1)) + stT304 21 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 20
    simpa using h
  have hprev := st304_p20
  have hstep := st304_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p22 : ((3898714356069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT304 (i+1))
      = (∑ i ∈ Finset.range 21, stT304 (i+1)) + stT304 22 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 21
    simpa using h
  have hprev := st304_p21
  have hstep := st304_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p23 : ((3584491345149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT304 (i+1))
      = (∑ i ∈ Finset.range 22, stT304 (i+1)) + stT304 23 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 22
    simpa using h
  have hprev := st304_p22
  have hstep := st304_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p24 : ((3395409057447/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT304 (i+1))
      = (∑ i ∈ Finset.range 23, stT304 (i+1)) + stT304 24 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 23
    simpa using h
  have hprev := st304_p23
  have hstep := st304_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p25 : ((1973223836451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT304 (i+1))
      = (∑ i ∈ Finset.range 24, stT304 (i+1)) + stT304 25 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 24
    simpa using h
  have hprev := st304_p24
  have hstep := st304_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p26 : ((55624389289/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT304 (i+1))
      = (∑ i ∈ Finset.range 25, stT304 (i+1)) + stT304 26 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 25
    simpa using h
  have hprev := st304_p25
  have hstep := st304_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p27 : ((6285119797059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT304 (i+1))
      = (∑ i ∈ Finset.range 26, stT304 (i+1)) + stT304 27 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 26
    simpa using h
  have hprev := st304_p26
  have hstep := st304_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p28 : ((6924616663639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT304 (i+1))
      = (∑ i ∈ Finset.range 27, stT304 (i+1)) + stT304 28 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 27
    simpa using h
  have hprev := st304_p27
  have hstep := st304_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p29 : ((14738440842187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT304 (i+1))
      = (∑ i ∈ Finset.range 28, stT304 (i+1)) + stT304 29 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 28
    simpa using h
  have hprev := st304_p28
  have hstep := st304_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p30 : ((12945390578439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT304 (i+1))
      = (∑ i ∈ Finset.range 29, stT304 (i+1)) + stT304 30 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 29
    simpa using h
  have hprev := st304_p29
  have hstep := st304_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p31 : ((14630336147753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT304 (i+1))
      = (∑ i ∈ Finset.range 30, stT304 (i+1)) + stT304 31 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 30
    simpa using h
  have hprev := st304_p30
  have hstep := st304_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p32 : ((13151606123321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT304 (i+1))
      = (∑ i ∈ Finset.range 31, stT304 (i+1)) + stT304 32 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 31
    simpa using h
  have hprev := st304_p31
  have hstep := st304_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p33 : ((14670760449209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT304 (i+1))
      = (∑ i ∈ Finset.range 32, stT304 (i+1)) + stT304 33 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 32
    simpa using h
  have hprev := st304_p32
  have hstep := st304_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p34 : ((12977630230793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT304 (i+1))
      = (∑ i ∈ Finset.range 33, stT304 (i+1)) + stT304 34 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 33
    simpa using h
  have hprev := st304_p33
  have hstep := st304_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p35 : ((14497921981229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT304 (i+1))
      = (∑ i ∈ Finset.range 34, stT304 (i+1)) + stT304 35 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 34
    simpa using h
  have hprev := st304_p34
  have hstep := st304_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p36 : ((3518192557383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT304 (i+1))
      = (∑ i ∈ Finset.range 35, stT304 (i+1)) + stT304 36 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 35
    simpa using h
  have hprev := st304_p35
  have hstep := st304_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p37 : ((3212752367303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT304 (i+1))
      = (∑ i ∈ Finset.range 36, stT304 (i+1)) + stT304 37 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 36
    simpa using h
  have hprev := st304_p36
  have hstep := st304_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p38 : ((142037607461/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT304 (i+1))
      = (∑ i ∈ Finset.range 37, stT304 (i+1)) + stT304 38 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 37
    simpa using h
  have hprev := st304_p37
  have hstep := st304_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p39 : ((15029514136023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT304 (i+1))
      = (∑ i ∈ Finset.range 38, stT304 (i+1)) + stT304 39 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 38
    simpa using h
  have hprev := st304_p38
  have hstep := st304_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p40 : ((13819313507701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT304 (i+1))
      = (∑ i ∈ Finset.range 39, stT304 (i+1)) + stT304 40 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 39
    simpa using h
  have hprev := st304_p39
  have hstep := st304_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p41 : ((12467023314357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT304 (i+1))
      = (∑ i ∈ Finset.range 40, stT304 (i+1)) + stT304 41 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 40
    simpa using h
  have hprev := st304_p40
  have hstep := st304_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p42 : ((2492065926573/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT304 (i+1))
      = (∑ i ∈ Finset.range 41, stT304 (i+1)) + stT304 42 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 41
    simpa using h
  have hprev := st304_p41
  have hstep := st304_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p43 : ((1362167433469/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT304 (i+1))
      = (∑ i ∈ Finset.range 42, stT304 (i+1)) + stT304 43 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 42
    simpa using h
  have hprev := st304_p42
  have hstep := st304_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p44 : ((1512907957909/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT304 (i+1))
      = (∑ i ∈ Finset.range 43, stT304 (i+1)) + stT304 44 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 43
    simpa using h
  have hprev := st304_p43
  have hstep := st304_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p45 : ((8200202811321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT304 (i+1))
      = (∑ i ∈ Finset.range 44, stT304 (i+1)) + stT304 45 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 44
    simpa using h
  have hprev := st304_p44
  have hstep := st304_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p46 : ((3452150834853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT304 (i+1))
      = (∑ i ∈ Finset.range 45, stT304 (i+1)) + stT304 46 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 45
    simpa using h
  have hprev := st304_p45
  have hstep := st304_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p47 : ((17785964085099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT304 (i+1))
      = (∑ i ∈ Finset.range 46, stT304 (i+1)) + stT304 47 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 46
    simpa using h
  have hprev := st304_p46
  have hstep := st304_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p48 : ((18144870825849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT304 (i+1))
      = (∑ i ∈ Finset.range 47, stT304 (i+1)) + stT304 48 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 47
    simpa using h
  have hprev := st304_p47
  have hstep := st304_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p49 : ((18520739284517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT304 (i+1))
      = (∑ i ∈ Finset.range 48, stT304 (i+1)) + stT304 49 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 48
    simpa using h
  have hprev := st304_p48
  have hstep := st304_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p50 : ((19081565248649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT304 (i+1))
      = (∑ i ∈ Finset.range 49, stT304 (i+1)) + stT304 50 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 49
    simpa using h
  have hprev := st304_p49
  have hstep := st304_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p51 : ((19952158532489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT304 (i+1))
      = (∑ i ∈ Finset.range 50, stT304 (i+1)) + stT304 51 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 50
    simpa using h
  have hprev := st304_p50
  have hstep := st304_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p52 : ((21155717470739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT304 (i+1))
      = (∑ i ∈ Finset.range 51, stT304 (i+1)) + stT304 52 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 51
    simpa using h
  have hprev := st304_p51
  have hstep := st304_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p53 : ((5632170249301/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT304 (i+1))
      = (∑ i ∈ Finset.range 52, stT304 (i+1)) + stT304 53 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 52
    simpa using h
  have hprev := st304_p52
  have hstep := st304_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p54 : ((23671515759247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT304 (i+1))
      = (∑ i ∈ Finset.range 53, stT304 (i+1)) + stT304 54 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 53
    simpa using h
  have hprev := st304_p53
  have hstep := st304_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p55 : ((962384586249/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT304 (i+1))
      = (∑ i ∈ Finset.range 54, stT304 (i+1)) + stT304 55 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 54
    simpa using h
  have hprev := st304_p54
  have hstep := st304_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p56 : ((11701521464497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT304 (i+1))
      = (∑ i ∈ Finset.range 55, stT304 (i+1)) + stT304 56 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 55
    simpa using h
  have hprev := st304_p55
  have hstep := st304_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p57 : ((22094212267709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT304 (i+1))
      = (∑ i ∈ Finset.range 56, stT304 (i+1)) + stT304 57 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 56
    simpa using h
  have hprev := st304_p56
  have hstep := st304_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p58 : ((10609462225887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT304 (i+1))
      = (∑ i ∈ Finset.range 57, stT304 (i+1)) + stT304 58 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 57
    simpa using h
  have hprev := st304_p57
  have hstep := st304_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p59 : ((21673740675813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT304 (i+1))
      = (∑ i ∈ Finset.range 58, stT304 (i+1)) + stT304 59 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 58
    simpa using h
  have hprev := st304_p58
  have hstep := st304_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p60 : ((22963574072207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT304 (i+1))
      = (∑ i ∈ Finset.range 59, stT304 (i+1)) + stT304 60 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 59
    simpa using h
  have hprev := st304_p59
  have hstep := st304_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p61 : ((23405490526671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT304 (i+1))
      = (∑ i ∈ Finset.range 60, stT304 (i+1)) + stT304 61 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 60
    simpa using h
  have hprev := st304_p60
  have hstep := st304_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p62 : ((22345360167177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT304 (i+1))
      = (∑ i ∈ Finset.range 61, stT304 (i+1)) + stT304 62 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 61
    simpa using h
  have hprev := st304_p61
  have hstep := st304_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p63 : ((21500338411547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT304 (i+1))
      = (∑ i ∈ Finset.range 62, stT304 (i+1)) + stT304 63 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 62
    simpa using h
  have hprev := st304_p62
  have hstep := st304_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p64 : ((22361967161547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT304 (i+1))
      = (∑ i ∈ Finset.range 63, stT304 (i+1)) + stT304 64 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 63
    simpa using h
  have hprev := st304_p63
  have hstep := st304_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p65 : ((23261082298377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT304 (i+1))
      = (∑ i ∈ Finset.range 64, stT304 (i+1)) + stT304 65 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 64
    simpa using h
  have hprev := st304_p64
  have hstep := st304_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p66 : ((11175963624231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT304 (i+1))
      = (∑ i ∈ Finset.range 65, stT304 (i+1)) + stT304 66 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 65
    simpa using h
  have hprev := st304_p65
  have hstep := st304_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p67 : ((676965886631/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT304 (i+1))
      = (∑ i ∈ Finset.range 66, stT304 (i+1)) + stT304 67 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 66
    simpa using h
  have hprev := st304_p66
  have hstep := st304_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p68 : ((356002805551/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT304 (i+1))
      = (∑ i ∈ Finset.range 67, stT304 (i+1)) + stT304 68 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 67
    simpa using h
  have hprev := st304_p67
  have hstep := st304_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p69 : ((11461775699891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT304 (i+1))
      = (∑ i ∈ Finset.range 68, stT304 (i+1)) + stT304 69 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 68
    simpa using h
  have hprev := st304_p68
  have hstep := st304_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p70 : ((21757558896351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT304 (i+1))
      = (∑ i ∈ Finset.range 69, stT304 (i+1)) + stT304 70 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 69
    simpa using h
  have hprev := st304_p69
  have hstep := st304_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p71 : ((5612320627417/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT304 (i+1))
      = (∑ i ∈ Finset.range 70, stT304 (i+1)) + stT304 71 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 70
    simpa using h
  have hprev := st304_p70
  have hstep := st304_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p72 : ((11500798201931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT304 (i+1))
      = (∑ i ∈ Finset.range 71, stT304 (i+1)) + stT304 72 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 71
    simpa using h
  have hprev := st304_p71
  have hstep := st304_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p73 : ((10915821017477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT304 (i+1))
      = (∑ i ∈ Finset.range 72, stT304 (i+1)) + stT304 73 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 72
    simpa using h
  have hprev := st304_p72
  have hstep := st304_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p74 : ((2249521356013/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT304 (i+1))
      = (∑ i ∈ Finset.range 73, stT304 (i+1)) + stT304 74 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 73
    simpa using h
  have hprev := st304_p73
  have hstep := st304_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p75 : ((2287079590093/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT304 (i+1))
      = (∑ i ∈ Finset.range 74, stT304 (i+1)) + stT304 75 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 74
    simpa using h
  have hprev := st304_p74
  have hstep := st304_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p76 : ((21794908064907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT304 (i+1))
      = (∑ i ∈ Finset.range 75, stT304 (i+1)) + stT304 76 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 75
    simpa using h
  have hprev := st304_p75
  have hstep := st304_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p77 : ((22806733714677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT304 (i+1))
      = (∑ i ∈ Finset.range 76, stT304 (i+1)) + stT304 77 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 76
    simpa using h
  have hprev := st304_p76
  have hstep := st304_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p78 : ((22459180982577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT304 (i+1))
      = (∑ i ∈ Finset.range 77, stT304 (i+1)) + stT304 78 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 77
    simpa using h
  have hprev := st304_p77
  have hstep := st304_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p79 : ((22001143031633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT304 (i+1))
      = (∑ i ∈ Finset.range 78, stT304 (i+1)) + stT304 79 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 78
    simpa using h
  have hprev := st304_p78
  have hstep := st304_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p80 : ((718694146477/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT304 (i+1))
      = (∑ i ∈ Finset.range 79, stT304 (i+1)) + stT304 80 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 79
    simpa using h
  have hprev := st304_p79
  have hstep := st304_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p81 : ((85555428079/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT304 (i+1))
      = (∑ i ∈ Finset.range 80, stT304 (i+1)) + stT304 81 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 80
    simpa using h
  have hprev := st304_p80
  have hstep := st304_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p82 : ((22706991169609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT304 (i+1))
      = (∑ i ∈ Finset.range 81, stT304 (i+1)) + stT304 82 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 81
    simpa using h
  have hprev := st304_p81
  have hstep := st304_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p83 : ((4482108388691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT304 (i+1))
      = (∑ i ∈ Finset.range 82, stT304 (i+1)) + stT304 83 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 82
    simpa using h
  have hprev := st304_p82
  have hstep := st304_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p84 : ((4433233230359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT304 (i+1))
      = (∑ i ∈ Finset.range 83, stT304 (i+1)) + stT304 84 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 83
    simpa using h
  have hprev := st304_p83
  have hstep := st304_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p85 : ((22849653101683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT304 (i+1))
      = (∑ i ∈ Finset.range 84, stT304 (i+1)) + stT304 85 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 84
    simpa using h
  have hprev := st304_p84
  have hstep := st304_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p86 : ((4378113106719/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT304 (i+1))
      = (∑ i ∈ Finset.range 85, stT304 (i+1)) + stT304 86 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 85
    simpa using h
  have hprev := st304_p85
  have hstep := st304_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p87 : ((22956996412107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT304 (i+1))
      = (∑ i ∈ Finset.range 86, stT304 (i+1)) + stT304 87 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 86
    simpa using h
  have hprev := st304_p86
  have hstep := st304_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p88 : ((4383826343939/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT304 (i+1))
      = (∑ i ∈ Finset.range 87, stT304 (i+1)) + stT304 88 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 87
    simpa using h
  have hprev := st304_p87
  have hstep := st304_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p89 : ((11418353231389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT304 (i+1))
      = (∑ i ∈ Finset.range 88, stT304 (i+1)) + stT304 89 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 88
    simpa using h
  have hprev := st304_p88
  have hstep := st304_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p90 : ((22086684508209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT304 (i+1))
      = (∑ i ∈ Finset.range 89, stT304 (i+1)) + stT304 90 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 89
    simpa using h
  have hprev := st304_p89
  have hstep := st304_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p91 : ((22655769588141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT304 (i+1))
      = (∑ i ∈ Finset.range 90, stT304 (i+1)) + stT304 91 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 90
    simpa using h
  have hprev := st304_p90
  have hstep := st304_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p92 : ((22256270210563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT304 (i+1))
      = (∑ i ∈ Finset.range 91, stT304 (i+1)) + stT304 92 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 91
    simpa using h
  have hprev := st304_p91
  have hstep := st304_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p93 : ((11255458689243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT304 (i+1))
      = (∑ i ∈ Finset.range 92, stT304 (i+1)) + stT304 93 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 92
    simpa using h
  have hprev := st304_p92
  have hstep := st304_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p94 : ((11184242094409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT304 (i+1))
      = (∑ i ∈ Finset.range 93, stT304 (i+1)) + stT304 94 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 93
    simpa using h
  have hprev := st304_p93
  have hstep := st304_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p95 : ((11216523466201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT304 (i+1))
      = (∑ i ∈ Finset.range 94, stT304 (i+1)) + stT304 95 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 94
    simpa using h
  have hprev := st304_p94
  have hstep := st304_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p96 : ((22411118890217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT304 (i+1))
      = (∑ i ∈ Finset.range 95, stT304 (i+1)) + stT304 96 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 95
    simpa using h
  have hprev := st304_p95
  have hstep := st304_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p97 : ((4484780013133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT304 (i+1))
      = (∑ i ∈ Finset.range 96, stT304 (i+1)) + stT304 97 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 96
    simpa using h
  have hprev := st304_p96
  have hstep := st304_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p98 : ((5596783381731/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT304 (i+1))
      = (∑ i ∈ Finset.range 97, stT304 (i+1)) + stT304 98 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 97
    simpa using h
  have hprev := st304_p97
  have hstep := st304_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p99 : ((2809866700813/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT304 (i+1))
      = (∑ i ∈ Finset.range 98, stT304 (i+1)) + stT304 99 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 98
    simpa using h
  have hprev := st304_p98
  have hstep := st304_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p100 : ((2787737575813/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT304 (i+1))
      = (∑ i ∈ Finset.range 99, stT304 (i+1)) + stT304 100 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 99
    simpa using h
  have hprev := st304_p99
  have hstep := st304_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p101 : ((705958135747/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT304 (i+1))
      = (∑ i ∈ Finset.range 100, stT304 (i+1)) + stT304 101 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 100
    simpa using h
  have hprev := st304_p100
  have hstep := st304_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p102 : ((5541972975401/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT304 (i+1))
      = (∑ i ∈ Finset.range 101, stT304 (i+1)) + stT304 102 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 101
    simpa using h
  have hprev := st304_p101
  have hstep := st304_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p103 : ((22737712588949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT304 (i+1))
      = (∑ i ∈ Finset.range 102, stT304 (i+1)) + stT304 103 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 102
    simpa using h
  have hprev := st304_p102
  have hstep := st304_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p104 : ((22019899840681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT304 (i+1))
      = (∑ i ∈ Finset.range 103, stT304 (i+1)) + stT304 104 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 103
    simpa using h
  have hprev := st304_p103
  have hstep := st304_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p105 : ((22868069169181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT304 (i+1))
      = (∑ i ∈ Finset.range 104, stT304 (i+1)) + stT304 105 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 104
    simpa using h
  have hprev := st304_p104
  have hstep := st304_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p106 : ((21928615125259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT304 (i+1))
      = (∑ i ∈ Finset.range 105, stT304 (i+1)) + stT304 106 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 105
    simpa using h
  have hprev := st304_p105
  have hstep := st304_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p107 : ((4578964077439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT304 (i+1))
      = (∑ i ∈ Finset.range 106, stT304 (i+1)) + stT304 107 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 106
    simpa using h
  have hprev := st304_p106
  have hstep := st304_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p108 : ((21988732129061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT304 (i+1))
      = (∑ i ∈ Finset.range 107, stT304 (i+1)) + stT304 108 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 107
    simpa using h
  have hprev := st304_p107
  have hstep := st304_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p109 : ((909254879283/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT304 (i+1))
      = (∑ i ∈ Finset.range 108, stT304 (i+1)) + stT304 109 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 108
    simpa using h
  have hprev := st304_p108
  have hstep := st304_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p110 : ((11127892795569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT304 (i+1))
      = (∑ i ∈ Finset.range 109, stT304 (i+1)) + stT304 110 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 109
    simpa using h
  have hprev := st304_p109
  have hstep := st304_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p111 : ((5595077323649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT304 (i+1))
      = (∑ i ∈ Finset.range 110, stT304 (i+1)) + stT304 111 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 110
    simpa using h
  have hprev := st304_p110
  have hstep := st304_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p112 : ((22644490346709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT304 (i+1))
      = (∑ i ∈ Finset.range 111, stT304 (i+1)) + stT304 112 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 111
    simpa using h
  have hprev := st304_p111
  have hstep := st304_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p113 : ((11011060781241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT304 (i+1))
      = (∑ i ∈ Finset.range 112, stT304 (i+1)) + stT304 113 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 112
    simpa using h
  have hprev := st304_p112
  have hstep := st304_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p114 : ((11445057411711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT304 (i+1))
      = (∑ i ∈ Finset.range 113, stT304 (i+1)) + stT304 114 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 113
    simpa using h
  have hprev := st304_p113
  have hstep := st304_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p115 : ((21962336691267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT304 (i+1))
      = (∑ i ∈ Finset.range 114, stT304 (i+1)) + stT304 115 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 114
    simpa using h
  have hprev := st304_p114
  have hstep := st304_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p116 : ((22722583981779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT304 (i+1))
      = (∑ i ∈ Finset.range 115, stT304 (i+1)) + stT304 116 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 115
    simpa using h
  have hprev := st304_p115
  have hstep := st304_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p117 : ((22339284018177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT304 (i+1))
      = (∑ i ∈ Finset.range 116, stT304 (i+1)) + stT304 117 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 116
    simpa using h
  have hprev := st304_p116
  have hstep := st304_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p118 : ((1388915275247/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT304 (i+1))
      = (∑ i ∈ Finset.range 117, stT304 (i+1)) + stT304 118 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 117
    simpa using h
  have hprev := st304_p117
  have hstep := st304_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p119 : ((11407652622409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT304 (i+1))
      = (∑ i ∈ Finset.range 118, stT304 (i+1)) + stT304 119 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 118
    simpa using h
  have hprev := st304_p118
  have hstep := st304_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p120 : ((10967710875637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT304 (i+1))
      = (∑ i ∈ Finset.range 119, stT304 (i+1)) + stT304 120 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 119
    simpa using h
  have hprev := st304_p119
  have hstep := st304_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p121 : ((356089062311/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT304 (i+1))
      = (∑ i ∈ Finset.range 120, stT304 (i+1)) + stT304 121 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 120
    simpa using h
  have hprev := st304_p120
  have hstep := st304_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p122 : ((5572881687101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT304 (i+1))
      = (∑ i ∈ Finset.range 121, stT304 (i+1)) + stT304 122 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 121
    simpa using h
  have hprev := st304_p121
  have hstep := st304_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p123 : ((5555428060911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT304 (i+1))
      = (∑ i ∈ Finset.range 122, stT304 (i+1)) + stT304 123 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 122
    simpa using h
  have hprev := st304_p122
  have hstep := st304_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p124 : ((2283863006289/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT304 (i+1))
      = (∑ i ∈ Finset.range 123, stT304 (i+1)) + stT304 124 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 123
    simpa using h
  have hprev := st304_p123
  have hstep := st304_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p125 : ((10974935920991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT304 (i+1))
      = (∑ i ∈ Finset.range 124, stT304 (i+1)) + stT304 125 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 124
    simpa using h
  have hprev := st304_p124
  have hstep := st304_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p126 : ((11341080818381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT304 (i+1))
      = (∑ i ∈ Finset.range 125, stT304 (i+1)) + stT304 126 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 125
    simpa using h
  have hprev := st304_p125
  have hstep := st304_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p127 : ((175645953191/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT304 (i+1))
      = (∑ i ∈ Finset.range 126, stT304 (i+1)) + stT304 127 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 126
    simpa using h
  have hprev := st304_p126
  have hstep := st304_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p128 : ((5508821390071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT304 (i+1))
      = (∑ i ∈ Finset.range 127, stT304 (i+1)) + stT304 128 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 127
    simpa using h
  have hprev := st304_p127
  have hstep := st304_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p129 : ((11442529020467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT304 (i+1))
      = (∑ i ∈ Finset.range 128, stT304 (i+1)) + stT304 129 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 128
    simpa using h
  have hprev := st304_p128
  have hstep := st304_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p130 : ((4425624032903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT304 (i+1))
      = (∑ i ∈ Finset.range 129, stT304 (i+1)) + stT304 130 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 129
    simpa using h
  have hprev := st304_p129
  have hstep := st304_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p131 : ((22326358359891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT304 (i+1))
      = (∑ i ∈ Finset.range 130, stT304 (i+1)) + stT304 131 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 130
    simpa using h
  have hprev := st304_p130
  have hstep := st304_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p132 : ((22818306879819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT304 (i+1))
      = (∑ i ∈ Finset.range 131, stT304 (i+1)) + stT304 132 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 131
    simpa using h
  have hprev := st304_p131
  have hstep := st304_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p133 : ((21957634304459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT304 (i+1))
      = (∑ i ∈ Finset.range 132, stT304 (i+1)) + stT304 133 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 132
    simpa using h
  have hprev := st304_p132
  have hstep := st304_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p134 : ((22594503710099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT304 (i+1))
      = (∑ i ∈ Finset.range 133, stT304 (i+1)) + stT304 134 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 133
    simpa using h
  have hprev := st304_p133
  have hstep := st304_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p135 : ((22639374323469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT304 (i+1))
      = (∑ i ∈ Finset.range 134, stT304 (i+1)) + stT304 135 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 134
    simpa using h
  have hprev := st304_p134
  have hstep := st304_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p136 : ((21941640844299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT304 (i+1))
      = (∑ i ∈ Finset.range 135, stT304 (i+1)) + stT304 136 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 135
    simpa using h
  have hprev := st304_p135
  have hstep := st304_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p137 : ((2275926305637/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT304 (i+1))
      = (∑ i ∈ Finset.range 136, stT304 (i+1)) + stT304 137 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 136
    simpa using h
  have hprev := st304_p136
  have hstep := st304_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p138 : ((22470371117023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT304 (i+1))
      = (∑ i ∈ Finset.range 137, stT304 (i+1)) + stT304 138 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 137
    simpa using h
  have hprev := st304_p137
  have hstep := st304_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p139 : ((21991027281941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT304 (i+1))
      = (∑ i ∈ Finset.range 138, stT304 (i+1)) + stT304 139 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 138
    simpa using h
  have hprev := st304_p138
  have hstep := st304_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p140 : ((22836069721613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT304 (i+1))
      = (∑ i ∈ Finset.range 139, stT304 (i+1)) + stT304 140 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 139
    simpa using h
  have hprev := st304_p139
  have hstep := st304_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p141 : ((22359885821189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT304 (i+1))
      = (∑ i ∈ Finset.range 140, stT304 (i+1)) + stT304 141 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 140
    simpa using h
  have hprev := st304_p140
  have hstep := st304_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p142 : ((22038953253019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT304 (i+1))
      = (∑ i ∈ Finset.range 141, stT304 (i+1)) + stT304 142 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 141
    simpa using h
  have hprev := st304_p141
  have hstep := st304_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p143 : ((22863023750709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT304 (i+1))
      = (∑ i ∈ Finset.range 142, stT304 (i+1)) + stT304 143 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 142
    simpa using h
  have hprev := st304_p142
  have hstep := st304_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p144 : ((22314775812111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT304 (i+1))
      = (∑ i ∈ Finset.range 143, stT304 (i+1)) + stT304 144 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 143
    simpa using h
  have hprev := st304_p143
  have hstep := st304_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p145 : ((22053561174591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT304 (i+1))
      = (∑ i ∈ Finset.range 144, stT304 (i+1)) + stT304 145 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 144
    simpa using h
  have hprev := st304_p144
  have hstep := st304_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p146 : ((5716200071429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT304 (i+1))
      = (∑ i ∈ Finset.range 145, stT304 (i+1)) + stT304 146 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 145
    simpa using h
  have hprev := st304_p145
  have hstep := st304_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p147 : ((139571893181/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT304 (i+1))
      = (∑ i ∈ Finset.range 146, stT304 (i+1)) + stT304 147 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 146
    simpa using h
  have hprev := st304_p146
  have hstep := st304_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p148 : ((35245384203/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT304 (i+1))
      = (∑ i ∈ Finset.range 147, stT304 (i+1)) + stT304 148 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 147
    simpa using h
  have hprev := st304_p147
  have hstep := st304_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p149 : ((456870409053/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT304 (i+1))
      = (∑ i ∈ Finset.range 148, stT304 (i+1)) + stT304 149 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 148
    simpa using h
  have hprev := st304_p148
  have hstep := st304_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p150 : ((5602188440771/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT304 (i+1))
      = (∑ i ∈ Finset.range 149, stT304 (i+1)) + stT304 150 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 149
    simpa using h
  have hprev := st304_p149
  have hstep := st304_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p151 : ((10988121406471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT304 (i+1))
      = (∑ i ∈ Finset.range 150, stT304 (i+1)) + stT304 151 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 150
    simpa using h
  have hprev := st304_p150
  have hstep := st304_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p152 : ((22780999656239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT304 (i+1))
      = (∑ i ∈ Finset.range 151, stT304 (i+1)) + stT304 152 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 151
    simpa using h
  have hprev := st304_p151
  have hstep := st304_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p153 : ((11271681086483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT304 (i+1))
      = (∑ i ∈ Finset.range 152, stT304 (i+1)) + stT304 153 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 152
    simpa using h
  have hprev := st304_p152
  have hstep := st304_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p154 : ((21931082546929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT304 (i+1))
      = (∑ i ∈ Finset.range 153, stT304 (i+1)) + stT304 154 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 153
    simpa using h
  have hprev := st304_p153
  have hstep := st304_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p155 : ((22648562737993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT304 (i+1))
      = (∑ i ∈ Finset.range 154, stT304 (i+1)) + stT304 155 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 154
    simpa using h
  have hprev := st304_p154
  have hstep := st304_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p156 : ((22713934193353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT304 (i+1))
      = (∑ i ∈ Finset.range 155, stT304 (i+1)) + stT304 156 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 155
    simpa using h
  have hprev := st304_p155
  have hstep := st304_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p157 : ((171477040469/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT304 (i+1))
      = (∑ i ∈ Finset.range 156, stT304 (i+1)) + stT304 157 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 156
    simpa using h
  have hprev := st304_p156
  have hstep := st304_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p158 : ((5607487482177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT304 (i+1))
      = (∑ i ∈ Finset.range 157, stT304 (i+1)) + stT304 158 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 157
    simpa using h
  have hprev := st304_p157
  have hstep := st304_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p159 : ((5715185394079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT304 (i+1))
      = (∑ i ∈ Finset.range 158, stT304 (i+1)) + stT304 159 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 158
    simpa using h
  have hprev := st304_p158
  have hstep := st304_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p160 : ((11046302000033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT304 (i+1))
      = (∑ i ∈ Finset.range 159, stT304 (i+1)) + stT304 160 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 159
    simpa using h
  have hprev := st304_p159
  have hstep := st304_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p161 : ((11079349816663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT304 (i+1))
      = (∑ i ∈ Finset.range 160, stT304 (i+1)) + stT304 161 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 160
    simpa using h
  have hprev := st304_p160
  have hstep := st304_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p162 : ((228836025351/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT304 (i+1))
      = (∑ i ∈ Finset.range 161, stT304 (i+1)) + stT304 162 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 161
    simpa using h
  have hprev := st304_p161
  have hstep := st304_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p163 : ((11190779432487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT304 (i+1))
      = (∑ i ∈ Finset.range 162, stT304 (i+1)) + stT304 163 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 162
    simpa using h
  have hprev := st304_p162
  have hstep := st304_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p164 : ((21949217468351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT304 (i+1))
      = (∑ i ∈ Finset.range 163, stT304 (i+1)) + stT304 164 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 163
    simpa using h
  have hprev := st304_p163
  have hstep := st304_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p165 : ((22690666748531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT304 (i+1))
      = (∑ i ∈ Finset.range 164, stT304 (i+1)) + stT304 165 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 164
    simpa using h
  have hprev := st304_p164
  have hstep := st304_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p166 : ((22724232131431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT304 (i+1))
      = (∑ i ∈ Finset.range 165, stT304 (i+1)) + stT304 166 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 165
    simpa using h
  have hprev := st304_p165
  have hstep := st304_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p167 : ((21967606369831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT304 (i+1))
      = (∑ i ∈ Finset.range 166, stT304 (i+1)) + stT304 167 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 166
    simpa using h
  have hprev := st304_p166
  have hstep := st304_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p168 : ((22307145160819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT304 (i+1))
      = (∑ i ∈ Finset.range 167, stT304 (i+1)) + stT304 168 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 167
    simpa using h
  have hprev := st304_p167
  have hstep := st304_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p169 : ((22900727644159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT304 (i+1))
      = (∑ i ∈ Finset.range 168, stT304 (i+1)) + stT304 169 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 168
    simpa using h
  have hprev := st304_p168
  have hstep := st304_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p170 : ((22294231663249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT304 (i+1))
      = (∑ i ∈ Finset.range 169, stT304 (i+1)) + stT304 170 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 169
    simpa using h
  have hprev := st304_p169
  have hstep := st304_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p171 : ((21963806857329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT304 (i+1))
      = (∑ i ∈ Finset.range 170, stT304 (i+1)) + stT304 171 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 170
    simpa using h
  have hprev := st304_p170
  have hstep := st304_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p172 : ((22703471371833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT304 (i+1))
      = (∑ i ∈ Finset.range 171, stT304 (i+1)) + stT304 172 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 171
    simpa using h
  have hprev := st304_p171
  have hstep := st304_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p173 : ((11371977893899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT304 (i+1))
      = (∑ i ∈ Finset.range 172, stT304 (i+1)) + stT304 173 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 172
    simpa using h
  have hprev := st304_p172
  have hstep := st304_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p174 : ((10995991113859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT304 (i+1))
      = (∑ i ∈ Finset.range 173, stT304 (i+1)) + stT304 174 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 173
    simpa using h
  have hprev := st304_p173
  have hstep := st304_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p175 : ((11107407341779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT304 (i+1))
      = (∑ i ∈ Finset.range 174, stT304 (i+1)) + stT304 175 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 174
    simpa using h
  have hprev := st304_p174
  have hstep := st304_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p176 : ((11444960436849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT304 (i+1))
      = (∑ i ∈ Finset.range 175, stT304 (i+1)) + stT304 176 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 175
    simpa using h
  have hprev := st304_p175
  have hstep := st304_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p177 : ((350903367963/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT304 (i+1))
      = (∑ i ∈ Finset.range 176, stT304 (i+1)) + stT304 177 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 176
    simpa using h
  have hprev := st304_p176
  have hstep := st304_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p178 : ((1095573671499/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT304 (i+1))
      = (∑ i ∈ Finset.range 177, stT304 (i+1)) + stT304 178 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 177
    simpa using h
  have hprev := st304_p177
  have hstep := st304_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p179 : ((4498113177447/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT304 (i+1))
      = (∑ i ∈ Finset.range 178, stT304 (i+1)) + stT304 179 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 178
    simpa using h
  have hprev := st304_p178
  have hstep := st304_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p180 : ((572183909171/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT304 (i+1))
      = (∑ i ∈ Finset.range 179, stT304 (i+1)) + stT304 180 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 179
    simpa using h
  have hprev := st304_p179
  have hstep := st304_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p181 : ((4443472280653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT304 (i+1))
      = (∑ i ∈ Finset.range 180, stT304 (i+1)) + stT304 181 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 180
    simpa using h
  have hprev := st304_p180
  have hstep := st304_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p182 : ((4393466666153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT304 (i+1))
      = (∑ i ∈ Finset.range 181, stT304 (i+1)) + stT304 182 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 181
    simpa using h
  have hprev := st304_p181
  have hstep := st304_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p183 : ((2268368652913/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT304 (i+1))
      = (∑ i ∈ Finset.range 182, stT304 (i+1)) + stT304 183 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 182
    simpa using h
  have hprev := st304_p182
  have hstep := st304_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p184 : ((11401657453989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT304 (i+1))
      = (∑ i ∈ Finset.range 183, stT304 (i+1)) + stT304 184 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 183
    simpa using h
  have hprev := st304_p183
  have hstep := st304_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p185 : ((22070754769343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT304 (i+1))
      = (∑ i ∈ Finset.range 184, stT304 (i+1)) + stT304 185 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 184
    simpa using h
  have hprev := st304_p184
  have hstep := st304_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p186 : ((22057357081151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT304 (i+1))
      = (∑ i ∈ Finset.range 185, stT304 (i+1)) + stT304 186 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 185
    simpa using h
  have hprev := st304_p185
  have hstep := st304_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p187 : ((22787938760383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT304 (i+1))
      = (∑ i ∈ Finset.range 186, stT304 (i+1)) + stT304 187 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 186
    simpa using h
  have hprev := st304_p186
  have hstep := st304_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p188 : ((22721148635533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT304 (i+1))
      = (∑ i ∈ Finset.range 187, stT304 (i+1)) + stT304 188 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 187
    simpa using h
  have hprev := st304_p187
  have hstep := st304_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p189 : ((22000161058291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT304 (i+1))
      = (∑ i ∈ Finset.range 188, stT304 (i+1)) + stT304 189 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 188
    simpa using h
  have hprev := st304_p188
  have hstep := st304_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p190 : ((22120660445463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT304 (i+1))
      = (∑ i ∈ Finset.range 189, stT304 (i+1)) + stT304 190 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 189
    simpa using h
  have hprev := st304_p189
  have hstep := st304_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p191 : ((22830867139387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT304 (i+1))
      = (∑ i ∈ Finset.range 190, stT304 (i+1)) + stT304 191 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 190
    simpa using h
  have hprev := st304_p190
  have hstep := st304_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p192 : ((22681302353203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT304 (i+1))
      = (∑ i ∈ Finset.range 191, stT304 (i+1)) + stT304 192 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 191
    simpa using h
  have hprev := st304_p191
  have hstep := st304_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p193 : ((21978307733307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT304 (i+1))
      = (∑ i ∈ Finset.range 192, stT304 (i+1)) + stT304 193 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 192
    simpa using h
  have hprev := st304_p192
  have hstep := st304_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p194 : ((22133059990417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT304 (i+1))
      = (∑ i ∈ Finset.range 193, stT304 (i+1)) + stT304 194 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 193
    simpa using h
  have hprev := st304_p193
  have hstep := st304_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p195 : ((22833438101381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT304 (i+1))
      = (∑ i ∈ Finset.range 194, stT304 (i+1)) + stT304 195 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 194
    simpa using h
  have hprev := st304_p194
  have hstep := st304_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p196 : ((4539169609269/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT304 (i+1))
      = (∑ i ∈ Finset.range 195, stT304 (i+1)) + stT304 196 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 195
    simpa using h
  have hprev := st304_p195
  have hstep := st304_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p197 : ((4398715926213/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT304 (i+1))
      = (∑ i ∈ Finset.range 196, stT304 (i+1)) + stT304 197 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 196
    simpa using h
  have hprev := st304_p196
  have hstep := st304_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p198 : ((2761450364613/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT304 (i+1))
      = (∑ i ∈ Finset.range 197, stT304 (i+1)) + stT304 198 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 197
    simpa using h
  have hprev := st304_p197
  have hstep := st304_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p199 : ((22796930296451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT304 (i+1))
      = (∑ i ∈ Finset.range 198, stT304 (i+1)) + stT304 199 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 198
    simpa using h
  have hprev := st304_p198
  have hstep := st304_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p200 : ((4551997073983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT304 (i+1))
      = (∑ i ∈ Finset.range 199, stT304 (i+1)) + stT304 200 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 199
    simpa using h
  have hprev := st304_p199
  have hstep := st304_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p201 : ((22054570951353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT304 (i+1))
      = (∑ i ∈ Finset.range 200, stT304 (i+1)) + stT304 201 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 200
    simpa using h
  have hprev := st304_p200
  have hstep := st304_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p202 : ((22009129074523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT304 (i+1))
      = (∑ i ∈ Finset.range 201, stT304 (i+1)) + stT304 202 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 201
    simpa using h
  have hprev := st304_p201
  have hstep := st304_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p203 : ((22704620975011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT304 (i+1))
      = (∑ i ∈ Finset.range 202, stT304 (i+1)) + stT304 203 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 202
    simpa using h
  have hprev := st304_p202
  have hstep := st304_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p204 : ((22851202985551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT304 (i+1))
      = (∑ i ∈ Finset.range 203, stT304 (i+1)) + stT304 204 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 203
    simpa using h
  have hprev := st304_p203
  have hstep := st304_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p205 : ((11091462673557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT304 (i+1))
      = (∑ i ∈ Finset.range 204, stT304 (i+1)) + stT304 205 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 204
    simpa using h
  have hprev := st304_p204
  have hstep := st304_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p206 : ((2740009173509/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT304 (i+1))
      = (∑ i ∈ Finset.range 205, stT304 (i+1)) + stT304 206 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 205
    simpa using h
  have hprev := st304_p205
  have hstep := st304_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p207 : ((704211660757/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT304 (i+1))
      = (∑ i ∈ Finset.range 206, stT304 (i+1)) + stT304 207 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 206
    simpa using h
  have hprev := st304_p206
  have hstep := st304_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p208 : ((5730276956681/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT304 (i+1))
      = (∑ i ∈ Finset.range 207, stT304 (i+1)) + stT304 208 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 207
    simpa using h
  have hprev := st304_p207
  have hstep := st304_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p209 : ((22393709033259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT304 (i+1))
      = (∑ i ∈ Finset.range 208, stT304 (i+1)) + stT304 209 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 208
    simpa using h
  have hprev := st304_p208
  have hstep := st304_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p210 : ((21887423480577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT304 (i+1))
      = (∑ i ∈ Finset.range 209, stT304 (i+1)) + stT304 210 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 209
    simpa using h
  have hprev := st304_p209
  have hstep := st304_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p211 : ((22287698237901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT304 (i+1))
      = (∑ i ∈ Finset.range 210, stT304 (i+1)) + stT304 211 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 210
    simpa using h
  have hprev := st304_p210
  have hstep := st304_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p212 : ((4578906764127/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT304 (i+1))
      = (∑ i ∈ Finset.range 211, stT304 (i+1)) + stT304 212 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 211
    simpa using h
  have hprev := st304_p211
  have hstep := st304_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p213 : ((22661476374931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT304 (i+1))
      = (∑ i ∈ Finset.range 212, stT304 (i+1)) + stT304 213 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 212
    simpa using h
  have hprev := st304_p212
  have hstep := st304_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p214 : ((21991456822687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT304 (i+1))
      = (∑ i ∈ Finset.range 213, stT304 (i+1)) + stT304 214 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 213
    simpa using h
  have hprev := st304_p213
  have hstep := st304_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p215 : ((22023100662293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT304 (i+1))
      = (∑ i ∈ Finset.range 214, stT304 (i+1)) + stT304 215 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 214
    simpa using h
  have hprev := st304_p214
  have hstep := st304_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p216 : ((2837382544901/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT304 (i+1))
      = (∑ i ∈ Finset.range 215, stT304 (i+1)) + stT304 216 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 215
    simpa using h
  have hprev := st304_p215
  have hstep := st304_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p217 : ((2860844751229/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT304 (i+1))
      = (∑ i ∈ Finset.range 216, stT304 (i+1)) + stT304 217 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 216
    simpa using h
  have hprev := st304_p216
  have hstep := st304_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p218 : ((445556379439/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT304 (i+1))
      = (∑ i ∈ Finset.range 217, stT304 (i+1)) + stT304 218 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 217
    simpa using h
  have hprev := st304_p217
  have hstep := st304_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p219 : ((43756206103/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT304 (i+1))
      = (∑ i ∈ Finset.range 218, stT304 (i+1)) + stT304 219 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 218
    simpa using h
  have hprev := st304_p218
  have hstep := st304_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p220 : ((11169324868399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT304 (i+1))
      = (∑ i ∈ Finset.range 219, stT304 (i+1)) + stT304 220 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 219
    simpa using h
  have hprev := st304_p219
  have hstep := st304_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p221 : ((11454245856751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT304 (i+1))
      = (∑ i ∈ Finset.range 220, stT304 (i+1)) + stT304 221 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 220
    simpa using h
  have hprev := st304_p220
  have hstep := st304_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p222 : ((4534187004439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT304 (i+1))
      = (∑ i ∈ Finset.range 221, stT304 (i+1)) + stT304 222 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 221
    simpa using h
  have hprev := st304_p221
  have hstep := st304_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p223 : ((4401894700479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT304 (i+1))
      = (∑ i ∈ Finset.range 222, stT304 (i+1)) + stT304 223 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 222
    simpa using h
  have hprev := st304_p222
  have hstep := st304_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p224 : ((21973729267857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT304 (i+1))
      = (∑ i ∈ Finset.range 223, stT304 (i+1)) + stT304 224 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 223
    simpa using h
  have hprev := st304_p223
  have hstep := st304_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p225 : ((22616161292091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT304 (i+1))
      = (∑ i ∈ Finset.range 224, stT304 (i+1)) + stT304 225 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 224
    simpa using h
  have hprev := st304_p224
  have hstep := st304_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p226 : ((22930777536771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT304 (i+1))
      = (∑ i ∈ Finset.range 225, stT304 (i+1)) + stT304 226 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 225
    simpa using h
  have hprev := st304_p225
  have hstep := st304_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p227 : ((22432330768631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT304 (i+1))
      = (∑ i ∈ Finset.range 226, stT304 (i+1)) + stT304 227 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 226
    simpa using h
  have hprev := st304_p226
  have hstep := st304_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p228 : ((21891291742981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT304 (i+1))
      = (∑ i ∈ Finset.range 227, stT304 (i+1)) + stT304 228 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 227
    simpa using h
  have hprev := st304_p227
  have hstep := st304_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p229 : ((4426590973607/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT304 (i+1))
      = (∑ i ∈ Finset.range 228, stT304 (i+1)) + stT304 229 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 228
    simpa using h
  have hprev := st304_p228
  have hstep := st304_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p230 : ((911473900307/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT304 (i+1))
      = (∑ i ∈ Finset.range 229, stT304 (i+1)) + stT304 230 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 229
    simpa using h
  have hprev := st304_p229
  have hstep := st304_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p231 : ((11433949916707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT304 (i+1))
      = (∑ i ∈ Finset.range 230, stT304 (i+1)) + stT304 231 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 230
    simpa using h
  have hprev := st304_p230
  have hstep := st304_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p232 : ((4451687655983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT304 (i+1))
      = (∑ i ∈ Finset.range 231, stT304 (i+1)) + stT304 232 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 231
    simpa using h
  have hprev := st304_p231
  have hstep := st304_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p233 : ((21864774159871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT304 (i+1))
      = (∑ i ∈ Finset.range 232, stT304 (i+1)) + stT304 233 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 232
    simpa using h
  have hprev := st304_p232
  have hstep := st304_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p234 : ((22264190542671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT304 (i+1))
      = (∑ i ∈ Finset.range 233, stT304 (i+1)) + stT304 234 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 233
    simpa using h
  have hprev := st304_p233
  have hstep := st304_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p235 : ((22869186275319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT304 (i+1))
      = (∑ i ∈ Finset.range 234, stT304 (i+1)) + stT304 235 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 234
    simpa using h
  have hprev := st304_p234
  have hstep := st304_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p236 : ((22802129827089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT304 (i+1))
      = (∑ i ∈ Finset.range 235, stT304 (i+1)) + stT304 236 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 235
    simpa using h
  have hprev := st304_p235
  have hstep := st304_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p237 : ((22163258244989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT304 (i+1))
      = (∑ i ∈ Finset.range 236, stT304 (i+1)) + stT304 237 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 236
    simpa using h
  have hprev := st304_p236
  have hstep := st304_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p238 : ((21867840568397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT304 (i+1))
      = (∑ i ∈ Finset.range 237, stT304 (i+1)) + stT304 238 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 237
    simpa using h
  have hprev := st304_p237
  have hstep := st304_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p239 : ((22332488808731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT304 (i+1))
      = (∑ i ∈ Finset.range 238, stT304 (i+1)) + stT304 239 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 238
    simpa using h
  have hprev := st304_p238
  have hstep := st304_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p240 : ((11449440398439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT304 (i+1))
      = (∑ i ∈ Finset.range 239, stT304 (i+1)) + stT304 240 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 239
    simpa using h
  have hprev := st304_p239
  have hstep := st304_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p241 : ((22775073177321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT304 (i+1))
      = (∑ i ∈ Finset.range 240, stT304 (i+1)) + stT304 241 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 240
    simpa using h
  have hprev := st304_p240
  have hstep := st304_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p242 : ((22136706811521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT304 (i+1))
      = (∑ i ∈ Finset.range 241, stT304 (i+1)) + stT304 242 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 241
    simpa using h
  have hprev := st304_p241
  have hstep := st304_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p243 : ((2186579388271/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT304 (i+1))
      = (∑ i ∈ Finset.range 242, stT304 (i+1)) + stT304 243 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 242
    simpa using h
  have hprev := st304_p242
  have hstep := st304_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p244 : ((11165273170319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT304 (i+1))
      = (∑ i ∈ Finset.range 243, stT304 (i+1)) + stT304 244 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 243
    simpa using h
  have hprev := st304_p243
  have hstep := st304_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p245 : ((11447820234013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT304 (i+1))
      = (∑ i ∈ Finset.range 244, stT304 (i+1)) + stT304 245 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 244
    simpa using h
  have hprev := st304_p244
  have hstep := st304_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p246 : ((4559727518103/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT304 (i+1))
      = (∑ i ∈ Finset.range 245, stT304 (i+1)) + stT304 246 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 245
    simpa using h
  have hprev := st304_p245
  have hstep := st304_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p247 : ((4434626760711/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT304 (i+1))
      = (∑ i ∈ Finset.range 246, stT304 (i+1)) + stT304 247 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 246
    simpa using h
  have hprev := st304_p246
  have hstep := st304_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p248 : ((21853476840159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT304 (i+1))
      = (∑ i ∈ Finset.range 247, stT304 (i+1)) + stT304 248 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 247
    simpa using h
  have hprev := st304_p247
  have hstep := st304_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p249 : ((22259687586919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT304 (i+1))
      = (∑ i ∈ Finset.range 248, stT304 (i+1)) + stT304 249 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 248
    simpa using h
  have hprev := st304_p248
  have hstep := st304_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_p250 : ((22855114876489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT304 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT304 (i+1))
      = (∑ i ∈ Finset.range 249, stT304 (i+1)) + stT304 250 := by
    have h := Finset.sum_range_succ (fun i => stT304 (i+1)) 249
    simpa using h
  have hprev := st304_p249
  have hstep := st304_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st304_s250 :
    |Real.sin (((304 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((142517/250000 : ℚ) : ℝ))
      - ((336863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 858959/10000000) (δ := 3077/200000000) (ψ := 142517/250000) 304 267
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 304`** (evaluated boundary). -/
theorem station_304_sign : hardyG ((((304:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 304 250 (by norm_num) (by norm_num)
    ((142517/250000 : ℚ) : ℝ)
  have hchain := st304_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT304 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((304 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((142517/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st304_c250
  have hsinb := abs_le.mp st304_s250
  have hbdy_lo : ((-478562616059/27181250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((304 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((142517/250000 : ℚ) : ℝ))) / 2
          - ((((304:ℕ)):ℝ))
            * Real.sin (((304 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((142517/250000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((304:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((304:ℝ) * Real.log (250:ℝ) - ((142517/250000 : ℚ) : ℝ))) / 2
        - ((304:ℝ)) * Real.sin ((304:ℝ) * Real.log (250:ℝ) - ((142517/250000 : ℚ) : ℝ))
        ≥ ((-102907579/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((304:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-102907579/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-102907579/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-102907579/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((304:ℕ)):ℝ))+1) * (((((304:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((125687427481/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((22855114876489/10000000000000 : ℚ) : ℝ) + ((-478562616059/27181250000000 : ℚ) : ℝ)
      - ((125687427481/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((142517/250000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((304:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((142517/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((304:ℕ)):ℝ)))).re
      - Real.sin ((142517/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((304:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((304:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((304:ℕ)):ℝ))
      = (((((304:ℕ)):ℝ)) * (Real.log ((((304:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((304:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_304
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
  have hθwin : |(((142517/250000 : ℚ) : ℝ) + ((70:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((304:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((304:ℕ)):ℝ)))
    (φ := ((142517/250000 : ℚ) : ℝ) + ((70:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((142517/250000 : ℚ) : ℝ) + ((70:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((142517/250000 : ℚ)) : ℝ) - Real.pi) + ((70:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((142517/250000 : ℚ)) : ℝ) - Real.pi) 70).1,
    (cos_sin_shift ((((142517/250000 : ℚ)) : ℝ) - Real.pi) 70).2]
  exact cos_sin_flip ((142517/250000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_304_sign
end AxiomAudit
