import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 191` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT191 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((191 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((859139/1000000 : ℚ) : ℝ))

theorem st191_c1 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((65309/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268481/1250000) (δ := 201/1000000000) (ψ := 859139/1000000) 191 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t1 : ((8163/12500 : ℚ) : ℝ) ≤ stT191 1 := by
  have hc : ((8163/12500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8163/12500 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((8163/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c2 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((915147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8104/78125) (δ := 597/62500000) (ψ := 859139/1000000) 191 21
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t2 : ((6470712198499/10000000000000 : ℚ) : ℝ) ≤ stT191 2 := by
  have hc : ((915097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6470712198499/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((915097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c3 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-59853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2038357/5000000) (δ := 1913/200000000) (ψ := 859139/1000000) 191 33
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t3 : ((-345850150209/10000000000000 : ℚ) : ℝ) ≤ stT191 3 := by
  have hc : ((-59903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345850150209/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-59903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c4 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((999571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73247/10000000) (δ := 97/10000000) (ψ := 859139/1000000) 191 42
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t4 : ((999521/2000000 : ℚ) : ℝ) ≤ stT191 4 := by
  have hc : ((999521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999521/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((999521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c5 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((235979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3331427/10000000) (δ := 39/4000000) (ψ := 859139/1000000) 191 49
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t5 : ((211021267683/2000000000000 : ℚ) : ℝ) ≤ stT191 5 := by
  have hc : ((235929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211021267683/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((235929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c6 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-483031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5187273/10000000) (δ := 4857/500000000) (ψ := 859139/1000000) 191 54
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t6 : ((-1972169970123/10000000000000 : ℚ) : ℝ) ≤ stT191 6 := by
  have hc : ((-483081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1972169970123/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-483081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c7 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((497413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15901/625000) (δ := 4839/500000000) (ψ := 859139/1000000) 191 59
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t7 : ((117496848117/312500000000 : ℚ) : ℝ) ≤ stT191 7 := by
  have hc : ((124347/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117496848117/312500000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((124347/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c8 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((889967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1183807/10000000) (δ := 4827/500000000) (ψ := 859139/1000000) 191 63
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t8 : ((3146330920761/10000000000000 : ℚ) : ℝ) ≤ stT191 8 := by
  have hc : ((889917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3146330920761/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((889917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c9 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-557913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -675833/1250000) (δ := 481/50000000) (ψ := 859139/1000000) 191 67
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t9 : ((-929938519321/5000000000000 : ℚ) : ℝ) ≤ stT191 9 := by
  have hc : ((-557963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-929938519321/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-557963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c10 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((630681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -444183/2000000) (δ := 9599/1000000000) (ψ := 859139/1000000) 191 70
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t10 : ((1994229906787/10000000000000 : ℚ) : ℝ) ≤ stT191 10 := by
  have hc : ((630631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1994229906787/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((630631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c11 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((18557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479273/1250000) (δ := 4813/500000000) (ψ := 859139/1000000) 191 73
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t11 : ((13969018529/1250000000000 : ℚ) : ℝ) ≤ stT191 11 := by
  have hc : ((4633/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13969018529/1250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((4633/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c12 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-812447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6297833/10000000) (δ := 241/25000000) (ψ := 859139/1000000) 191 75
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t12 : ((-73296166867/312500000000 : ℚ) : ℝ) ≤ stT191 12 := by
  have hc : ((-812497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73296166867/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-812497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c13 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((63033/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -651417/2500000) (δ := 9641/1000000000) (ψ := 859139/1000000) 191 78
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t13 : ((1398437529/10000000000 : ℚ) : ℝ) ≤ stT191 13 := by
  have hc : ((252107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1398437529/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((252107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c14 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((854613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85311/625000) (δ := 2419/250000000) (ψ := 859139/1000000) 191 80
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t14 : ((570978832139/2500000000000 : ℚ) : ℝ) ≤ stT191 14 := by
  have hc : ((854563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((570978832139/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((854563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c15 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((401847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2893159/10000000) (δ := 959/100000000) (ψ := 859139/1000000) 191 82
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t15 : ((259358758109/2500000000000 : ℚ) : ℝ) ≤ stT191 15 := by
  have hc : ((401797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259358758109/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((401797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c16 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((151903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1147183/5000000) (δ := 4799/500000000) (ψ := 859139/1000000) 191 84
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t16 : ((303781/2000000 : ℚ) : ℝ) ≤ stT191 16 := by
  have hc : ((303781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303781/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((303781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c17 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((498799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86657/5000000) (δ := 599/62500000) (ψ := 859139/1000000) 191 86
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t17 : ((151213064193/625000000000 : ℚ) : ℝ) ≤ stT191 17 := by
  have hc : ((249387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151213064193/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((249387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c18 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-147109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -537013/1250000) (δ := 9733/1000000000) (ψ := 859139/1000000) 191 88
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t18 : ((-346857147657/10000000000000 : ℚ) : ℝ) ≤ stT191 18 := by
  have hc : ((-147159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346857147657/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-147159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c19 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-34243/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290651/500000) (δ := 9663/1000000000) (ψ := 859139/1000000) 191 89
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t19 : ((-78564587789/500000000000 : ℚ) : ℝ) ≤ stT191 19 := by
  have hc : ((-68491/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78564587789/500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-68491/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c20 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((902979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277589/2500000) (δ := 2437/250000000) (ψ := 859139/1000000) 191 91
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t20 : ((2019009740243/10000000000000 : ℚ) : ℝ) ≤ stT191 20 := by
  have hc : ((902929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2019009740243/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((902929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c21 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-852529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3239501/5000000) (δ := 4831/500000000) (ψ := 859139/1000000) 191 92
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t21 : ((-1860479989641/10000000000000 : ℚ) : ℝ) ≤ stT191 21 := by
  have hc : ((-852579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1860479989641/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-852579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c22 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((462973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21789/80000) (δ := 9627/1000000000) (ψ := 859139/1000000) 191 94
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t22 : ((986955076461/10000000000000 : ℚ) : ℝ) ≤ stT191 22 := by
  have hc : ((462923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((986955076461/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((462923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c23 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((437789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1397073/5000000) (δ := 9719/1000000000) (ψ := 859139/1000000) 191 95
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t23 : ((114093606177/1250000000000 : ℚ) : ℝ) ≤ stT191 23 := by
  have hc : ((437739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114093606177/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((437739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c24 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-492079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926049/1250000) (δ := 2403/250000000) (ψ := 859139/1000000) 191 96
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t24 : ((-62781459573/312500000000 : ℚ) : ℝ) ≤ stT191 24 := by
  have hc : ((-61513/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62781459573/312500000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-61513/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c25 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-58263/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4515029/10000000) (δ := 1941/200000000) (ψ := 859139/1000000) 191 98
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t25 : ((-233102116551/5000000000000 : ℚ) : ℝ) ≤ stT191 25 := by
  have hc : ((-116551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233102116551/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-116551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c26 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((826439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373777/2500000) (δ := 607/62500000) (ψ := 859139/1000000) 191 99
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t26 : ((1620681877629/10000000000000 : ℚ) : ℝ) ≤ stT191 26 := by
  have hc : ((826389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1620681877629/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((826389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c27 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((236739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 408961/5000000) (δ := 9719/1000000000) (ψ := 859139/1000000) 191 100
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t27 : ((1822320597/10000000000 : ℚ) : ℝ) ≤ stT191 27 := by
  have hc : ((473453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1822320597/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((473453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c28 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((548511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 495107/2000000) (δ := 1197/125000000) (ψ := 859139/1000000) 191 101
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t28 : ((518246831971/5000000000000 : ℚ) : ℝ) ≤ stT191 28 := by
  have hc : ((548461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518246831971/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((548461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c29 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((16063/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 880917/2500000) (δ := 4867/500000000) (ψ := 859139/1000000) 191 102
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t29 : ((14909475637/500000000000 : ℚ) : ℝ) ≤ stT191 29 := by
  have hc : ((8029/50000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14909475637/500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((8029/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c30 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-30667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4003671/10000000) (δ := 9741/1000000000) (ψ := 859139/1000000) 191 103
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t30 : ((-28040658507/5000000000000 : ℚ) : ℝ) ≤ stT191 30 := by
  have hc : ((-30717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28040658507/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-30717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c31 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-10357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 790577/2000000) (δ := 2437/250000000) (ψ := 859139/1000000) 191 104
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t31 : ((-9345766989/5000000000000 : ℚ) : ℝ) ≤ stT191 31 := by
  have hc : ((-10407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9345766989/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-10407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c32 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((12957/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136197/400000) (δ := 2437/250000000) (ψ := 859139/1000000) 191 105
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t32 : ((91597679173/2500000000000 : ℚ) : ℝ) ≤ stT191 32 := by
  have hc : ((103631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91597679173/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((103631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c33 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((576661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2390401/10000000) (δ := 241/25000000) (ψ := 859139/1000000) 191 106
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t33 : ((125468823767/1250000000000 : ℚ) : ℝ) ≤ stT191 33 := by
  have hc : ((576611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125468823767/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((576611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c34 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((186109/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187449/2000000) (δ := 9733/1000000000) (ψ := 859139/1000000) 191 107
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t34 : ((63831398703/400000000000 : ℚ) : ℝ) ≤ stT191 34 := by
  have hc : ((186099/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63831398703/400000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((186099/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c35 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((23293/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -929187/10000000) (δ := 4863/500000000) (ψ := 859139/1000000) 191 108
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t35 : ((39370231359/250000000000 : ℚ) : ℝ) ≤ stT191 35 := by
  have hc : ((93167/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39370231359/250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((93167/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c36 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((1169/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -637109/2000000) (δ := 599/62500000) (ψ := 859139/1000000) 191 109
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t36 : ((1217499513/25000000000 : ℚ) : ℝ) ≤ stT191 36 := by
  have hc : ((1461/5000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1217499513/25000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((1461/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c37 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-684121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2905243/5000000) (δ := 2403/250000000) (ψ := 859139/1000000) 191 110
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t37 : ((-112477028229/1000000000000 : ℚ) : ℝ) ≤ stT191 37 := by
  have hc : ((-684171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112477028229/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-684171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c38 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-116443/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 346179/500000) (δ := 9691/1000000000) (ψ := 859139/1000000) 191 110
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t38 : ((-151124576071/1000000000000 : ℚ) : ℝ) ≤ stT191 38 := by
  have hc : ((-465797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151124576071/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-465797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c39 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((122917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1809459/5000000) (δ := 4849/500000000) (ψ := 859139/1000000) 191 111
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t39 : ((196744592627/10000000000000 : ℚ) : ℝ) ≤ stT191 39 := by
  have hc : ((122867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196744592627/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((122867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c40 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51/2500000) (δ := 4803/500000000) (ψ := 859139/1000000) 191 112
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t40 : ((15810589431/100000000000 : ℚ) : ℝ) ≤ stT191 40 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15810589431/100000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c41 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((3979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3917043/10000000) (δ := 959/100000000) (ψ := 859139/1000000) 191 113
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t41 : ((6136064673/10000000000000 : ℚ) : ℝ) ≤ stT191 41 := by
  have hc : ((3929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6136064673/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((3929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c42 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-248603/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7589561/10000000) (δ := 959/100000000) (ψ := 859139/1000000) 191 113
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t42 : ((-383622169427/2500000000000 : ℚ) : ℝ) ≤ stT191 42 := by
  have hc : ((-497231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383622169427/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-497231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c43 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((318201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 779353/2500000) (δ := 243/25000000) (ψ := 859139/1000000) 191 114
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t43 : ((97035100547/2000000000000 : ℚ) : ℝ) ≤ stT191 43 := by
  have hc : ((318151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97035100547/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((318151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c44 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((199741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -322613/2000000) (δ := 9727/1000000000) (ψ := 859139/1000000) 191 115
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t44 : ((150550949273/1250000000000 : ℚ) : ℝ) ≤ stT191 44 := by
  have hc : ((399457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150550949273/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((399457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c45 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-874939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6590267/10000000) (δ := 9669/1000000000) (ψ := 859139/1000000) 191 116
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t45 : ((-163044575271/1250000000000 : ℚ) : ℝ) ≤ stT191 45 := by
  have hc : ((-874989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163044575271/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-874989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c46 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((8933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1952329/5000000) (δ := 9569/1000000000) (ψ := 859139/1000000) 191 116
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t46 : ((13097263977/10000000000000 : ℚ) : ℝ) ≤ stT191 46 := by
  have hc : ((8883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13097263977/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((8883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c47 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((81757/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1534047/10000000) (δ := 9561/1000000000) (ψ := 859139/1000000) 191 117
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t47 : ((14905934131/125000000000 : ℚ) : ℝ) ≤ stT191 47 := by
  have hc : ((10219/12500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14905934131/125000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((10219/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c48 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-964833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1797253/2500000) (δ := 4827/500000000) (ψ := 859139/1000000) 191 118
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t48 : ((-87043060313/625000000000 : ℚ) : ℝ) ≤ stT191 48 := by
  have hc : ((-964883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87043060313/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-964883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c49 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((121637/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166041/625000) (δ := 4827/500000000) (ψ := 859139/1000000) 191 118
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t49 : ((347498467179/5000000000000 : ℚ) : ℝ) ≤ stT191 49 := by
  have hc : ((243249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((347498467179/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((243249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c50 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((20749/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -340447/1000000) (δ := 2389/250000000) (ψ := 859139/1000000) 191 119
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t50 : ((3667054309/125000000000 : ℚ) : ℝ) ≤ stT191 50 := by
  have hc : ((2593/12500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3667054309/125000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((2593/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c51 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-75109/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6051271/10000000) (δ := 9747/1000000000) (ψ := 859139/1000000) 191 119
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t51 : ((-52590353517/500000000000 : ℚ) : ℝ) ≤ stT191 51 := by
  have hc : ((-37557/50000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52590353517/500000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-37557/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c52 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((988193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -384549/10000000) (δ := 9563/1000000000) (ψ := 859139/1000000) 191 120
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t52 : ((5481229221/40000000000 : ℚ) : ℝ) ≤ stT191 52 := by
  have hc : ((988143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5481229221/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((988143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c53 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-941819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6996997/10000000) (δ := 9633/1000000000) (ψ := 859139/1000000) 191 121
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t53 : ((-646878454807/5000000000000 : ℚ) : ℝ) ≤ stT191 53 := by
  have hc : ((-941869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-646878454807/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-941869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c54 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((716941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1928481/10000000) (δ := 957/100000000) (ψ := 859139/1000000) 191 121
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t54 : ((975564628857/10000000000000 : ℚ) : ℝ) ≤ stT191 54 := by
  have hc : ((716891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((975564628857/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((716891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c55 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-211303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5017787/10000000) (δ := 9577/1000000000) (ψ := 859139/1000000) 191 122
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t55 : ((-5565521/97656250 : ℚ) : ℝ) ≤ stT191 55 := by
  have hc : ((-6604/15625 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5565521/97656250 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-6604/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c56 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((27191/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3586047/10000000) (δ := 9677/1000000000) (ψ := 859139/1000000) 191 122
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t56 : ((18161066693/1000000000000 : ℚ) : ℝ) ≤ stT191 56 := by
  have hc : ((27181/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18161066693/1000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((27181/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c57 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((102473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1835179/5000000) (δ := 4859/500000000) (ψ := 859139/1000000) 191 123
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t57 : ((33915635259/2500000000000 : ℚ) : ℝ) ≤ stT191 57 := by
  have hc : ((102423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33915635259/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((102423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c58 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-8723/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4634227/10000000) (δ := 1917/200000000) (ψ := 859139/1000000) 191 123
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t58 : ((-36658936509/1000000000000 : ℚ) : ℝ) ≤ stT191 58 := by
  have hc : ((-139593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36658936509/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-139593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c59 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((395243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72779/250000) (δ := 2423/250000000) (ψ := 859139/1000000) 191 124
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t59 : ((514497419577/10000000000000 : ℚ) : ℝ) ≤ stT191 59 := by
  have hc : ((395193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((514497419577/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((395193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c60 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-228623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 511423/1000000) (δ := 1199/125000000) (ψ := 859139/1000000) 191 124
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t60 : ((-7379585619/125000000000 : ℚ) : ℝ) ≤ stT191 60 := by
  have hc : ((-28581/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7379585619/125000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-28581/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c61 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((235489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2700993/10000000) (δ := 1213/125000000) (ψ := 859139/1000000) 191 125
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t61 : ((2355316959/39062500000 : ℚ) : ℝ) ≤ stT191 61 := by
  have hc : ((29433/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2355316959/39062500000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((29433/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c62 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-439069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1265849/2500000) (δ := 2401/250000000) (ψ := 859139/1000000) 191 125
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t62 : ((-278841004119/5000000000000 : ℚ) : ℝ) ≤ stT191 62 := by
  have hc : ((-439119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278841004119/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-439119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c63 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((180363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -375547/1250000) (δ := 4803/500000000) (ψ := 859139/1000000) 191 126
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t63 : ((113602209889/2500000000000 : ℚ) : ℝ) ≤ stT191 63 := by
  have hc : ((90169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113602209889/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((90169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c64 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-233211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4515437/10000000) (δ := 9597/1000000000) (ψ := 859139/1000000) 191 126
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t64 : ((-291576483261/10000000000000 : ℚ) : ℝ) ≤ stT191 64 := by
  have hc : ((-233261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291576483261/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-233261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c65 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((2753/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3789271/10000000) (δ := 969/100000000) (ψ := 859139/1000000) 191 127
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t65 : ((6823148847/1000000000000 : ℚ) : ℝ) ≤ stT191 65 := by
  have hc : ((5501/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6823148847/1000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((5501/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c66 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((42397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3500961/10000000) (δ := 9713/1000000000) (ψ := 859139/1000000) 191 127
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t66 : ((52171674433/2500000000000 : ℚ) : ℝ) ≤ stT191 66 := by
  have hc : ((84769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52171674433/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((84769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c67 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-425727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1005281/2000000) (δ := 243/25000000) (ψ := 859139/1000000) 191 128
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t67 : ((-104033926403/2000000000000 : ℚ) : ℝ) ≤ stT191 67 := by
  have hc : ((-425777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104033926403/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-425777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c68 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((682863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 409561/2000000) (δ := 481/50000000) (ψ := 859139/1000000) 191 128
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t68 : ((414016151607/5000000000000 : ℚ) : ℝ) ≤ stT191 68 := by
  have hc : ((682813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414016151607/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((682813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c69 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-446709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6689231/10000000) (δ := 19/1953125) (ψ := 859139/1000000) 191 129
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t69 : ((-268902373253/2500000000000 : ℚ) : ℝ) ≤ stT191 69 := by
  have hc : ((-223367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268902373253/2500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-223367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c70 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((997369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181373/10000000) (δ := 2407/250000000) (ψ := 859139/1000000) 191 129
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t70 : ((298005898433/2500000000000 : ℚ) : ℝ) ≤ stT191 70 := by
  have hc : ((997319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298005898433/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((997319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c71 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-935973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6954519/10000000) (δ := 387/40000000) (ψ := 859139/1000000) 191 129
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t71 : ((-555427623993/5000000000000 : ℚ) : ℝ) ≤ stT191 71 := by
  have hc : ((-936023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-555427623993/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-936023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c72 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((2109/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1037493/5000000) (δ := 2417/250000000) (ψ := 859139/1000000) 191 130
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t72 : ((79529457813/1000000000000 : ℚ) : ℝ) ≤ stT191 72 := by
  have hc : ((67483/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79529457813/1000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((67483/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c73 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-231607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 902263/2000000) (δ := 299/31250000) (ψ := 859139/1000000) 191 130
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t73 : ((-67783533171/2500000000000 : ℚ) : ℝ) ≤ stT191 73 := by
  have hc : ((-231657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67783533171/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-231657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c74 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-30429/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2349987/5000000) (δ := 4821/500000000) (ψ := 859139/1000000) 191 131
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t74 : ((-17689412509/500000000000 : ℚ) : ℝ) ≤ stT191 74 := by
  have hc : ((-15217/50000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17689412509/500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-15217/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c75 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((193791/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 427389/2500000) (δ := 9561/1000000000) (ψ := 859139/1000000) 191 131
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t75 : ((4475120679/50000000000 : ℚ) : ℝ) ≤ stT191 75 := by
  have hc : ((387557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4475120679/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((387557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c76 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-199481/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239807/312500) (δ := 9649/1000000000) (ψ := 859139/1000000) 191 132
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t76 : ((-228831936789/2000000000000 : ℚ) : ℝ) ≤ stT191 76 := by
  have hc : ((-199491/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228831936789/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-199491/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c77 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((840409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -178987/1250000) (δ := 9749/1000000000) (ψ := 859139/1000000) 191 132
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t77 : ((191535463639/2000000000000 : ℚ) : ℝ) ≤ stT191 77 := by
  have hc : ((840359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191535463639/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((840359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c78 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-31551/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4729477/10000000) (δ := 4777/500000000) (ψ := 859139/1000000) 191 132
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t78 : ((-4466270571/125000000000 : ℚ) : ℝ) ≤ stT191 78 := by
  have hc : ((-7889/25000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4466270571/125000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-7889/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c79 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-94457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2447807/5000000) (δ := 9647/1000000000) (ψ := 859139/1000000) 191 133
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t79 : ((-6642906301/156250000000 : ℚ) : ℝ) ≤ stT191 79 := by
  have hc : ((-188939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6642906301/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-188939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c80 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((90291/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1110763/10000000) (δ := 9647/1000000000) (ψ := 859139/1000000) 191 133
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t80 : ((50471363719/500000000000 : ℚ) : ℝ) ≤ stT191 80 := by
  have hc : ((45143/50000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50471363719/500000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((45143/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c81 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-473891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7042507/10000000) (δ := 2389/250000000) (ψ := 859139/1000000) 191 133
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t81 : ((-16455429831/156250000000 : ℚ) : ℝ) ≤ stT191 81 := by
  have hc : ((-118479/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16455429831/156250000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-118479/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c82 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((216673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701621/2500000) (δ := 9739/1000000000) (ψ := 859139/1000000) 191 134
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t82 : ((5981190903/125000000000 : ℚ) : ℝ) ≤ stT191 82 := by
  have hc : ((27081/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5981190903/125000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((27081/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c83 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((1477/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 596297/2000000) (δ := 2391/250000000) (ψ := 859139/1000000) 191 134
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t83 : ((506561783/12500000000 : ℚ) : ℝ) ≤ stT191 83 := by
  have hc : ((923/2500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506561783/12500000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((923/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c84 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-117909/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7007867/10000000) (δ := 601/31250000) (ψ := 859139/1000000) 191 135
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t84 : ((-51462460049/500000000000 : ℚ) : ℝ) ≤ stT191 84 := by
  have hc : ((-471661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51462460049/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-471661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c85 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((856283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1356917/10000000) (δ := 301/31250000) (ψ := 859139/1000000) 191 135
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t85 : ((232178708979/2500000000000 : ℚ) : ℝ) ≤ stT191 85 := by
  have hc : ((856233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232178708979/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((856233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c86 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-60041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4227923/10000000) (δ := 301/31250000) (ψ := 859139/1000000) 191 135
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t86 : ((-4048178103/312500000000 : ℚ) : ℝ) ≤ stT191 86 := by
  have hc : ((-30033/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4048178103/312500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-30033/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c87 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-726413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595971/1000000) (δ := 4839/500000000) (ψ := 859139/1000000) 191 136
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t87 : ((-778850426319/10000000000000 : ℚ) : ℝ) ≤ stT191 87 := by
  have hc : ((-726463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-778850426319/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-726463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c88 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((979867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251253/5000000) (δ := 4789/500000000) (ψ := 859139/1000000) 191 136
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t88 : ((1044487861451/10000000000000 : ℚ) : ℝ) ≤ stT191 88 := by
  have hc : ((979817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1044487861451/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((979817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c89 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-188431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 978601/2000000) (δ := 77/8000000) (ψ := 859139/1000000) 191 136
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t89 : ((-12485186443/312500000000 : ℚ) : ℝ) ≤ stT191 89 := by
  have hc : ((-23557/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12485186443/312500000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-23557/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c90 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-581919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5479707/10000000) (δ := 1937/200000000) (ψ := 859139/1000000) 191 137
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t90 : ((-613449449117/10000000000000 : ℚ) : ℝ) ≤ stT191 90 := by
  have hc : ((-581969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-613449449117/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-581969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c91 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((249173/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50851/2500000) (δ := 9559/500000000) (ψ := 859139/1000000) 191 137
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t91 : ((130595482791/1250000000000 : ℚ) : ℝ) ≤ stT191 91 := by
  have hc : ((498321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130595482791/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((498321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c92 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-210837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5015217/10000000) (δ := 4859/500000000) (ψ := 859139/1000000) 191 137
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t92 : ((-109919513963/2500000000000 : ℚ) : ℝ) ≤ stT191 92 := by
  have hc : ((-105431/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109919513963/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-105431/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c93 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-299167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5530541/10000000) (δ := 1199/125000000) (ψ := 859139/1000000) 191 138
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t93 : ((-4847620981/78125000000 : ℚ) : ℝ) ≤ stT191 93 := by
  have hc : ((-37399/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4847620981/78125000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-37399/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c94 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((246421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84707/2000000) (δ := 2423/250000000) (ψ := 859139/1000000) 191 138
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t94 : ((508301802957/5000000000000 : ℚ) : ℝ) ≤ stT191 94 := by
  have hc : ((492817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((508301802957/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((492817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c95 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-34661/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4629417/10000000) (δ := 9711/1000000000) (ψ := 859139/1000000) 191 138
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t95 : ((-142271481951/5000000000000 : ℚ) : ℝ) ≤ stT191 95 := by
  have hc : ((-138669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142271481951/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-138669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c96 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-189559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12157/20000) (δ := 9599/1000000000) (ψ := 859139/1000000) 191 139
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t96 : ((-386961307803/5000000000000 : ℚ) : ℝ) ≤ stT191 96 := by
  have hc : ((-379143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386961307803/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-379143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c97 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((899529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1130263/10000000) (δ := 9599/1000000000) (ψ := 859139/1000000) 191 139
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t97 : ((456641202367/5000000000000 : ℚ) : ℝ) ≤ stT191 97 := by
  have hc : ((899479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((456641202367/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((899479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c98 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((31933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 235451/625000) (δ := 9699/1000000000) (ψ := 859139/1000000) 191 139
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t98 : ((1007247813/156250000000 : ℚ) : ℝ) ≤ stT191 98 := by
  have hc : ((7977/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1007247813/156250000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((7977/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c99 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-477013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7092977/10000000) (δ := 303/31250000) (ψ := 859139/1000000) 191 140
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t99 : ((-119860329361/1250000000000 : ℚ) : ℝ) ≤ stT191 99 := by
  have hc : ((-238519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119860329361/1250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-238519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c100 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((607741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1146979/5000000) (δ := 9707/1000000000) (ψ := 859139/1000000) 191 140
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t100 : ((607690392309/10000000000000 : ℚ) : ℝ) ≤ stT191 100 := by
  have hc : ((607691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((607690392309/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((607691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c101 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((34661/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1228679/5000000) (δ := 9707/1000000000) (ψ := 859139/1000000) 191 140
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t101 : ((275886943731/5000000000000 : ℚ) : ℝ) ≤ stT191 101 := by
  have hc : ((277263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275886943731/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((277263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c102 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-480959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7161831/10000000) (δ := 9607/1000000000) (ψ := 859139/1000000) 191 140
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t102 : ((-14882667051/156250000000 : ℚ) : ℝ) ≤ stT191 102 := by
  have hc : ((-60123/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14882667051/156250000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-60123/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c103 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((7879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -777519/2000000) (δ := 9689/1000000000) (ψ := 859139/1000000) 191 141
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t103 : ((3869386983/2500000000000 : ℚ) : ℝ) ≤ stT191 103 := by
  have hc : ((3927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3869386983/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((3927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c104 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((479067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725963/10000000) (δ := 4857/500000000) (ψ := 859139/1000000) 191 141
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t104 : ((11743475109/125000000000 : ℚ) : ℝ) ≤ stT191 104 := by
  have hc : ((239521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11743475109/125000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((239521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c105 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-260219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5295399/10000000) (δ := 4807/500000000) (ψ := 859139/1000000) 191 141
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t105 : ((-63493094961/1250000000000 : ℚ) : ℝ) ≤ stT191 105 := by
  have hc : ((-65061/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63493094961/1250000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-65061/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c106 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-352987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1177297/2000000) (δ := 9621/1000000000) (ψ := 859139/1000000) 191 142
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t106 : ((-42859451679/625000000000 : ℚ) : ℝ) ≤ stT191 106 := by
  have hc : ((-88253/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42859451679/625000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-88253/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c107 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((105831/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175357/1250000) (δ := 4841/500000000) (ψ := 859139/1000000) 191 142
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t107 : ((25576148879/312500000000 : ℚ) : ℝ) ≤ stT191 107 := by
  have hc : ((423299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25576148879/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((423299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c108 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((347759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9497/31250) (δ := 4841/500000000) (ψ := 859139/1000000) 191 142
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t108 : ((1338331941/40000000000 : ℚ) : ℝ) ≤ stT191 108 := by
  have hc : ((347709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1338331941/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((347709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c109 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-986319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7439967/10000000) (δ := 9621/1000000000) (ψ := 859139/1000000) 191 142
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t109 : ((-944770860163/10000000000000 : ℚ) : ℝ) ≤ stT191 109 := by
  have hc : ((-986369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-944770860163/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-986369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c110 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((1581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -976807/2500000) (δ := 387/40000000) (ψ := 859139/1000000) 191 143
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t110 : ((748944401/1000000000000 : ℚ) : ℝ) ≤ stT191 110 := by
  have hc : ((1571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((748944401/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((1571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c111 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((986313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4141/100000) (δ := 19/1953125) (ψ := 859139/1000000) 191 143
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t111 : ((936118430291/10000000000000 : ℚ) : ℝ) ≤ stT191 111 := by
  have hc : ((986263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((936118430291/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((986263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c112 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-303007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2348303/5000000) (δ := 383/40000000) (ψ := 859139/1000000) 191 143
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t112 : ((-17897637249/625000000000 : ℚ) : ℝ) ≤ stT191 112 := by
  have hc : ((-303057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17897637249/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-303057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c113 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-453467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338343/500000) (δ := 2417/250000000) (ψ := 859139/1000000) 191 144
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t113 : ((-106652361933/1250000000000 : ℚ) : ℝ) ≤ stT191 113 := by
  have hc : ((-113373/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106652361933/1250000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-113373/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c114 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((260011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1279899/5000000) (δ := 1927/200000000) (ψ := 859139/1000000) 191 144
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t114 : ((24349898781/500000000000 : ℚ) : ℝ) ≤ stT191 114 := by
  have hc : ((129993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24349898781/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((129993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c115 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((79957/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100659/625000) (δ := 1947/200000000) (ψ := 859139/1000000) 191 144
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t115 : ((582465311/7812500000 : ℚ) : ℝ) ≤ stT191 115 := by
  have hc : ((4997/6250 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((582465311/7812500000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((4997/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c116 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-132941/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5744739/10000000) (δ := 1947/200000000) (ψ := 859139/1000000) 191 144
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t116 : ((-123441945627/2000000000000 : ℚ) : ℝ) ≤ stT191 116 := by
  have hc : ((-132951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123441945627/2000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-132951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c117 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-699707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293223/500000) (δ := 9643/1000000000) (ψ := 859139/1000000) 191 145
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t117 : ((-646926046257/10000000000000 : ℚ) : ℝ) ≤ stT191 117 := by
  have hc : ((-699757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-646926046257/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-699757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c118 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((751647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1800601/10000000) (δ := 239/25000000) (ψ := 859139/1000000) 191 145
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t118 : ((345950328339/5000000000000 : ℚ) : ℝ) ≤ stT191 118 := by
  have hc : ((751597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345950328339/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((751597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c119 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((628191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1114463/5000000) (δ := 239/25000000) (ψ := 859139/1000000) 191 145
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t119 : ((287907799209/5000000000000 : ℚ) : ℝ) ≤ stT191 119 := by
  have hc : ((628141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287907799209/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((628141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c120 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-198767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6224789/10000000) (δ := 483/50000000) (ψ := 859139/1000000) 191 145
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t120 : ((-362920081889/5000000000000 : ℚ) : ℝ) ≤ stT191 120 := by
  have hc : ((-397559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362920081889/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-397559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c121 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-59511/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5520497/10000000) (δ := 9553/1000000000) (ψ := 859139/1000000) 191 146
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t121 : ((-13526364989/250000000000 : ℚ) : ℝ) ≤ stT191 121 := by
  have hc : ((-14879/25000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13526364989/250000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-14879/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c122 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((1287/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1590433/10000000) (δ := 193/20000000) (ψ := 859139/1000000) 191 146
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t122 : ((29128050761/400000000000 : ℚ) : ℝ) ≤ stT191 122 := by
  have hc : ((32173/40000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29128050761/400000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((32173/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c123 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((603417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2307543/10000000) (δ := 39/4000000) (ψ := 859139/1000000) 191 146
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t123 : ((544037319523/10000000000000 : ℚ) : ℝ) ≤ stT191 123 := by
  have hc : ((603367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544037319523/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((603367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c124 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-195643/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543489/2500000) (δ := 39/4000000) (ψ := 859139/1000000) 191 146
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t124 : ((-351407843397/5000000000000 : ℚ) : ℝ) ≤ stT191 124 := by
  have hc : ((-391311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351407843397/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-391311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c125 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-325407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -712329/1250000) (δ := 9657/1000000000) (ψ := 859139/1000000) 191 147
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t125 : ((-9096109153/156250000000 : ℚ) : ℝ) ≤ stT191 125 := by
  have hc : ((-40679/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9096109153/156250000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-40679/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c126 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((363269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1893817/10000000) (δ := 4823/500000000) (ψ := 859139/1000000) 191 147
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t126 : ((8090079557/125000000000 : ℚ) : ℝ) ≤ stT191 126 := by
  have hc : ((90811/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8090079557/125000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((90811/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c127 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((730087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 470217/2500000) (δ := 4873/500000000) (ψ := 859139/1000000) 191 147
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t127 : ((161950678043/2500000000000 : ℚ) : ℝ) ≤ stT191 127 := by
  have hc : ((730037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161950678043/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((730037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c128 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-157121/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1406499/2500000) (δ := 4873/500000000) (ψ := 859139/1000000) 191 147
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t128 : ((-69443893257/1250000000000 : ℚ) : ℝ) ≤ stT191 128 := by
  have hc : ((-314267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69443893257/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-314267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c129 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-828033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3182983/5000000) (δ := 151/15625000) (ψ := 859139/1000000) 191 148
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t129 : ((-729086505433/10000000000000 : ℚ) : ℝ) ≤ stT191 129 := by
  have hc : ((-828083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729086505433/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-828083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c130 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((239411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2678711/10000000) (δ := 151/15625000) (ψ := 859139/1000000) 191 148
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t130 : ((52488851597/1250000000000 : ℚ) : ℝ) ≤ stT191 130 := by
  have hc : ((119693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52488851597/1250000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((119693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c131 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((924097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 980323/10000000) (δ := 9739/1000000000) (ψ := 859139/1000000) 191 148
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t131 : ((100917945011/1250000000000 : ℚ) : ℝ) ≤ stT191 131 := by
  have hc : ((924047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100917945011/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((924047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c132 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-270403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14411/31250) (δ := 2391/250000000) (ψ := 859139/1000000) 191 148
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t132 : ((-235399316217/10000000000000 : ℚ) : ℝ) ≤ stT191 132 := by
  have hc : ((-270453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235399316217/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-270453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c133 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-494787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1498531/2000000) (δ := 9671/1000000000) (ψ := 859139/1000000) 191 149
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t133 : ((-10726410833/125000000000 : ℚ) : ℝ) ≤ stT191 133 := by
  have hc : ((-123703/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10726410833/125000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-123703/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c134 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((139/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -391587/1000000) (δ := 4783/250000000) (ψ := 859139/1000000) 191 149
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t134 : ((474911433/1250000000000 : ℚ) : ℝ) ≤ stT191 134 := by
  have hc : ((2199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474911433/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((2199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c135 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((989321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -365681/10000000) (δ := 9671/1000000000) (ψ := 859139/1000000) 191 149
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t135 : ((425713978701/5000000000000 : ℚ) : ℝ) ≤ stT191 135 := by
  have hc : ((989271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((425713978701/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((989271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c136 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((37831/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 789579/2500000) (δ := 2433/250000000) (ψ := 859139/1000000) 191 149
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t136 : ((32434420527/1250000000000 : ℚ) : ℝ) ≤ stT191 136 := by
  have hc : ((151299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32434420527/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((151299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c137 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-177493/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6656529/10000000) (δ := 301/31250000) (ψ := 859139/1000000) 191 149
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t137 : ((-75825554037/1000000000000 : ℚ) : ℝ) ≤ stT191 137 := by
  have hc : ((-177503/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75825554037/1000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-177503/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c138 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-613663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34867/62500) (δ := 77/8000000) (ψ := 859139/1000000) 191 150
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t138 : ((-522427487241/10000000000000 : ℚ) : ℝ) ≤ stT191 138 := by
  have hc : ((-613713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522427487241/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-613713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c139 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((65817/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2131027/10000000) (δ := 389/40000000) (ψ := 859139/1000000) 191 150
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t139 : ((3488809291/62500000000 : ℚ) : ℝ) ≤ stT191 139 := by
  have hc : ((16453/25000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3488809291/62500000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((16453/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c140 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((434709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 322983/2500000) (δ := 77/8000000) (ψ := 859139/1000000) 191 150
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t140 : ((45921865167/625000000000 : ℚ) : ℝ) ≤ stT191 140 := by
  have hc : ((108671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45921865167/625000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((108671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c141 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-12027/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4690491/10000000) (δ := 4839/500000000) (ψ := 859139/1000000) 191 150
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t141 : ((-1266280801/50000000000 : ℚ) : ℝ) ≤ stT191 141 := by
  have hc : ((-12029/40000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1266280801/50000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-12029/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c142 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-996437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1528577/2000000) (δ := 9717/1000000000) (ψ := 859139/1000000) 191 151
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t142 : ((-418116976817/5000000000000 : ℚ) : ℝ) ≤ stT191 142 := by
  have hc : ((-996487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418116976817/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-996487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c143 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-72739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4291981/10000000) (δ := 9717/1000000000) (ψ := 859139/1000000) 191 151
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t143 : ((-15212096413/1250000000000 : ℚ) : ℝ) ≤ stT191 143 := by
  have hc : ((-18191/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15212096413/1250000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-18191/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c144 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((463251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482237/5000000) (δ := 4793/500000000) (ψ := 859139/1000000) 191 151
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t144 : ((193010756129/2500000000000 : ℚ) : ℝ) ≤ stT191 144 := by
  have hc : ((231613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193010756129/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((231613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c145 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((592993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 468013/2000000) (δ := 4843/500000000) (ψ := 859139/1000000) 191 151
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t145 : ((246205943061/5000000000000 : ℚ) : ℝ) ≤ stT191 145 := by
  have hc : ((592943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246205943061/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((592943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c146 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-392/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2810937/5000000) (δ := 9717/1000000000) (ψ := 859139/1000000) 191 151
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t146 : ((-1038231727/20000000000 : ℚ) : ℝ) ≤ stT191 146 := by
  have hc : ((-2509/4000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1038231727/20000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-2509/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c147 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-22919/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3413361/5000000) (δ := 971/100000000) (ψ := 859139/1000000) 191 152
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t147 : ((-75617296947/1000000000000 : ℚ) : ℝ) ≤ stT191 147 := by
  have hc : ((-91681/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75617296947/1000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-91681/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c148 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((6731/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -717883/2000000) (δ := 961/100000000) (ψ := 859139/1000000) 191 152
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t148 : ((5530786629/500000000000 : ℚ) : ℝ) ≤ stT191 148 := by
  have hc : ((13457/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5530786629/500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((13457/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c149 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((494419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186941/5000000) (δ := 9593/1000000000) (ψ := 859139/1000000) 191 152
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t149 : ((202511445507/2500000000000 : ℚ) : ℝ) ≤ stT191 149 := by
  have hc : ((247197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202511445507/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((247197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c150 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((428443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 705017/2500000) (δ := 9693/1000000000) (ψ := 859139/1000000) 191 152
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t150 : ((21861323183/625000000000 : ℚ) : ℝ) ≤ stT191 150 := by
  have hc : ((428393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21861323183/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((428393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c151 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-735463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187277/312500) (δ := 961/100000000) (ψ := 859139/1000000) 191 152
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t151 : ((-598552388757/10000000000000 : ℚ) : ℝ) ≤ stT191 151 := by
  have hc : ((-735513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-598552388757/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-735513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c152 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-434829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312653/2000000) (δ := 9603/1000000000) (ψ := 859139/1000000) 191 153
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t152 : ((-44089194779/625000000000 : ℚ) : ℝ) ≤ stT191 152 := by
  have hc : ((-217427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44089194779/625000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-217427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c153 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((24583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1716053/5000000) (δ := 97/10000000) (ψ := 859139/1000000) 191 153
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t153 : ((19869122691/1250000000000 : ℚ) : ℝ) ≤ stT191 153 := by
  have hc : ((98307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19869122691/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((98307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c154 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((991751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321337/10000000) (δ := 3/312500) (ψ := 859139/1000000) 191 153
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t154 : ((399567241611/5000000000000 : ℚ) : ℝ) ≤ stT191 154 := by
  have hc : ((991701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399567241611/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((991701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c155 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((446709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1384641/5000000) (δ := 97/10000000) (ψ := 859139/1000000) 191 153
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t155 : ((358764995321/10000000000000 : ℚ) : ℝ) ≤ stT191 155 := by
  have hc : ((446659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358764995321/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((446659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c156 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-346347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1460009/2500000) (δ := 9703/1000000000) (ψ := 859139/1000000) 191 153
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t156 : ((-69329906113/1250000000000 : ℚ) : ℝ) ≤ stT191 156 := by
  have hc : ((-86593/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69329906113/1250000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-86593/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c157 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-915167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6816797/10000000) (δ := 9707/1000000000) (ψ := 859139/1000000) 191 154
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t157 : ((-730422789879/10000000000000 : ℚ) : ℝ) ≤ stT191 157 := by
  have hc : ((-915217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-730422789879/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-915217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c158 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((7093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1892527/5000000) (δ := 9707/1000000000) (ψ := 859139/1000000) 191 154
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t158 : ((22551654279/5000000000000 : ℚ) : ℝ) ≤ stT191 158 := by
  have hc : ((28347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22551654279/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((28347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c159 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((952649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772411/10000000) (δ := 9707/1000000000) (ψ := 859139/1000000) 191 154
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t159 : ((755459589549/10000000000000 : ℚ) : ℝ) ≤ stT191 159 := by
  have hc : ((952599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((755459589549/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((952599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c160 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((315277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2221323/10000000) (δ := 9707/1000000000) (ψ := 859139/1000000) 191 154
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t160 : ((62307114597/1250000000000 : ℚ) : ℝ) ≤ stT191 160 := by
  have hc : ((78813/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62307114597/1250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((78813/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c161 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-486219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2598193/5000000) (δ := 303/31250000) (ψ := 859139/1000000) 191 154
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t161 : ((-383233947859/10000000000000 : ℚ) : ℝ) ≤ stT191 161 := by
  have hc : ((-486269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383233947859/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-486269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c162 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-248213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7554897/10000000) (δ := 9589/1000000000) (ψ := 859139/1000000) 191 155
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t162 : ((-15601965577/200000000000 : ℚ) : ℝ) ≤ stT191 162 := by
  have hc : ((-496451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15601965577/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-496451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c163 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-136143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461641/1000000) (δ := 9689/1000000000) (ψ := 859139/1000000) 191 155
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t163 : ((-13331885481/625000000000 : ℚ) : ℝ) ≤ stT191 163 := by
  have hc : ((-17021/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13331885481/625000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-17021/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c164 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((778597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -423981/2500000) (δ := 4807/500000000) (ψ := 859139/1000000) 191 155
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t164 : ((151985609699/2500000000000 : ℚ) : ℝ) ≤ stT191 164 := by
  have hc : ((778547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151985609699/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((778547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c165 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((110717/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 603399/5000000) (δ := 9689/1000000000) (ψ := 859139/1000000) 191 155
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t165 : ((172376194907/2500000000000 : ℚ) : ℝ) ≤ stT191 165 := by
  have hc : ((442843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172376194907/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((442843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c166 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-13191/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4091997/10000000) (δ := 4857/500000000) (ψ := 859139/1000000) 191 155
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t166 : ((-10245969351/2000000000000 : ℚ) : ℝ) ≤ stT191 166 := by
  have hc : ((-13201/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10245969351/2000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-13201/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c167 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-936729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6959909/10000000) (δ := 9689/1000000000) (ψ := 859139/1000000) 191 155
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t167 : ((-11326594889/156250000000 : ℚ) : ℝ) ≤ stT191 167 := by
  have hc : ((-936779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11326594889/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-936779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c168 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-8863/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5897331/10000000) (δ := 4811/500000000) (ψ := 859139/1000000) 191 156
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t168 : ((-54707498953/1000000000000 : ℚ) : ℝ) ≤ stT191 168 := by
  have hc : ((-70909/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54707498953/1000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-70909/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c169 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((338583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382933/1250000) (δ := 4811/500000000) (ψ := 859139/1000000) 191 156
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t169 : ((26040973959/1000000000000 : ℚ) : ℝ) ≤ stT191 169 := by
  have hc : ((338533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26040973959/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((338533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c170 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((995149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246357/10000000) (δ := 4861/500000000) (ψ := 859139/1000000) 191 156
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t170 : ((190801277359/2500000000000 : ℚ) : ℝ) ≤ stT191 170 := by
  have hc : ((995099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190801277359/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((995099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c171 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((130481/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 638557/2500000) (δ := 4811/500000000) (ψ := 859139/1000000) 191 156
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t171 : ((199543481703/5000000000000 : ℚ) : ℝ) ≤ stT191 171 := by
  have hc : ((260937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199543481703/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((260937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c172 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-21403/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5338483/10000000) (δ := 4861/500000000) (ψ := 859139/1000000) 191 156
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t172 : ((-3264232533/80000000000 : ℚ) : ℝ) ≤ stT191 172 := by
  have hc : ((-4281/8000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3264232533/80000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-4281/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c173 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-994899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1520273/2000000) (δ := 9729/1000000000) (ψ := 859139/1000000) 191 157
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t173 : ((-378222897707/5000000000000 : ℚ) : ℝ) ≤ stT191 173 := by
  have hc : ((-994949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378222897707/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-994949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c174 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-180287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4849199/10000000) (δ := 4837/500000000) (ψ := 859139/1000000) 191 157
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t174 : ((-17086793361/625000000000 : ℚ) : ℝ) ≤ stT191 174 := by
  have hc : ((-22539/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17086793361/625000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-22539/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c175 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((132729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2112789/10000000) (δ := 9729/1000000000) (ψ := 859139/1000000) 191 157
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t175 : ((12540751029/250000000000 : ℚ) : ℝ) ≤ stT191 175 := by
  have hc : ((132719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12540751029/250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((132719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c176 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((242643/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304003/5000000) (δ := 9729/1000000000) (ψ := 859139/1000000) 191 157
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t176 : ((182889533029/2500000000000 : ℚ) : ℝ) ≤ stT191 176 := by
  have hc : ((485261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182889533029/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((485261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c177 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((24297/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132537/400000) (δ := 4787/500000000) (ψ := 859139/1000000) 191 157
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t177 : ((2282373079/125000000000 : ℚ) : ℝ) ≤ stT191 177 := by
  have hc : ((6073/25000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2282373079/125000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((6073/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c178 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-184589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1200713/2000000) (δ := 9729/1000000000) (ψ := 859139/1000000) 191 157
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t178 : ((-69182365749/1250000000000 : ℚ) : ℝ) ≤ stT191 178 := by
  have hc : ((-369203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69182365749/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-369203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c179 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-236521/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70293/100000) (δ := 1217/125000000) (ψ := 859139/1000000) 191 158
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t179 : ((-88396826553/1250000000000 : ℚ) : ℝ) ≤ stT191 179 := by
  have hc : ((-473067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88396826553/1250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-473067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c180 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-87971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1092287/2500000) (δ := 9567/1000000000) (ψ := 859139/1000000) 191 158
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t180 : ((-4099271661/312500000000 : ℚ) : ℝ) ≤ stT191 180 := by
  have hc : ((-21999/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4099271661/312500000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-21999/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c181 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((96447/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -861851/5000000) (δ := 1217/125000000) (ψ := 859139/1000000) 191 158
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t181 : ((143367661661/2500000000000 : ℚ) : ℝ) ≤ stT191 181 := by
  have hc : ((385763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143367661661/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((385763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c182 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((116861/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 226783/2500000) (δ := 1217/125000000) (ψ := 859139/1000000) 191 158
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t182 : ((346473866331/5000000000000 : ℚ) : ℝ) ≤ stT191 182 := by
  have hc : ((467419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346473866331/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((467419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c183 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((8033/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3523593/10000000) (δ := 2409/250000000) (ψ := 859139/1000000) 191 158
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t183 : ((11872628481/1000000000000 : ℚ) : ℝ) ≤ stT191 183 := by
  have hc : ((16061/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11872628481/1000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((16061/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c184 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-770429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6125777/10000000) (δ := 2409/250000000) (ψ := 859139/1000000) 191 158
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t184 : ((-56800482359/1000000000000 : ℚ) : ℝ) ≤ stT191 184 := by
  have hc : ((-770479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56800482359/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-770479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c185 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-235357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6994089/10000000) (δ := 483/50000000) (ψ := 859139/1000000) 191 159
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t185 : ((-69218874777/1000000000000 : ℚ) : ℝ) ≤ stT191 185 := by
  have hc : ((-470739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69218874777/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-470739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c186 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-195921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2209991/5000000) (δ := 483/50000000) (ψ := 859139/1000000) 191 159
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t186 : ((-35923248039/2500000000000 : ℚ) : ℝ) ≤ stT191 186 := by
  have hc : ((-195971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35923248039/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-195971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c187 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((735867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1859627/10000000) (δ := 483/50000000) (ψ := 859139/1000000) 191 159
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t187 : ((67260296153/1250000000000 : ℚ) : ℝ) ≤ stT191 187 := by
  have hc : ((735817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67260296153/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((735817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c188 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((962477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42939/625000) (δ := 239/25000000) (ψ := 859139/1000000) 191 159
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t188 : ((175480277337/2500000000000 : ℚ) : ℝ) ≤ stT191 188 := by
  have hc : ((962427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175480277337/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((962427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c189 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((139481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3220209/10000000) (δ := 483/50000000) (ψ := 859139/1000000) 191 159
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t189 : ((49530849/2441406250 : ℚ) : ℝ) ≤ stT191 189 := by
  have hc : ((4358/15625 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49530849/2441406250 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((4358/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c190 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-663281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5739977/10000000) (δ := 9643/1000000000) (ψ := 859139/1000000) 191 159
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t190 : ((-481231383887/10000000000000 : ℚ) : ℝ) ≤ stT191 190 := by
  have hc : ((-663331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-481231383887/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-663331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c191 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-61731/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3730699/5000000) (δ := 9553/1000000000) (ψ := 859139/1000000) 191 160
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t191 : ((-14294166239/200000000000 : ℚ) : ℝ) ≤ stT191 191 := by
  have hc : ((-493873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14294166239/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-493873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c192 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-101113/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4967941/10000000) (δ := 9653/1000000000) (ψ := 859139/1000000) 191 160
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t192 : ((-18245264961/625000000000 : ℚ) : ℝ) ≤ stT191 192 := by
  have hc : ((-202251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18245264961/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-202251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c193 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((34033/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19433/78125) (δ := 9653/1000000000) (ψ := 859139/1000000) 191 160
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t193 : ((39192343157/1000000000000 : ℚ) : ℝ) ≤ stT191 193 := by
  have hc : ((272239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39192343157/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((272239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c194 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((999969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2463/1250000) (δ := 9653/1000000000) (ψ := 859139/1000000) 191 160
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t194 : ((358949922701/5000000000000 : ℚ) : ℝ) ≤ stT191 194 := by
  have hc : ((999919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358949922701/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((999919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c195 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((561891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 487063/2000000) (δ := 193/20000000) (ψ := 859139/1000000) 191 160
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t195 : ((201171102937/5000000000000 : ℚ) : ℝ) ≤ stT191 195 := by
  have hc : ((561841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201171102937/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((561841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c196 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-92803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195111/400000) (δ := 9553/1000000000) (ψ := 859139/1000000) 191 160
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t196 : ((-66296812233/2500000000000 : ℚ) : ℝ) ≤ stT191 196 := by
  have hc : ((-185631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66296812233/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-185631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c197 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-976231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365391/500000) (δ := 9653/1000000000) (ψ := 859139/1000000) 191 160
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t197 : ((-695571900351/10000000000000 : ℚ) : ℝ) ≤ stT191 197 := by
  have hc : ((-976281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-695571900351/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-976281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c198 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-5861/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5982417/10000000) (δ := 9657/1000000000) (ψ := 859139/1000000) 191 161
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t198 : ((-2082760569/40000000000 : ℚ) : ℝ) ≤ stT191 198 := by
  have hc : ((-29307/40000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2082760569/40000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-29307/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c199 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((17449/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -894217/2500000) (δ := 4823/500000000) (ψ := 859139/1000000) 191 161
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t199 : ((49459336251/5000000000000 : ℚ) : ℝ) ≤ stT191 199 := by
  have hc : ((69771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49459336251/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((69771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c200 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((445021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1183399/10000000) (δ := 9557/1000000000) (ψ := 859139/1000000) 191 161
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t200 : ((39332417697/625000000000 : ℚ) : ℝ) ≤ stT191 200 := by
  have hc : ((111249/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39332417697/625000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((111249/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c201 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((887331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59909/500000) (δ := 9557/1000000000) (ψ := 859139/1000000) 191 161
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t201 : ((125167843389/2000000000000 : ℚ) : ℝ) ≤ stT191 201 := by
  have hc : ((887281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125167843389/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((887281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c202 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((28631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3567869/10000000) (δ := 4823/500000000) (ψ := 859139/1000000) 191 161
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t202 : ((20137649737/2000000000000 : ℚ) : ℝ) ≤ stT191 202 := by
  have hc : ((28621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20137649737/2000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((28621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c203 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-358527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5925907/10000000) (δ := 4873/500000000) (ψ := 859139/1000000) 191 161
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t203 : ((-31456797797/625000000000 : ℚ) : ℝ) ≤ stT191 203 := by
  have hc : ((-44819/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31456797797/625000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-44819/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c204 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-986031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7435621/10000000) (δ := 4819/500000000) (ψ := 859139/1000000) 191 162
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t204 : ((-690395737421/10000000000000 : ℚ) : ℝ) ≤ stT191 204 := by
  have hc : ((-986081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-690395737421/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-986081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c205 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-452407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2550323/5000000) (δ := 4819/500000000) (ψ := 859139/1000000) 191 162
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t205 : ((-316009994967/10000000000000 : ℚ) : ℝ) ≤ stT191 205 := by
  have hc : ((-452457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316009994967/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-452457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c206 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((110983/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -555407/2000000) (δ := 1933/200000000) (ψ := 859139/1000000) 191 162
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t206 : ((154633618753/5000000000000 : ℚ) : ℝ) ≤ stT191 206 := by
  have hc : ((221941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154633618753/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((221941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c207 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((491387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232347/5000000) (δ := 4819/500000000) (ψ := 859139/1000000) 191 162
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t207 : ((21345010961/312500000000 : ℚ) : ℝ) ≤ stT191 207 := by
  have hc : ((245681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21345010961/312500000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((245681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c208 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((742093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 918261/5000000) (δ := 1913/200000000) (ψ := 859139/1000000) 191 162
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t208 : ((4116112521/80000000000 : ℚ) : ℝ) ≤ stT191 208 := by
  have hc : ((742043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4116112521/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((742043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c209 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-39901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4126707/10000000) (δ := 4869/500000000) (ψ := 859139/1000000) 191 162
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t209 : ((-2761741309/500000000000 : ℚ) : ℝ) ≤ stT191 209 := by
  have hc : ((-19963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2761741309/500000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-19963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c210 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-26153/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3202979/5000000) (δ := 4819/500000000) (ψ := 859139/1000000) 191 162
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t210 : ((-144386994609/2500000000000 : ℚ) : ℝ) ≤ stT191 210 := by
  have hc : ((-418473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144386994609/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-418473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c211 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-946639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3516797/5000000) (δ := 9731/1000000000) (ψ := 859139/1000000) 191 163
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t211 : ((-651728161581/10000000000000 : ℚ) : ℝ) ≤ stT191 211 := by
  have hc : ((-946689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-651728161581/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-946689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c212 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-166543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2387963/5000000) (δ := 9631/1000000000) (ψ := 859139/1000000) 191 163
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t212 : ((-14299925263/625000000000 : ℚ) : ℝ) ≤ stT191 212 := by
  have hc : ((-20821/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14299925263/625000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-20821/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c213 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((530553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2528859/10000000) (δ := 9731/1000000000) (ψ := 859139/1000000) 191 163
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t213 : ((90873572391/2500000000000 : ℚ) : ℝ) ≤ stT191 213 := by
  have hc : ((530503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90873572391/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((530503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c214 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((993173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36537/1250000) (δ := 1209/125000000) (ψ := 859139/1000000) 191 163
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t214 : ((135776797191/2000000000000 : ℚ) : ℝ) ≤ stT191 214 := by
  have hc : ((993123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135776797191/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((993123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c215 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((715453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1933809/10000000) (δ := 1209/125000000) (ψ := 859139/1000000) 191 163
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t215 : ((243950276791/5000000000000 : ℚ) : ℝ) ≤ stT191 215 := by
  have hc : ((715403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243950276791/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((715403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c216 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-44463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5187/12500) (δ := 1209/125000000) (ψ := 859139/1000000) 191 163
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t216 : ((-1891891127/312500000000 : ℚ) : ℝ) ≤ stT191 216 := by
  have hc : ((-5561/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1891891127/312500000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-5561/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c217 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-412797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1588781/2500000) (δ := 9731/1000000000) (ψ := 859139/1000000) 191 163
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t217 : ((-28024215059/500000000000 : ℚ) : ℝ) ≤ stT191 217 := by
  have hc : ((-206411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28024215059/500000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-206411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c218 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-240359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7157437/10000000) (δ := 9579/1000000000) (ψ := 859139/1000000) 191 164
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t218 : ((-162800251749/2500000000000 : ℚ) : ℝ) ≤ stT191 218 := by
  have hc : ((-480743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162800251749/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-480743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c219 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-10149/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4972063/10000000) (δ := 1203/125000000) (ψ := 859139/1000000) 191 164
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t219 : ((-13717819269/500000000000 : ℚ) : ℝ) ≤ stT191 219 := by
  have hc : ((-40601/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13717819269/500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-40601/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c220 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((218441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -699167/2500000) (δ := 9679/1000000000) (ψ := 859139/1000000) 191 164
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t220 : ((9203490549/312500000000 : ℚ) : ℝ) ≤ stT191 220 := by
  have hc : ((13651/31250 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9203490549/312500000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((13651/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c221 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((193661/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63111/1000000) (δ := 9679/1000000000) (ψ := 859139/1000000) 191 164
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t221 : ((4070737671/62500000000 : ℚ) : ℝ) ≤ stT191 221 := by
  have hc : ((193651/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4070737671/62500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((193651/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c222 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((819737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1524611/10000000) (δ := 1203/125000000) (ψ := 859139/1000000) 191 164
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t222 : ((137534462043/2500000000000 : ℚ) : ℝ) ≤ stT191 222 := by
  have hc : ((819687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137534462043/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((819687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c223 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((51171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3670687/10000000) (δ := 1203/125000000) (ψ := 859139/1000000) 191 164
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t223 : ((17124933877/2500000000000 : ℚ) : ℝ) ≤ stT191 223 := by
  have hc : ((25573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17124933877/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((25573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c224 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-42697/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1161433/2000000) (δ := 2431/250000000) (ψ := 859139/1000000) 191 164
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t224 : ((-114121037277/2500000000000 : ℚ) : ℝ) ≤ stT191 224 := by
  have hc : ((-341601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114121037277/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-341601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c225 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-499743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3886911/5000000) (δ := 9617/1000000000) (ψ := 859139/1000000) 191 165
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t225 : ((-41647354157/625000000000 : ℚ) : ℝ) ≤ stT191 225 := by
  have hc : ((-62471/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41647354157/625000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-62471/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c226 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-637873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414081/2500000) (δ := 9593/500000000) (ψ := 859139/1000000) 191 165
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t226 : ((-424340638293/10000000000000 : ℚ) : ℝ) ≤ stT191 226 := by
  have hc : ((-637923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424340638293/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-637923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c227 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((75481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1774069/5000000) (δ := 9617/1000000000) (ψ := 859139/1000000) 191 165
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t227 : ((782529417/78125000000 : ℚ) : ℝ) ≤ stT191 227 := by
  have hc : ((2358/15625 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((782529417/78125000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((2358/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c228 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((836629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1449239/10000000) (δ := 9617/1000000000) (ψ := 859139/1000000) 191 165
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t228 : ((277018914007/5000000000000 : ℚ) : ℝ) ≤ stT191 228 := by
  have hc : ((836579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277018914007/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((836579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c229 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((967361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160123/2500000) (δ := 9617/1000000000) (ψ := 859139/1000000) 191 165
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t229 : ((319608260199/5000000000000 : ℚ) : ℝ) ≤ stT191 229 := by
  have hc : ((967311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319608260199/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((967311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c230 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((463867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2721103/10000000) (δ := 4793/500000000) (ψ := 859139/1000000) 191 165
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t230 : ((15291582673/500000000000 : ℚ) : ℝ) ≤ stT191 230 := by
  have hc : ((463817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15291582673/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((463817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c231 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-1697/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4792689/10000000) (δ := 4793/500000000) (ψ := 859139/1000000) 191 165
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t231 : ((-139588629/6250000000 : ℚ) : ℝ) ≤ stT191 231 := by
  have hc : ((-6789/20000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139588629/6250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-6789/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c232 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-460633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3427649/5000000) (δ := 4793/500000000) (ψ := 859139/1000000) 191 165
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t232 : ((-151218589357/2500000000000 : ℚ) : ℝ) ≤ stT191 232 := by
  have hc : ((-230329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151218589357/2500000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-230329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c233 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-912257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -679889/1000000) (δ := 9593/1000000000) (ψ := 859139/1000000) 191 166
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t233 : ((-298836193227/5000000000000 : ℚ) : ℝ) ≤ stT191 233 := by
  have hc : ((-912307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298836193227/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-912307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c234 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-162383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4753901/10000000) (δ := 961/100000000) (ψ := 859139/1000000) 191 166
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t234 : ((-13271190021/625000000000 : ℚ) : ℝ) ≤ stT191 234 := by
  have hc : ((-20301/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13271190021/625000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-20301/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c235 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((46509/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54353/200000) (δ := 961/100000000) (ψ := 859139/1000000) 191 166
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t235 : ((473997833/15625000000 : ℚ) : ℝ) ≤ stT191 235 := by
  have hc : ((5813/12500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((473997833/15625000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((5813/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c236 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((962149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345021/5000000) (δ := 971/100000000) (ψ := 859139/1000000) 191 166
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t236 : ((9785508929/156250000000 : ℚ) : ℝ) ≤ stT191 236 := by
  have hc : ((962099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9785508929/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((962099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c237 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((862003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332243/2500000) (δ := 9693/1000000000) (ψ := 859139/1000000) 191 166
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t237 : ((559897948257/10000000000000 : ℚ) : ℝ) ≤ stT191 237 := by
  have hc : ((861953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((559897948257/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((861953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c238 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((46569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 667897/2000000) (δ := 971/100000000) (ψ := 859139/1000000) 191 166
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t238 : ((30179683477/2000000000000 : ℚ) : ℝ) ≤ stT191 238 := by
  have hc : ((46559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30179683477/2000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((46559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c239 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-268063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1068319/2000000) (δ := 961/100000000) (ψ := 859139/1000000) 191 166
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t239 : ((-21676489817/625000000000 : ℚ) : ℝ) ≤ stT191 239 := by
  have hc : ((-33511/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21676489817/625000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-33511/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c240 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-978559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7335349/10000000) (δ := 9693/1000000000) (ψ := 859139/1000000) 191 166
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t240 : ((-315845076141/5000000000000 : ℚ) : ℝ) ≤ stT191 240 := by
  have hc : ((-978609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315845076141/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-978609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c241 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-416379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -638717/1000000) (δ := 9703/1000000000) (ψ := 859139/1000000) 191 167
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t241 : ((-67057387857/1250000000000 : ℚ) : ℝ) ≤ stT191 241 := by
  have hc : ((-104101/125000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67057387857/1250000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-104101/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c242 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-9599/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2204969/5000000) (δ := 9703/1000000000) (ψ := 859139/1000000) 191 167
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t242 : ((-493766739/40000000000 : ℚ) : ℝ) ≤ stT191 242 := by
  have hc : ((-19203/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-493766739/40000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-19203/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c243 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((560051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2440871/10000000) (δ := 9603/1000000000) (ψ := 859139/1000000) 191 167
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t243 : ((718481283/20000000000 : ℚ) : ℝ) ≤ stT191 243 := by
  have hc : ((560001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718481283/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((560001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c244 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((490817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239937/5000000) (δ := 9603/1000000000) (ψ := 859139/1000000) 191 167
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t244 : ((4909331027/78125000000 : ℚ) : ℝ) ≤ stT191 244 := by
  have hc : ((61349/62500 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4909331027/78125000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((61349/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c245 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((103921/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473077/10000000) (δ := 19203/1000000000) (ψ := 859139/1000000) 191 167
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t245 : ((66388639821/1250000000000 : ℚ) : ℝ) ≤ stT191 245 := by
  have hc : ((415659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66388639821/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((415659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c246 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((202153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1709051/5000000) (δ := 3/312500) (ψ := 859139/1000000) 191 167
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t246 : ((16107002791/1250000000000 : ℚ) : ℝ) ≤ stT191 246 := by
  have hc : ((202103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16107002791/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((202103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c247 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-6759/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 669403/1250000) (δ := 3/312500) (ψ := 859139/1000000) 191 167
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t247 : ((-6881676789/200000000000 : ℚ) : ℝ) ≤ stT191 247 := by
  have hc : ((-54077/100000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6881676789/200000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-54077/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c248 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-974169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1456903/2000000) (δ := 3/312500) (ψ := 859139/1000000) 191 167
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t248 : ((-618630039219/10000000000000 : ℚ) : ℝ) ≤ stT191 248 := by
  have hc : ((-974219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618630039219/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-974219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c249 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-857289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6501941/10000000) (δ := 1939/200000000) (ψ := 859139/1000000) 191 168
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t249 : ((-21732686311/400000000000 : ℚ) : ℝ) ≤ stT191 249 := by
  have hc : ((-857339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21732686311/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-857339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_c250 :
    |Real.cos (((191 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-130681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4588073/10000000) (δ := 1919/200000000) (ψ := 859139/1000000) 191 168
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st191_t250 : ((-5166612121/312500000000 : ℚ) : ℝ) ≤ stT191 250 := by
  have hc : ((-65353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((191 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st191_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5166612121/312500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-65353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st191_p1 : ((8163/12500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT191 (i+1) := by
  rw [Finset.sum_range_one]
  exact st191_t1

theorem st191_p2 : ((13001112198499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT191 (i+1))
      = (∑ i ∈ Finset.range 1, stT191 (i+1)) + stT191 2 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 1
    simpa using h
  have hprev := st191_p1
  have hstep := st191_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p3 : ((1265526204829/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT191 (i+1))
      = (∑ i ∈ Finset.range 2, stT191 (i+1)) + stT191 3 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 2
    simpa using h
  have hprev := st191_p2
  have hstep := st191_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p4 : ((1765286704829/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT191 (i+1))
      = (∑ i ∈ Finset.range 3, stT191 (i+1)) + stT191 4 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 3
    simpa using h
  have hprev := st191_p3
  have hstep := st191_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p5 : ((3741594677341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT191 (i+1))
      = (∑ i ∈ Finset.range 4, stT191 (i+1)) + stT191 5 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 4
    simpa using h
  have hprev := st191_p4
  have hstep := st191_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p6 : ((8367901708291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT191 (i+1))
      = (∑ i ∈ Finset.range 5, stT191 (i+1)) + stT191 6 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 5
    simpa using h
  have hprev := st191_p5
  have hstep := st191_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p7 : ((10247851278163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT191 (i+1))
      = (∑ i ∈ Finset.range 6, stT191 (i+1)) + stT191 7 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 6
    simpa using h
  have hprev := st191_p6
  have hstep := st191_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p8 : ((23642033477087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT191 (i+1))
      = (∑ i ∈ Finset.range 7, stT191 (i+1)) + stT191 8 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 7
    simpa using h
  have hprev := st191_p7
  have hstep := st191_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p9 : ((4356431287689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT191 (i+1))
      = (∑ i ∈ Finset.range 8, stT191 (i+1)) + stT191 9 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 8
    simpa using h
  have hprev := st191_p8
  have hstep := st191_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p10 : ((1486024146577/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT191 (i+1))
      = (∑ i ∈ Finset.range 9, stT191 (i+1)) + stT191 10 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 9
    simpa using h
  have hprev := st191_p9
  have hstep := st191_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p11 : ((2986017311683/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT191 (i+1))
      = (∑ i ∈ Finset.range 10, stT191 (i+1)) + stT191 11 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 10
    simpa using h
  have hprev := st191_p10
  have hstep := st191_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p12 : ((538566528843/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT191 (i+1))
      = (∑ i ∈ Finset.range 11, stT191 (i+1)) + stT191 12 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 11
    simpa using h
  have hprev := st191_p11
  have hstep := st191_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p13 : ((143381866767/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT191 (i+1))
      = (∑ i ∈ Finset.range 12, stT191 (i+1)) + stT191 13 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 12
    simpa using h
  have hprev := st191_p12
  have hstep := st191_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p14 : ((6306253502819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT191 (i+1))
      = (∑ i ∈ Finset.range 13, stT191 (i+1)) + stT191 14 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 13
    simpa using h
  have hprev := st191_p13
  have hstep := st191_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p15 : ((102587691577/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT191 (i+1))
      = (∑ i ∈ Finset.range 14, stT191 (i+1)) + stT191 15 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 14
    simpa using h
  have hprev := st191_p14
  have hstep := st191_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p16 : ((434083656933/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT191 (i+1))
      = (∑ i ∈ Finset.range 15, stT191 (i+1)) + stT191 16 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 15
    simpa using h
  have hprev := st191_p15
  have hstep := st191_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p17 : ((75501907677/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT191 (i+1))
      = (∑ i ∈ Finset.range 16, stT191 (i+1)) + stT191 17 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 16
    simpa using h
  have hprev := st191_p16
  have hstep := st191_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p18 : ((29853905923143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT191 (i+1))
      = (∑ i ∈ Finset.range 17, stT191 (i+1)) + stT191 18 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 17
    simpa using h
  have hprev := st191_p17
  have hstep := st191_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p19 : ((28282614167363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT191 (i+1))
      = (∑ i ∈ Finset.range 18, stT191 (i+1)) + stT191 19 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 18
    simpa using h
  have hprev := st191_p18
  have hstep := st191_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p20 : ((15150811953803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT191 (i+1))
      = (∑ i ∈ Finset.range 19, stT191 (i+1)) + stT191 20 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 19
    simpa using h
  have hprev := st191_p19
  have hstep := st191_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p21 : ((5688228783593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT191 (i+1))
      = (∑ i ∈ Finset.range 20, stT191 (i+1)) + stT191 21 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 20
    simpa using h
  have hprev := st191_p20
  have hstep := st191_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p22 : ((14714049497213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT191 (i+1))
      = (∑ i ∈ Finset.range 21, stT191 (i+1)) + stT191 22 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 21
    simpa using h
  have hprev := st191_p21
  have hstep := st191_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p23 : ((15170423921921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT191 (i+1))
      = (∑ i ∈ Finset.range 22, stT191 (i+1)) + stT191 23 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 22
    simpa using h
  have hprev := st191_p22
  have hstep := st191_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p24 : ((14165920568753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT191 (i+1))
      = (∑ i ∈ Finset.range 23, stT191 (i+1)) + stT191 24 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 23
    simpa using h
  have hprev := st191_p23
  have hstep := st191_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p25 : ((6966409226101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT191 (i+1))
      = (∑ i ∈ Finset.range 24, stT191 (i+1)) + stT191 25 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 24
    simpa using h
  have hprev := st191_p24
  have hstep := st191_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p26 : ((29486318782033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT191 (i+1))
      = (∑ i ∈ Finset.range 25, stT191 (i+1)) + stT191 26 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 25
    simpa using h
  have hprev := st191_p25
  have hstep := st191_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p27 : ((31308639379033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT191 (i+1))
      = (∑ i ∈ Finset.range 26, stT191 (i+1)) + stT191 27 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 26
    simpa using h
  have hprev := st191_p26
  have hstep := st191_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p28 : ((1293805321719/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT191 (i+1))
      = (∑ i ∈ Finset.range 27, stT191 (i+1)) + stT191 28 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 27
    simpa using h
  have hprev := st191_p27
  have hstep := st191_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p29 : ((6528664511143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT191 (i+1))
      = (∑ i ∈ Finset.range 28, stT191 (i+1)) + stT191 29 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 28
    simpa using h
  have hprev := st191_p28
  have hstep := st191_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p30 : ((32587241238701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT191 (i+1))
      = (∑ i ∈ Finset.range 29, stT191 (i+1)) + stT191 30 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 29
    simpa using h
  have hprev := st191_p29
  have hstep := st191_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p31 : ((32568549704723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT191 (i+1))
      = (∑ i ∈ Finset.range 30, stT191 (i+1)) + stT191 31 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 30
    simpa using h
  have hprev := st191_p30
  have hstep := st191_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p32 : ((6586988084283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT191 (i+1))
      = (∑ i ∈ Finset.range 31, stT191 (i+1)) + stT191 32 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 31
    simpa using h
  have hprev := st191_p31
  have hstep := st191_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p33 : ((33938691011551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT191 (i+1))
      = (∑ i ∈ Finset.range 32, stT191 (i+1)) + stT191 33 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 32
    simpa using h
  have hprev := st191_p32
  have hstep := st191_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p34 : ((17767237989563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT191 (i+1))
      = (∑ i ∈ Finset.range 33, stT191 (i+1)) + stT191 34 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 33
    simpa using h
  have hprev := st191_p33
  have hstep := st191_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p35 : ((18554642616743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT191 (i+1))
      = (∑ i ∈ Finset.range 34, stT191 (i+1)) + stT191 35 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 34
    simpa using h
  have hprev := st191_p34
  have hstep := st191_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p36 : ((18798142519343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT191 (i+1))
      = (∑ i ∈ Finset.range 35, stT191 (i+1)) + stT191 36 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 35
    simpa using h
  have hprev := st191_p35
  have hstep := st191_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p37 : ((9117878689099/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT191 (i+1))
      = (∑ i ∈ Finset.range 36, stT191 (i+1)) + stT191 37 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 36
    simpa using h
  have hprev := st191_p36
  have hstep := st191_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p38 : ((17480134497843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT191 (i+1))
      = (∑ i ∈ Finset.range 37, stT191 (i+1)) + stT191 38 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 37
    simpa using h
  have hprev := st191_p37
  have hstep := st191_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p39 : ((35157013588313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT191 (i+1))
      = (∑ i ∈ Finset.range 38, stT191 (i+1)) + stT191 39 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 38
    simpa using h
  have hprev := st191_p38
  have hstep := st191_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p40 : ((36738072531413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT191 (i+1))
      = (∑ i ∈ Finset.range 39, stT191 (i+1)) + stT191 40 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 39
    simpa using h
  have hprev := st191_p39
  have hstep := st191_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p41 : ((18372104298043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT191 (i+1))
      = (∑ i ∈ Finset.range 40, stT191 (i+1)) + stT191 41 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 40
    simpa using h
  have hprev := st191_p40
  have hstep := st191_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p42 : ((17604859959189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT191 (i+1))
      = (∑ i ∈ Finset.range 41, stT191 (i+1)) + stT191 42 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 41
    simpa using h
  have hprev := st191_p41
  have hstep := st191_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p43 : ((35694895421113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT191 (i+1))
      = (∑ i ∈ Finset.range 42, stT191 (i+1)) + stT191 43 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 42
    simpa using h
  have hprev := st191_p42
  have hstep := st191_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p44 : ((36899303015297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT191 (i+1))
      = (∑ i ∈ Finset.range 43, stT191 (i+1)) + stT191 44 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 43
    simpa using h
  have hprev := st191_p43
  have hstep := st191_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p45 : ((35594946413129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT191 (i+1))
      = (∑ i ∈ Finset.range 44, stT191 (i+1)) + stT191 45 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 44
    simpa using h
  have hprev := st191_p44
  have hstep := st191_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p46 : ((17804021838553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT191 (i+1))
      = (∑ i ∈ Finset.range 45, stT191 (i+1)) + stT191 46 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 45
    simpa using h
  have hprev := st191_p45
  have hstep := st191_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p47 : ((18400259203793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT191 (i+1))
      = (∑ i ∈ Finset.range 46, stT191 (i+1)) + stT191 47 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 46
    simpa using h
  have hprev := st191_p46
  have hstep := st191_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p48 : ((17703914721289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT191 (i+1))
      = (∑ i ∈ Finset.range 47, stT191 (i+1)) + stT191 48 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 47
    simpa using h
  have hprev := st191_p47
  have hstep := st191_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p49 : ((4512853297117/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT191 (i+1))
      = (∑ i ∈ Finset.range 48, stT191 (i+1)) + stT191 49 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 48
    simpa using h
  have hprev := st191_p48
  have hstep := st191_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p50 : ((4549523840207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT191 (i+1))
      = (∑ i ∈ Finset.range 49, stT191 (i+1)) + stT191 50 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 49
    simpa using h
  have hprev := st191_p49
  have hstep := st191_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p51 : ((8836095912829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT191 (i+1))
      = (∑ i ∈ Finset.range 50, stT191 (i+1)) + stT191 51 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 50
    simpa using h
  have hprev := st191_p50
  have hstep := st191_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p52 : ((18357345478283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT191 (i+1))
      = (∑ i ∈ Finset.range 51, stT191 (i+1)) + stT191 52 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 51
    simpa using h
  have hprev := st191_p51
  have hstep := st191_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p53 : ((4427616755869/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT191 (i+1))
      = (∑ i ∈ Finset.range 52, stT191 (i+1)) + stT191 53 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 52
    simpa using h
  have hprev := st191_p52
  have hstep := st191_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p54 : ((36396498675809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT191 (i+1))
      = (∑ i ∈ Finset.range 53, stT191 (i+1)) + stT191 54 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 53
    simpa using h
  have hprev := st191_p53
  have hstep := st191_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p55 : ((35826589325409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT191 (i+1))
      = (∑ i ∈ Finset.range 54, stT191 (i+1)) + stT191 55 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 54
    simpa using h
  have hprev := st191_p54
  have hstep := st191_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p56 : ((36008199992339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT191 (i+1))
      = (∑ i ∈ Finset.range 55, stT191 (i+1)) + stT191 56 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 55
    simpa using h
  have hprev := st191_p55
  have hstep := st191_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p57 : ((289150900267/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT191 (i+1))
      = (∑ i ∈ Finset.range 56, stT191 (i+1)) + stT191 57 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 56
    simpa using h
  have hprev := st191_p56
  have hstep := st191_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p58 : ((7155454633657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT191 (i+1))
      = (∑ i ∈ Finset.range 57, stT191 (i+1)) + stT191 58 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 57
    simpa using h
  have hprev := st191_p57
  have hstep := st191_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p59 : ((18145885293931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT191 (i+1))
      = (∑ i ∈ Finset.range 58, stT191 (i+1)) + stT191 59 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 58
    simpa using h
  have hprev := st191_p58
  have hstep := st191_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p60 : ((17850701869171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT191 (i+1))
      = (∑ i ∈ Finset.range 59, stT191 (i+1)) + stT191 60 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 59
    simpa using h
  have hprev := st191_p59
  have hstep := st191_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p61 : ((18152182439923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT191 (i+1))
      = (∑ i ∈ Finset.range 60, stT191 (i+1)) + stT191 61 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 60
    simpa using h
  have hprev := st191_p60
  have hstep := st191_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p62 : ((4468335358951/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT191 (i+1))
      = (∑ i ∈ Finset.range 61, stT191 (i+1)) + stT191 62 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 61
    simpa using h
  have hprev := st191_p61
  have hstep := st191_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p63 : ((9050272927791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT191 (i+1))
      = (∑ i ∈ Finset.range 62, stT191 (i+1)) + stT191 63 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 62
    simpa using h
  have hprev := st191_p62
  have hstep := st191_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p64 : ((35909515227903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT191 (i+1))
      = (∑ i ∈ Finset.range 63, stT191 (i+1)) + stT191 64 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 63
    simpa using h
  have hprev := st191_p63
  have hstep := st191_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p65 : ((35977746716373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT191 (i+1))
      = (∑ i ∈ Finset.range 64, stT191 (i+1)) + stT191 65 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 64
    simpa using h
  have hprev := st191_p64
  have hstep := st191_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p66 : ((7237286682821/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT191 (i+1))
      = (∑ i ∈ Finset.range 65, stT191 (i+1)) + stT191 66 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 65
    simpa using h
  have hprev := st191_p65
  have hstep := st191_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p67 : ((3566626378209/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT191 (i+1))
      = (∑ i ∈ Finset.range 66, stT191 (i+1)) + stT191 67 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 66
    simpa using h
  have hprev := st191_p66
  have hstep := st191_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p68 : ((4561787010663/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT191 (i+1))
      = (∑ i ∈ Finset.range 67, stT191 (i+1)) + stT191 68 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 67
    simpa using h
  have hprev := st191_p67
  have hstep := st191_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p69 : ((8854671648073/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT191 (i+1))
      = (∑ i ∈ Finset.range 68, stT191 (i+1)) + stT191 69 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 68
    simpa using h
  have hprev := st191_p68
  have hstep := st191_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p70 : ((4576338773253/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT191 (i+1))
      = (∑ i ∈ Finset.range 69, stT191 (i+1)) + stT191 70 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 69
    simpa using h
  have hprev := st191_p69
  have hstep := st191_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p71 : ((17749927469019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT191 (i+1))
      = (∑ i ∈ Finset.range 70, stT191 (i+1)) + stT191 71 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 70
    simpa using h
  have hprev := st191_p70
  have hstep := st191_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p72 : ((4536893689521/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT191 (i+1))
      = (∑ i ∈ Finset.range 71, stT191 (i+1)) + stT191 72 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 71
    simpa using h
  have hprev := st191_p71
  have hstep := st191_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p73 : ((9006003845871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT191 (i+1))
      = (∑ i ∈ Finset.range 72, stT191 (i+1)) + stT191 73 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 72
    simpa using h
  have hprev := st191_p72
  have hstep := st191_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p74 : ((4458778391663/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT191 (i+1))
      = (∑ i ∈ Finset.range 73, stT191 (i+1)) + stT191 74 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 73
    simpa using h
  have hprev := st191_p73
  have hstep := st191_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p75 : ((2285328204319/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT191 (i+1))
      = (∑ i ∈ Finset.range 74, stT191 (i+1)) + stT191 75 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 74
    simpa using h
  have hprev := st191_p74
  have hstep := st191_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p76 : ((35421091585159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT191 (i+1))
      = (∑ i ∈ Finset.range 75, stT191 (i+1)) + stT191 76 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 75
    simpa using h
  have hprev := st191_p75
  have hstep := st191_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p77 : ((18189384451677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT191 (i+1))
      = (∑ i ∈ Finset.range 76, stT191 (i+1)) + stT191 77 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 76
    simpa using h
  have hprev := st191_p76
  have hstep := st191_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p78 : ((18010733628837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT191 (i+1))
      = (∑ i ∈ Finset.range 77, stT191 (i+1)) + stT191 78 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 77
    simpa using h
  have hprev := st191_p77
  have hstep := st191_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p79 : ((3559632125441/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT191 (i+1))
      = (∑ i ∈ Finset.range 78, stT191 (i+1)) + stT191 79 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 78
    simpa using h
  have hprev := st191_p78
  have hstep := st191_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p80 : ((3660574852879/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT191 (i+1))
      = (∑ i ∈ Finset.range 79, stT191 (i+1)) + stT191 80 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 79
    simpa using h
  have hprev := st191_p79
  have hstep := st191_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p81 : ((17776300509803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT191 (i+1))
      = (∑ i ∈ Finset.range 80, stT191 (i+1)) + stT191 81 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 80
    simpa using h
  have hprev := st191_p80
  have hstep := st191_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p82 : ((18015548145923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT191 (i+1))
      = (∑ i ∈ Finset.range 81, stT191 (i+1)) + stT191 82 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 81
    simpa using h
  have hprev := st191_p81
  have hstep := st191_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p83 : ((18218172859123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT191 (i+1))
      = (∑ i ∈ Finset.range 82, stT191 (i+1)) + stT191 83 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 82
    simpa using h
  have hprev := st191_p82
  have hstep := st191_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p84 : ((17703548258633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT191 (i+1))
      = (∑ i ∈ Finset.range 83, stT191 (i+1)) + stT191 84 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 83
    simpa using h
  have hprev := st191_p83
  have hstep := st191_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p85 : ((18167905676591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT191 (i+1))
      = (∑ i ∈ Finset.range 84, stT191 (i+1)) + stT191 85 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 84
    simpa using h
  have hprev := st191_p84
  have hstep := st191_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p86 : ((18103134826943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT191 (i+1))
      = (∑ i ∈ Finset.range 85, stT191 (i+1)) + stT191 86 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 85
    simpa using h
  have hprev := st191_p85
  have hstep := st191_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p87 : ((35427419227567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT191 (i+1))
      = (∑ i ∈ Finset.range 86, stT191 (i+1)) + stT191 87 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 86
    simpa using h
  have hprev := st191_p86
  have hstep := st191_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p88 : ((18235953544509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT191 (i+1))
      = (∑ i ∈ Finset.range 87, stT191 (i+1)) + stT191 88 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 87
    simpa using h
  have hprev := st191_p87
  have hstep := st191_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p89 : ((18036190561421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT191 (i+1))
      = (∑ i ∈ Finset.range 88, stT191 (i+1)) + stT191 89 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 88
    simpa using h
  have hprev := st191_p88
  have hstep := st191_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p90 : ((1418357266949/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT191 (i+1))
      = (∑ i ∈ Finset.range 89, stT191 (i+1)) + stT191 90 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 89
    simpa using h
  have hprev := st191_p89
  have hstep := st191_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p91 : ((36503695536053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT191 (i+1))
      = (∑ i ∈ Finset.range 90, stT191 (i+1)) + stT191 91 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 90
    simpa using h
  have hprev := st191_p90
  have hstep := st191_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p92 : ((36064017480201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT191 (i+1))
      = (∑ i ∈ Finset.range 91, stT191 (i+1)) + stT191 92 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 91
    simpa using h
  have hprev := st191_p91
  have hstep := st191_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p93 : ((35443521994633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT191 (i+1))
      = (∑ i ∈ Finset.range 92, stT191 (i+1)) + stT191 93 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 92
    simpa using h
  have hprev := st191_p92
  have hstep := st191_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p94 : ((36460125600547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT191 (i+1))
      = (∑ i ∈ Finset.range 93, stT191 (i+1)) + stT191 94 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 93
    simpa using h
  have hprev := st191_p93
  have hstep := st191_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p95 : ((7235116527329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT191 (i+1))
      = (∑ i ∈ Finset.range 94, stT191 (i+1)) + stT191 95 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 94
    simpa using h
  have hprev := st191_p94
  have hstep := st191_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p96 : ((35401660021039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT191 (i+1))
      = (∑ i ∈ Finset.range 95, stT191 (i+1)) + stT191 96 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 95
    simpa using h
  have hprev := st191_p95
  have hstep := st191_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p97 : ((36314942425773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT191 (i+1))
      = (∑ i ∈ Finset.range 96, stT191 (i+1)) + stT191 97 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 96
    simpa using h
  have hprev := st191_p96
  have hstep := st191_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p98 : ((7275881257161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT191 (i+1))
      = (∑ i ∈ Finset.range 97, stT191 (i+1)) + stT191 98 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 97
    simpa using h
  have hprev := st191_p97
  have hstep := st191_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p99 : ((35420523650917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT191 (i+1))
      = (∑ i ∈ Finset.range 98, stT191 (i+1)) + stT191 99 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 98
    simpa using h
  have hprev := st191_p98
  have hstep := st191_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p100 : ((18014107021613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT191 (i+1))
      = (∑ i ∈ Finset.range 99, stT191 (i+1)) + stT191 100 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 99
    simpa using h
  have hprev := st191_p99
  have hstep := st191_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p101 : ((571562311417/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT191 (i+1))
      = (∑ i ∈ Finset.range 100, stT191 (i+1)) + stT191 101 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 100
    simpa using h
  have hprev := st191_p100
  have hstep := st191_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p102 : ((278339822183/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT191 (i+1))
      = (∑ i ∈ Finset.range 101, stT191 (i+1)) + stT191 102 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 101
    simpa using h
  have hprev := st191_p101
  have hstep := st191_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p103 : ((8910743696839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT191 (i+1))
      = (∑ i ∈ Finset.range 102, stT191 (i+1)) + stT191 103 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 102
    simpa using h
  have hprev := st191_p102
  have hstep := st191_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p104 : ((9145613199019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT191 (i+1))
      = (∑ i ∈ Finset.range 103, stT191 (i+1)) + stT191 104 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 103
    simpa using h
  have hprev := st191_p103
  have hstep := st191_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p105 : ((9018627009097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT191 (i+1))
      = (∑ i ∈ Finset.range 104, stT191 (i+1)) + stT191 105 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 104
    simpa using h
  have hprev := st191_p104
  have hstep := st191_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p106 : ((8847189202381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT191 (i+1))
      = (∑ i ∈ Finset.range 105, stT191 (i+1)) + stT191 106 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 105
    simpa using h
  have hprev := st191_p105
  have hstep := st191_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p107 : ((9051798393413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT191 (i+1))
      = (∑ i ∈ Finset.range 106, stT191 (i+1)) + stT191 107 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 106
    simpa using h
  have hprev := st191_p106
  have hstep := st191_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p108 : ((18270888279451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT191 (i+1))
      = (∑ i ∈ Finset.range 107, stT191 (i+1)) + stT191 108 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 107
    simpa using h
  have hprev := st191_p107
  have hstep := st191_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p109 : ((35597005698739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT191 (i+1))
      = (∑ i ∈ Finset.range 108, stT191 (i+1)) + stT191 109 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 108
    simpa using h
  have hprev := st191_p108
  have hstep := st191_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p110 : ((35604495142749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT191 (i+1))
      = (∑ i ∈ Finset.range 109, stT191 (i+1)) + stT191 110 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 109
    simpa using h
  have hprev := st191_p109
  have hstep := st191_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p111 : ((456757669663/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT191 (i+1))
      = (∑ i ∈ Finset.range 110, stT191 (i+1)) + stT191 111 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 110
    simpa using h
  have hprev := st191_p110
  have hstep := st191_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p112 : ((1132945355533/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT191 (i+1))
      = (∑ i ∈ Finset.range 111, stT191 (i+1)) + stT191 112 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 111
    simpa using h
  have hprev := st191_p111
  have hstep := st191_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p113 : ((4425129060199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT191 (i+1))
      = (∑ i ∈ Finset.range 112, stT191 (i+1)) + stT191 113 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 112
    simpa using h
  have hprev := st191_p112
  have hstep := st191_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p114 : ((8972007614303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT191 (i+1))
      = (∑ i ∈ Finset.range 113, stT191 (i+1)) + stT191 114 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 113
    simpa using h
  have hprev := st191_p113
  have hstep := st191_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p115 : ((9158396513823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT191 (i+1))
      = (∑ i ∈ Finset.range 114, stT191 (i+1)) + stT191 115 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 114
    simpa using h
  have hprev := st191_p114
  have hstep := st191_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p116 : ((36016376327157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT191 (i+1))
      = (∑ i ∈ Finset.range 115, stT191 (i+1)) + stT191 116 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 115
    simpa using h
  have hprev := st191_p115
  have hstep := st191_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p117 : ((353694502809/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT191 (i+1))
      = (∑ i ∈ Finset.range 116, stT191 (i+1)) + stT191 117 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 116
    simpa using h
  have hprev := st191_p116
  have hstep := st191_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p118 : ((18030675468789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT191 (i+1))
      = (∑ i ∈ Finset.range 117, stT191 (i+1)) + stT191 118 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 117
    simpa using h
  have hprev := st191_p117
  have hstep := st191_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p119 : ((9159291633999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT191 (i+1))
      = (∑ i ∈ Finset.range 118, stT191 (i+1)) + stT191 119 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 118
    simpa using h
  have hprev := st191_p118
  have hstep := st191_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p120 : ((17955663186109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT191 (i+1))
      = (∑ i ∈ Finset.range 119, stT191 (i+1)) + stT191 120 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 119
    simpa using h
  have hprev := st191_p119
  have hstep := st191_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p121 : ((17685135886329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT191 (i+1))
      = (∑ i ∈ Finset.range 120, stT191 (i+1)) + stT191 121 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 120
    simpa using h
  have hprev := st191_p120
  have hstep := st191_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p122 : ((36098473041683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT191 (i+1))
      = (∑ i ∈ Finset.range 121, stT191 (i+1)) + stT191 122 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 121
    simpa using h
  have hprev := st191_p121
  have hstep := st191_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p123 : ((18321255180603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT191 (i+1))
      = (∑ i ∈ Finset.range 122, stT191 (i+1)) + stT191 123 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 122
    simpa using h
  have hprev := st191_p122
  have hstep := st191_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p124 : ((8984923668603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT191 (i+1))
      = (∑ i ∈ Finset.range 123, stT191 (i+1)) + stT191 124 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 123
    simpa using h
  have hprev := st191_p123
  have hstep := st191_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p125 : ((1767877184431/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT191 (i+1))
      = (∑ i ∈ Finset.range 124, stT191 (i+1)) + stT191 125 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 124
    simpa using h
  have hprev := st191_p124
  have hstep := st191_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p126 : ((1800237502659/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT191 (i+1))
      = (∑ i ∈ Finset.range 125, stT191 (i+1)) + stT191 126 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 125
    simpa using h
  have hprev := st191_p125
  have hstep := st191_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p127 : ((4581569095669/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT191 (i+1))
      = (∑ i ∈ Finset.range 126, stT191 (i+1)) + stT191 127 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 126
    simpa using h
  have hprev := st191_p126
  have hstep := st191_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p128 : ((1128031300603/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT191 (i+1))
      = (∑ i ∈ Finset.range 127, stT191 (i+1)) + stT191 128 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 127
    simpa using h
  have hprev := st191_p127
  have hstep := st191_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p129 : ((35367915113863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT191 (i+1))
      = (∑ i ∈ Finset.range 128, stT191 (i+1)) + stT191 129 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 128
    simpa using h
  have hprev := st191_p128
  have hstep := st191_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p130 : ((35787825926639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT191 (i+1))
      = (∑ i ∈ Finset.range 129, stT191 (i+1)) + stT191 130 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 129
    simpa using h
  have hprev := st191_p129
  have hstep := st191_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p131 : ((36595169486727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT191 (i+1))
      = (∑ i ∈ Finset.range 130, stT191 (i+1)) + stT191 131 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 130
    simpa using h
  have hprev := st191_p130
  have hstep := st191_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p132 : ((3635977017051/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT191 (i+1))
      = (∑ i ∈ Finset.range 131, stT191 (i+1)) + stT191 132 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 131
    simpa using h
  have hprev := st191_p131
  have hstep := st191_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p133 : ((3550165730387/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT191 (i+1))
      = (∑ i ∈ Finset.range 132, stT191 (i+1)) + stT191 133 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 132
    simpa using h
  have hprev := st191_p132
  have hstep := st191_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p134 : ((17752728297667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT191 (i+1))
      = (∑ i ∈ Finset.range 133, stT191 (i+1)) + stT191 134 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 133
    simpa using h
  have hprev := st191_p133
  have hstep := st191_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p135 : ((1136152642273/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT191 (i+1))
      = (∑ i ∈ Finset.range 134, stT191 (i+1)) + stT191 135 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 134
    simpa using h
  have hprev := st191_p134
  have hstep := st191_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p136 : ((4577044989619/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT191 (i+1))
      = (∑ i ∈ Finset.range 135, stT191 (i+1)) + stT191 136 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 135
    simpa using h
  have hprev := st191_p135
  have hstep := st191_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p137 : ((17929052188291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT191 (i+1))
      = (∑ i ∈ Finset.range 136, stT191 (i+1)) + stT191 137 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 136
    simpa using h
  have hprev := st191_p136
  have hstep := st191_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p138 : ((35335676889341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT191 (i+1))
      = (∑ i ∈ Finset.range 137, stT191 (i+1)) + stT191 138 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 137
    simpa using h
  have hprev := st191_p137
  have hstep := st191_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p139 : ((35893886375901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT191 (i+1))
      = (∑ i ∈ Finset.range 138, stT191 (i+1)) + stT191 139 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 138
    simpa using h
  have hprev := st191_p138
  have hstep := st191_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p140 : ((36628636218573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT191 (i+1))
      = (∑ i ∈ Finset.range 139, stT191 (i+1)) + stT191 140 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 139
    simpa using h
  have hprev := st191_p139
  have hstep := st191_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p141 : ((36375380058373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT191 (i+1))
      = (∑ i ∈ Finset.range 140, stT191 (i+1)) + stT191 141 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 140
    simpa using h
  have hprev := st191_p140
  have hstep := st191_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p142 : ((35539146104739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT191 (i+1))
      = (∑ i ∈ Finset.range 141, stT191 (i+1)) + stT191 142 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 141
    simpa using h
  have hprev := st191_p141
  have hstep := st191_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p143 : ((7083489866687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT191 (i+1))
      = (∑ i ∈ Finset.range 142, stT191 (i+1)) + stT191 143 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 142
    simpa using h
  have hprev := st191_p142
  have hstep := st191_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p144 : ((36189492357951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT191 (i+1))
      = (∑ i ∈ Finset.range 143, stT191 (i+1)) + stT191 144 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 143
    simpa using h
  have hprev := st191_p143
  have hstep := st191_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p145 : ((36681904244073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT191 (i+1))
      = (∑ i ∈ Finset.range 144, stT191 (i+1)) + stT191 145 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 144
    simpa using h
  have hprev := st191_p144
  have hstep := st191_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p146 : ((36162788380573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT191 (i+1))
      = (∑ i ∈ Finset.range 145, stT191 (i+1)) + stT191 146 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 145
    simpa using h
  have hprev := st191_p145
  have hstep := st191_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p147 : ((35406615411103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT191 (i+1))
      = (∑ i ∈ Finset.range 146, stT191 (i+1)) + stT191 147 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 146
    simpa using h
  have hprev := st191_p146
  have hstep := st191_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p148 : ((35517231143683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT191 (i+1))
      = (∑ i ∈ Finset.range 147, stT191 (i+1)) + stT191 148 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 147
    simpa using h
  have hprev := st191_p147
  have hstep := st191_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p149 : ((36327276925711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT191 (i+1))
      = (∑ i ∈ Finset.range 148, stT191 (i+1)) + stT191 149 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 148
    simpa using h
  have hprev := st191_p148
  have hstep := st191_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p150 : ((36677058096639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT191 (i+1))
      = (∑ i ∈ Finset.range 149, stT191 (i+1)) + stT191 150 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 149
    simpa using h
  have hprev := st191_p149
  have hstep := st191_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p151 : ((18039252853941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT191 (i+1))
      = (∑ i ∈ Finset.range 150, stT191 (i+1)) + stT191 151 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 150
    simpa using h
  have hprev := st191_p150
  have hstep := st191_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p152 : ((17686539295709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT191 (i+1))
      = (∑ i ∈ Finset.range 151, stT191 (i+1)) + stT191 152 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 151
    simpa using h
  have hprev := st191_p151
  have hstep := st191_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p153 : ((17766015786473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT191 (i+1))
      = (∑ i ∈ Finset.range 152, stT191 (i+1)) + stT191 153 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 152
    simpa using h
  have hprev := st191_p152
  have hstep := st191_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p154 : ((4541395757021/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT191 (i+1))
      = (∑ i ∈ Finset.range 153, stT191 (i+1)) + stT191 154 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 153
    simpa using h
  have hprev := st191_p153
  have hstep := st191_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p155 : ((36689931051489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT191 (i+1))
      = (∑ i ∈ Finset.range 154, stT191 (i+1)) + stT191 155 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 154
    simpa using h
  have hprev := st191_p154
  have hstep := st191_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p156 : ((7227058360517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT191 (i+1))
      = (∑ i ∈ Finset.range 155, stT191 (i+1)) + stT191 156 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 155
    simpa using h
  have hprev := st191_p155
  have hstep := st191_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p157 : ((17702434506353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT191 (i+1))
      = (∑ i ∈ Finset.range 156, stT191 (i+1)) + stT191 157 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 156
    simpa using h
  have hprev := st191_p156
  have hstep := st191_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p158 : ((2215623270079/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT191 (i+1))
      = (∑ i ∈ Finset.range 157, stT191 (i+1)) + stT191 158 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 157
    simpa using h
  have hprev := st191_p157
  have hstep := st191_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p159 : ((36205431910813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT191 (i+1))
      = (∑ i ∈ Finset.range 158, stT191 (i+1)) + stT191 159 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 158
    simpa using h
  have hprev := st191_p158
  have hstep := st191_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p160 : ((36703888827589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT191 (i+1))
      = (∑ i ∈ Finset.range 159, stT191 (i+1)) + stT191 160 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 159
    simpa using h
  have hprev := st191_p159
  have hstep := st191_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p161 : ((3632065487973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT191 (i+1))
      = (∑ i ∈ Finset.range 160, stT191 (i+1)) + stT191 161 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 160
    simpa using h
  have hprev := st191_p160
  have hstep := st191_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p162 : ((444256957511/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT191 (i+1))
      = (∑ i ∈ Finset.range 161, stT191 (i+1)) + stT191 162 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 161
    simpa using h
  have hprev := st191_p161
  have hstep := st191_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p163 : ((1103976451037/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT191 (i+1))
      = (∑ i ∈ Finset.range 162, stT191 (i+1)) + stT191 163 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 162
    simpa using h
  have hprev := st191_p162
  have hstep := st191_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p164 : ((1796759443599/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT191 (i+1))
      = (∑ i ∈ Finset.range 163, stT191 (i+1)) + stT191 164 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 163
    simpa using h
  have hprev := st191_p163
  have hstep := st191_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p165 : ((4578086706451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT191 (i+1))
      = (∑ i ∈ Finset.range 164, stT191 (i+1)) + stT191 165 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 164
    simpa using h
  have hprev := st191_p164
  have hstep := st191_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p166 : ((36573463804853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT191 (i+1))
      = (∑ i ∈ Finset.range 165, stT191 (i+1)) + stT191 166 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 165
    simpa using h
  have hprev := st191_p165
  have hstep := st191_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p167 : ((35848561731957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT191 (i+1))
      = (∑ i ∈ Finset.range 166, stT191 (i+1)) + stT191 167 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 166
    simpa using h
  have hprev := st191_p166
  have hstep := st191_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p168 : ((35301486742427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT191 (i+1))
      = (∑ i ∈ Finset.range 167, stT191 (i+1)) + stT191 168 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 167
    simpa using h
  have hprev := st191_p167
  have hstep := st191_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p169 : ((35561896482017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT191 (i+1))
      = (∑ i ∈ Finset.range 168, stT191 (i+1)) + stT191 169 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 168
    simpa using h
  have hprev := st191_p168
  have hstep := st191_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p170 : ((36325101591453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT191 (i+1))
      = (∑ i ∈ Finset.range 169, stT191 (i+1)) + stT191 170 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 169
    simpa using h
  have hprev := st191_p169
  have hstep := st191_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p171 : ((36724188554859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT191 (i+1))
      = (∑ i ∈ Finset.range 170, stT191 (i+1)) + stT191 171 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 170
    simpa using h
  have hprev := st191_p170
  have hstep := st191_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p172 : ((18158079744117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT191 (i+1))
      = (∑ i ∈ Finset.range 171, stT191 (i+1)) + stT191 172 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 171
    simpa using h
  have hprev := st191_p171
  have hstep := st191_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p173 : ((1777985684641/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT191 (i+1))
      = (∑ i ∈ Finset.range 172, stT191 (i+1)) + stT191 173 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 172
    simpa using h
  have hprev := st191_p172
  have hstep := st191_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p174 : ((8821581249761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT191 (i+1))
      = (∑ i ∈ Finset.range 173, stT191 (i+1)) + stT191 174 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 173
    simpa using h
  have hprev := st191_p173
  have hstep := st191_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p175 : ((8946988760051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT191 (i+1))
      = (∑ i ∈ Finset.range 174, stT191 (i+1)) + stT191 175 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 174
    simpa using h
  have hprev := st191_p174
  have hstep := st191_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p176 : ((228246957327/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT191 (i+1))
      = (∑ i ∈ Finset.range 175, stT191 (i+1)) + stT191 176 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 175
    simpa using h
  have hprev := st191_p175
  have hstep := st191_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p177 : ((458776287733/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT191 (i+1))
      = (∑ i ∈ Finset.range 176, stT191 (i+1)) + stT191 177 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 176
    simpa using h
  have hprev := st191_p176
  have hstep := st191_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p178 : ((4518580511581/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT191 (i+1))
      = (∑ i ∈ Finset.range 177, stT191 (i+1)) + stT191 178 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 177
    simpa using h
  have hprev := st191_p177
  have hstep := st191_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p179 : ((1107545921257/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT191 (i+1))
      = (∑ i ∈ Finset.range 178, stT191 (i+1)) + stT191 179 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 178
    simpa using h
  have hprev := st191_p178
  have hstep := st191_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p180 : ((275861662399/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT191 (i+1))
      = (∑ i ∈ Finset.range 179, stT191 (i+1)) + stT191 180 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 179
    simpa using h
  have hprev := st191_p179
  have hstep := st191_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p181 : ((8970940858429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT191 (i+1))
      = (∑ i ∈ Finset.range 180, stT191 (i+1)) + stT191 181 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 180
    simpa using h
  have hprev := st191_p180
  have hstep := st191_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p182 : ((18288355583189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT191 (i+1))
      = (∑ i ∈ Finset.range 181, stT191 (i+1)) + stT191 182 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 181
    simpa using h
  have hprev := st191_p181
  have hstep := st191_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p183 : ((9173859362797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT191 (i+1))
      = (∑ i ∈ Finset.range 182, stT191 (i+1)) + stT191 183 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 182
    simpa using h
  have hprev := st191_p182
  have hstep := st191_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p184 : ((18063716313799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT191 (i+1))
      = (∑ i ∈ Finset.range 183, stT191 (i+1)) + stT191 184 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 183
    simpa using h
  have hprev := st191_p183
  have hstep := st191_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p185 : ((8858810969957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT191 (i+1))
      = (∑ i ∈ Finset.range 184, stT191 (i+1)) + stT191 185 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 184
    simpa using h
  have hprev := st191_p184
  have hstep := st191_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p186 : ((4411443860959/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT191 (i+1))
      = (∑ i ∈ Finset.range 185, stT191 (i+1)) + stT191 186 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 185
    simpa using h
  have hprev := st191_p185
  have hstep := st191_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p187 : ((559838019639/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT191 (i+1))
      = (∑ i ∈ Finset.range 186, stT191 (i+1)) + stT191 187 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 186
    simpa using h
  have hprev := st191_p186
  have hstep := st191_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p188 : ((9132888591561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT191 (i+1))
      = (∑ i ∈ Finset.range 187, stT191 (i+1)) + stT191 188 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 187
    simpa using h
  have hprev := st191_p187
  have hstep := st191_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p189 : ((9183608180937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT191 (i+1))
      = (∑ i ∈ Finset.range 188, stT191 (i+1)) + stT191 189 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 188
    simpa using h
  have hprev := st191_p188
  have hstep := st191_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p190 : ((36253201339861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT191 (i+1))
      = (∑ i ∈ Finset.range 189, stT191 (i+1)) + stT191 190 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 189
    simpa using h
  have hprev := st191_p189
  have hstep := st191_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p191 : ((35538493027911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT191 (i+1))
      = (∑ i ∈ Finset.range 190, stT191 (i+1)) + stT191 191 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 190
    simpa using h
  have hprev := st191_p190
  have hstep := st191_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p192 : ((7049313757707/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT191 (i+1))
      = (∑ i ∈ Finset.range 191, stT191 (i+1)) + stT191 192 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 191
    simpa using h
  have hprev := st191_p191
  have hstep := st191_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p193 : ((7127698444021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT191 (i+1))
      = (∑ i ∈ Finset.range 192, stT191 (i+1)) + stT191 193 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 192
    simpa using h
  have hprev := st191_p192
  have hstep := st191_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p194 : ((36356392065507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT191 (i+1))
      = (∑ i ∈ Finset.range 193, stT191 (i+1)) + stT191 194 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 193
    simpa using h
  have hprev := st191_p193
  have hstep := st191_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p195 : ((36758734271381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT191 (i+1))
      = (∑ i ∈ Finset.range 194, stT191 (i+1)) + stT191 195 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 194
    simpa using h
  have hprev := st191_p194
  have hstep := st191_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p196 : ((36493547022449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT191 (i+1))
      = (∑ i ∈ Finset.range 195, stT191 (i+1)) + stT191 196 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 195
    simpa using h
  have hprev := st191_p195
  have hstep := st191_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p197 : ((17898987561049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT191 (i+1))
      = (∑ i ∈ Finset.range 196, stT191 (i+1)) + stT191 197 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 196
    simpa using h
  have hprev := st191_p196
  have hstep := st191_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p198 : ((4409660622481/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT191 (i+1))
      = (∑ i ∈ Finset.range 197, stT191 (i+1)) + stT191 198 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 197
    simpa using h
  have hprev := st191_p197
  have hstep := st191_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p199 : ((707524073047/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT191 (i+1))
      = (∑ i ∈ Finset.range 198, stT191 (i+1)) + stT191 199 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 198
    simpa using h
  have hprev := st191_p198
  have hstep := st191_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p200 : ((18002761167751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT191 (i+1))
      = (∑ i ∈ Finset.range 199, stT191 (i+1)) + stT191 200 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 199
    simpa using h
  have hprev := st191_p199
  have hstep := st191_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p201 : ((36631361552447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT191 (i+1))
      = (∑ i ∈ Finset.range 200, stT191 (i+1)) + stT191 201 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 200
    simpa using h
  have hprev := st191_p200
  have hstep := st191_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p202 : ((9183012450283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT191 (i+1))
      = (∑ i ∈ Finset.range 201, stT191 (i+1)) + stT191 202 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 201
    simpa using h
  have hprev := st191_p201
  have hstep := st191_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p203 : ((1811437051819/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT191 (i+1))
      = (∑ i ∈ Finset.range 202, stT191 (i+1)) + stT191 203 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 202
    simpa using h
  have hprev := st191_p202
  have hstep := st191_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p204 : ((35538345298959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT191 (i+1))
      = (∑ i ∈ Finset.range 203, stT191 (i+1)) + stT191 204 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 203
    simpa using h
  have hprev := st191_p203
  have hstep := st191_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p205 : ((4402791912999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT191 (i+1))
      = (∑ i ∈ Finset.range 204, stT191 (i+1)) + stT191 205 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 204
    simpa using h
  have hprev := st191_p204
  have hstep := st191_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p206 : ((17765801270749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT191 (i+1))
      = (∑ i ∈ Finset.range 205, stT191 (i+1)) + stT191 206 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 205
    simpa using h
  have hprev := st191_p205
  have hstep := st191_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p207 : ((144858571569/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT191 (i+1))
      = (∑ i ∈ Finset.range 206, stT191 (i+1)) + stT191 207 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 206
    simpa using h
  have hprev := st191_p206
  have hstep := st191_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p208 : ((293833255659/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT191 (i+1))
      = (∑ i ∈ Finset.range 207, stT191 (i+1)) + stT191 208 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 207
    simpa using h
  have hprev := st191_p207
  have hstep := st191_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p209 : ((7334784426239/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT191 (i+1))
      = (∑ i ∈ Finset.range 208, stT191 (i+1)) + stT191 209 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 208
    simpa using h
  have hprev := st191_p208
  have hstep := st191_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p210 : ((36096374152759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT191 (i+1))
      = (∑ i ∈ Finset.range 209, stT191 (i+1)) + stT191 210 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 209
    simpa using h
  have hprev := st191_p209
  have hstep := st191_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p211 : ((17722322995589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT191 (i+1))
      = (∑ i ∈ Finset.range 210, stT191 (i+1)) + stT191 211 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 210
    simpa using h
  have hprev := st191_p210
  have hstep := st191_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p212 : ((3521584718697/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT191 (i+1))
      = (∑ i ∈ Finset.range 211, stT191 (i+1)) + stT191 212 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 211
    simpa using h
  have hprev := st191_p211
  have hstep := st191_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p213 : ((17789670738267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT191 (i+1))
      = (∑ i ∈ Finset.range 212, stT191 (i+1)) + stT191 213 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 212
    simpa using h
  have hprev := st191_p212
  have hstep := st191_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p214 : ((36258225462489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT191 (i+1))
      = (∑ i ∈ Finset.range 213, stT191 (i+1)) + stT191 214 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 213
    simpa using h
  have hprev := st191_p213
  have hstep := st191_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p215 : ((36746126016071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT191 (i+1))
      = (∑ i ∈ Finset.range 214, stT191 (i+1)) + stT191 215 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 214
    simpa using h
  have hprev := st191_p214
  have hstep := st191_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p216 : ((36685585500007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT191 (i+1))
      = (∑ i ∈ Finset.range 215, stT191 (i+1)) + stT191 216 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 215
    simpa using h
  have hprev := st191_p215
  have hstep := st191_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p217 : ((36125101198827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT191 (i+1))
      = (∑ i ∈ Finset.range 216, stT191 (i+1)) + stT191 217 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 216
    simpa using h
  have hprev := st191_p216
  have hstep := st191_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p218 : ((35473900191831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT191 (i+1))
      = (∑ i ∈ Finset.range 217, stT191 (i+1)) + stT191 218 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 217
    simpa using h
  have hprev := st191_p217
  have hstep := st191_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p219 : ((35199543806451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT191 (i+1))
      = (∑ i ∈ Finset.range 218, stT191 (i+1)) + stT191 219 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 218
    simpa using h
  have hprev := st191_p218
  have hstep := st191_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p220 : ((35494055504019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT191 (i+1))
      = (∑ i ∈ Finset.range 219, stT191 (i+1)) + stT191 220 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 219
    simpa using h
  have hprev := st191_p219
  have hstep := st191_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p221 : ((36145373531379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT191 (i+1))
      = (∑ i ∈ Finset.range 220, stT191 (i+1)) + stT191 221 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 220
    simpa using h
  have hprev := st191_p220
  have hstep := st191_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p222 : ((36695511379551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT191 (i+1))
      = (∑ i ∈ Finset.range 221, stT191 (i+1)) + stT191 222 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 221
    simpa using h
  have hprev := st191_p221
  have hstep := st191_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p223 : ((36764011115059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT191 (i+1))
      = (∑ i ∈ Finset.range 222, stT191 (i+1)) + stT191 223 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 222
    simpa using h
  have hprev := st191_p222
  have hstep := st191_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p224 : ((36307526965951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT191 (i+1))
      = (∑ i ∈ Finset.range 223, stT191 (i+1)) + stT191 224 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 223
    simpa using h
  have hprev := st191_p223
  have hstep := st191_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p225 : ((35641169299439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT191 (i+1))
      = (∑ i ∈ Finset.range 224, stT191 (i+1)) + stT191 225 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 224
    simpa using h
  have hprev := st191_p224
  have hstep := st191_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p226 : ((17608414330573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT191 (i+1))
      = (∑ i ∈ Finset.range 225, stT191 (i+1)) + stT191 226 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 225
    simpa using h
  have hprev := st191_p225
  have hstep := st191_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p227 : ((17658496213261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT191 (i+1))
      = (∑ i ∈ Finset.range 226, stT191 (i+1)) + stT191 227 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 226
    simpa using h
  have hprev := st191_p226
  have hstep := st191_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p228 : ((4483878781817/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT191 (i+1))
      = (∑ i ∈ Finset.range 227, stT191 (i+1)) + stT191 228 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 227
    simpa using h
  have hprev := st191_p227
  have hstep := st191_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p229 : ((18255123387467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT191 (i+1))
      = (∑ i ∈ Finset.range 228, stT191 (i+1)) + stT191 229 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 228
    simpa using h
  have hprev := st191_p228
  have hstep := st191_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p230 : ((18408039214197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT191 (i+1))
      = (∑ i ∈ Finset.range 229, stT191 (i+1)) + stT191 230 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 229
    simpa using h
  have hprev := st191_p229
  have hstep := st191_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p231 : ((18296368310997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT191 (i+1))
      = (∑ i ∈ Finset.range 230, stT191 (i+1)) + stT191 231 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 230
    simpa using h
  have hprev := st191_p230
  have hstep := st191_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p232 : ((17993931132283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT191 (i+1))
      = (∑ i ∈ Finset.range 231, stT191 (i+1)) + stT191 232 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 231
    simpa using h
  have hprev := st191_p231
  have hstep := st191_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p233 : ((1105943433691/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT191 (i+1))
      = (∑ i ∈ Finset.range 232, stT191 (i+1)) + stT191 233 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 232
    simpa using h
  have hprev := st191_p232
  have hstep := st191_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p234 : ((2198615677361/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT191 (i+1))
      = (∑ i ∈ Finset.range 233, stT191 (i+1)) + stT191 234 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 233
    simpa using h
  have hprev := st191_p233
  have hstep := st191_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p235 : ((2217575590681/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT191 (i+1))
      = (∑ i ∈ Finset.range 234, stT191 (i+1)) + stT191 235 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 234
    simpa using h
  have hprev := st191_p234
  have hstep := st191_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p236 : ((2256717626397/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT191 (i+1))
      = (∑ i ∈ Finset.range 235, stT191 (i+1)) + stT191 236 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 235
    simpa using h
  have hprev := st191_p235
  have hstep := st191_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p237 : ((36667379970609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT191 (i+1))
      = (∑ i ∈ Finset.range 236, stT191 (i+1)) + stT191 237 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 236
    simpa using h
  have hprev := st191_p236
  have hstep := st191_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p238 : ((18409139193997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT191 (i+1))
      = (∑ i ∈ Finset.range 237, stT191 (i+1)) + stT191 238 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 237
    simpa using h
  have hprev := st191_p237
  have hstep := st191_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p239 : ((18235727275461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT191 (i+1))
      = (∑ i ∈ Finset.range 238, stT191 (i+1)) + stT191 239 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 238
    simpa using h
  have hprev := st191_p238
  have hstep := st191_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p240 : ((447997054983/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT191 (i+1))
      = (∑ i ∈ Finset.range 239, stT191 (i+1)) + stT191 240 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 239
    simpa using h
  have hprev := st191_p239
  have hstep := st191_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p241 : ((4412913161973/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT191 (i+1))
      = (∑ i ∈ Finset.range 240, stT191 (i+1)) + stT191 241 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 240
    simpa using h
  have hprev := st191_p240
  have hstep := st191_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p242 : ((17589931805517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT191 (i+1))
      = (∑ i ∈ Finset.range 241, stT191 (i+1)) + stT191 242 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 241
    simpa using h
  have hprev := st191_p241
  have hstep := st191_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p243 : ((17769552126267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT191 (i+1))
      = (∑ i ∈ Finset.range 242, stT191 (i+1)) + stT191 243 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 242
    simpa using h
  have hprev := st191_p242
  have hstep := st191_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p244 : ((3616749862399/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT191 (i+1))
      = (∑ i ∈ Finset.range 243, stT191 (i+1)) + stT191 244 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 243
    simpa using h
  have hprev := st191_p243
  have hstep := st191_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p245 : ((18349303871279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT191 (i+1))
      = (∑ i ∈ Finset.range 244, stT191 (i+1)) + stT191 245 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 244
    simpa using h
  have hprev := st191_p244
  have hstep := st191_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p246 : ((18413731882443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT191 (i+1))
      = (∑ i ∈ Finset.range 245, stT191 (i+1)) + stT191 246 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 245
    simpa using h
  have hprev := st191_p245
  have hstep := st191_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p247 : ((9120844981359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT191 (i+1))
      = (∑ i ∈ Finset.range 246, stT191 (i+1)) + stT191 247 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 246
    simpa using h
  have hprev := st191_p246
  have hstep := st191_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p248 : ((35864749886217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT191 (i+1))
      = (∑ i ∈ Finset.range 247, stT191 (i+1)) + stT191 248 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 247
    simpa using h
  have hprev := st191_p247
  have hstep := st191_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p249 : ((17660716364221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT191 (i+1))
      = (∑ i ∈ Finset.range 248, stT191 (i+1)) + stT191 249 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 248
    simpa using h
  have hprev := st191_p248
  have hstep := st191_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_p250 : ((3515610114057/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT191 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT191 (i+1))
      = (∑ i ∈ Finset.range 249, stT191 (i+1)) + stT191 250 := by
    have h := Finset.sum_range_succ (fun i => stT191 (i+1)) 249
    simpa using h
  have hprev := st191_p249
  have hstep := st191_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st191_s250 :
    |Real.sin (((191 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))
      - ((-965241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -4588073/10000000) (δ := 1919/200000000) (ψ := 859139/1000000) 191 168
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 191`** (evaluated boundary). -/
theorem station_191_sign : hardyG ((((191:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 191 250 (by norm_num) (by norm_num)
    ((859139/1000000 : ℚ) : ℝ)
  have hchain := st191_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT191 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((191 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((859139/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st191_c250
  have hsinb := abs_le.mp st191_s250
  have hbdy_lo : ((23335329991267/291850000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((191 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((859139/1000000 : ℚ) : ℝ))) / 2
          - ((((191:ℕ)):ℝ))
            * Real.sin (((191 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((859139/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((191:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((191:ℝ) * Real.log (250:ℝ) - ((859139/1000000 : ℚ) : ℝ))) / 2
        - ((191:ℝ)) * Real.sin ((191:ℝ) * Real.log (250:ℝ) - ((859139/1000000 : ℚ) : ℝ))
        ≥ ((184482137/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((191:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((184482137/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((184482137/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((184482137/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((191:ℕ)):ℝ))+1) * (((((191:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((31934363637/39062500000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((3515610114057/1000000000000 : ℚ) : ℝ) + ((23335329991267/291850000000000 : ℚ) : ℝ)
      - ((31934363637/39062500000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((859139/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((191:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((859139/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((191:ℕ)):ℝ)))).re
      - Real.sin ((859139/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((191:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((191:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((191:ℕ)):ℝ))
      = (((((191:ℕ)):ℝ)) * (Real.log ((((191:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((191:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_191
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
  have hθwin : |(((859139/1000000 : ℚ) : ℝ) + ((37:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((191:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((191:ℕ)):ℝ)))
    (φ := ((859139/1000000 : ℚ) : ℝ) + ((37:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((859139/1000000 : ℚ) : ℝ) + ((37:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((859139/1000000 : ℚ)) : ℝ) - Real.pi) + ((37:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((859139/1000000 : ℚ)) : ℝ) - Real.pi) 37).1,
    (cos_sin_shift ((((859139/1000000 : ℚ)) : ℝ) - Real.pi) 37).2]
  exact cos_sin_flip ((859139/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_191_sign
end AxiomAudit
