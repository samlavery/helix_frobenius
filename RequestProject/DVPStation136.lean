import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 136` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT136 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((136 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))

theorem st136_c1 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((786159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52049/312500) (δ := 201/1000000000) (ψ := -666227/1000000) 136 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t1 : ((786109/1000000 : ℚ) : ℝ) ≤ stT136 1 := by
  have hc : ((786109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((786109/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((786109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c2 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((154699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1716149/10000000) (δ := 3497/500000000) (ψ := -666227/1000000) 136 15
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t2 : ((1093816283163/2000000000000 : ℚ) : ℝ) ≤ stT136 2 := by
  have hc : ((154689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1093816283163/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((154689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c3 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((150499/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -898693/5000000) (δ := 6829/1000000000) (ψ := -666227/1000000) 136 24
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t3 : ((434424271239/1000000000000 : ℚ) : ℝ) ≤ stT136 3 := by
  have hc : ((150489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((434424271239/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((150489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c4 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((760509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441687/2500000) (δ := 3493/500000000) (ψ := -666227/1000000) 136 30
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t4 : ((760459/2000000 : ℚ) : ℝ) ≤ stT136 4 := by
  have hc : ((760459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760459/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((760459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c5 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((935297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226061/2500000) (δ := 137/20000000) (ψ := -666227/1000000) 136 35
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t5 : ((836510168469/2000000000000 : ℚ) : ℝ) ≤ stT136 5 := by
  have hc : ((935247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((836510168469/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((935247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c6 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((76567/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1746787/10000000) (δ := 6821/1000000000) (ψ := -666227/1000000) 136 39
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t6 : ((78140746721/250000000000 : ℚ) : ℝ) ≤ stT136 6 := by
  have hc : ((38281/50000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78140746721/250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((38281/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c7 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((153957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3540561/10000000) (δ := 69/10000000) (ψ := -666227/1000000) 136 42
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t7 : ((145428417277/2500000000000 : ℚ) : ℝ) ≤ stT136 7 := by
  have hc : ((153907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145428417277/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((153907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c8 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((186803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1817347/10000000) (δ := 3489/500000000) (ψ := -666227/1000000) 136 45
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t8 : ((1320807953673/5000000000000 : ℚ) : ℝ) ≤ stT136 8 := by
  have hc : ((373581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1320807953673/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((373581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c9 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-254203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2630161/5000000) (δ := 3473/500000000) (ψ := -666227/1000000) 136 48
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t9 : ((-105928354519/625000000000 : ℚ) : ℝ) ≤ stT136 9 := by
  have hc : ((-63557/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105928354519/625000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-63557/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c10 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((942263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -853679/10000000) (δ := 6843/1000000000) (ψ := -666227/1000000) 136 50
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t10 : ((2979538499001/10000000000000 : ℚ) : ℝ) ≤ stT136 10 := by
  have hc : ((942213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2979538499001/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((942213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c11 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((249631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135863/10000000) (δ := 279/40000000) (ψ := -666227/1000000) 136 52
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t11 : ((1505255968781/5000000000000 : ℚ) : ℝ) ≤ stT136 11 := by
  have hc : ((499237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1505255968781/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((499237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c12 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((778531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424047/2500000) (δ := 3407/500000000) (ψ := -666227/1000000) 136 54
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t12 : ((2247280805231/10000000000000 : ℚ) : ℝ) ≤ stT136 12 := by
  have hc : ((778481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2247280805231/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((778481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c13 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-141823/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5897597/10000000) (δ := 6999/1000000000) (ψ := -666227/1000000) 136 56
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t13 : ((-393373967333/2000000000000 : ℚ) : ℝ) ≤ stT136 13 := by
  have hc : ((-141833/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393373967333/2000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-141833/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c14 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((133929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89779/250000) (δ := 1723/250000000) (ψ := -666227/1000000) 136 57
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t14 : ((89451655487/2500000000000 : ℚ) : ℝ) ≤ stT136 14 := by
  have hc : ((133879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89451655487/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((133879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c15 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-175167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218359/500000) (δ := 277/40000000) (ψ := -666227/1000000) 136 59
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t15 : ((-452408366613/10000000000000 : ℚ) : ℝ) ≤ stT136 15 := by
  have hc : ((-175217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452408366613/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-175217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c16 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((733609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 933973/5000000) (δ := 6971/1000000000) (ψ := -666227/1000000) 136 60
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t16 : ((733559/4000000 : ℚ) : ℝ) ≤ stT136 16 := by
  have hc : ((733559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((733559/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((733559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c17 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-56741/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6772347/10000000) (δ := 429/62500000) (ψ := -666227/1000000) 136 61
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t17 : ((-1100998086221/5000000000000 : ℚ) : ℝ) ≤ stT136 17 := by
  have hc : ((-453953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1100998086221/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-453953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c18 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-245437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5209723/10000000) (δ := 3477/500000000) (ψ := -666227/1000000) 136 63
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t18 : ((-289279789813/2500000000000 : ℚ) : ℝ) ≤ stT136 18 := by
  have hc : ((-122731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289279789813/2500000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-122731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c19 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((132131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2534839/10000000) (δ := 3471/500000000) (ψ := -666227/1000000) 136 64
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t19 : ((606201163209/5000000000000 : ℚ) : ℝ) ≤ stT136 19 := by
  have hc : ((264237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606201163209/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((264237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c20 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((948847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20077/250000) (δ := 1367/200000000) (ψ := -666227/1000000) 136 65
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t20 : ((2121573661399/10000000000000 : ℚ) : ℝ) ≤ stT136 20 := by
  have hc : ((948797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2121573661399/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((948797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c21 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((499759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621/80000) (δ := 11/1600000) (ψ := -666227/1000000) 136 66
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t21 : ((272627135163/1250000000000 : ℚ) : ℝ) ≤ stT136 21 := by
  have hc : ((249867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272627135163/1250000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((249867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c22 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((49861/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93231/5000000) (δ := 6983/1000000000) (ψ := -666227/1000000) 136 67
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t22 : ((212597342019/1000000000000 : ℚ) : ℝ) ≤ stT136 22 := by
  have hc : ((99717/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212597342019/1000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((99717/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c23 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((6167/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40789/1000000) (δ := 6913/1000000000) (ψ := -666227/1000000) 136 68
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t23 : ((25716862881/125000000000 : ℚ) : ℝ) ≤ stT136 23 := by
  have hc : ((98667/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25716862881/125000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((98667/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c24 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((791073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1645589/10000000) (δ := 3403/500000000) (ψ := -666227/1000000) 136 69
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t24 : ((1614668579543/10000000000000 : ℚ) : ℝ) ≤ stT136 24 := by
  have hc : ((791023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1614668579543/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((791023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c25 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((90089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434259/1250000) (δ := 863/125000000) (ψ := -666227/1000000) 136 70
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t25 : ((5629/156250 : ℚ) : ℝ) ≤ stT136 25 := by
  have hc : ((5629/31250 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5629/156250 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((5629/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c26 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-6947/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2923499/5000000) (δ := 437/62500000) (ψ := -666227/1000000) 136 71
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t26 : ((-2725034599/20000000000 : ℚ) : ℝ) ≤ stT136 26 := by
  have hc : ((-2779/4000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2725034599/20000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-2779/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c27 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-188031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54568/78125) (δ := 437/62500000) (ψ := -666227/1000000) 136 71
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t27 : ((-361885092541/2000000000000 : ℚ) : ℝ) ≤ stT136 27 := by
  have hc : ((-188041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361885092541/2000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-188041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c28 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((22769/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3641759/10000000) (δ := 1377/200000000) (ψ := -666227/1000000) 136 72
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t28 : ((21505229449/1000000000000 : ℚ) : ℝ) ≤ stT136 28 := by
  have hc : ((22759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21505229449/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((22759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c29 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((998539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67581/5000000) (δ := 3413/500000000) (ψ := -666227/1000000) 136 73
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t29 : ((1854147144017/10000000000000 : ℚ) : ℝ) ≤ stT136 29 := by
  have hc : ((998489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1854147144017/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((998489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c30 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-7761/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -863323/2000000) (δ := 6933/1000000000) (ψ := -666227/1000000) 136 74
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t30 : ((-14174148017/500000000000 : ℚ) : ℝ) ≤ stT136 30 := by
  have hc : ((-15527/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14174148017/500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-15527/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c31 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-458797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6831951/10000000) (δ := 6933/1000000000) (ψ := -666227/1000000) 136 74
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t31 : ((-206017272097/1250000000000 : ℚ) : ℝ) ≤ stT136 31 := by
  have hc : ((-229411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206017272097/1250000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-229411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c32 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((359853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 383709/2000000) (δ := 6963/1000000000) (ψ := -666227/1000000) 136 75
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t32 : ((79511463031/625000000000 : ℚ) : ℝ) ≤ stT136 32 := by
  have hc : ((89957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79511463031/625000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((89957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c33 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((23767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1663537/5000000) (δ := 857/125000000) (ψ := -666227/1000000) 136 76
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t33 : ((2585269957/62500000000 : ℚ) : ℝ) ≤ stT136 33 := by
  have hc : ((11881/50000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2585269957/62500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((11881/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c34 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-229039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3411473/5000000) (δ := 857/125000000) (ψ := -666227/1000000) 136 76
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t34 : ((-392820115779/2500000000000 : ℚ) : ℝ) ≤ stT136 34 := by
  have hc : ((-458103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-392820115779/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-458103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c35 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((925557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970733/10000000) (δ := 3427/500000000) (ψ := -666227/1000000) 136 77
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t35 : ((391097971539/2500000000000 : ℚ) : ℝ) ≤ stT136 35 := by
  have hc : ((925507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391097971539/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((925507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c36 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-236571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1289781/2500000) (δ := 3481/500000000) (ψ := -666227/1000000) 136 78
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t36 : ((-98581686383/1250000000000 : ℚ) : ℝ) ≤ stT136 36 := by
  have hc : ((-59149/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98581686383/1250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-59149/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c37 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-91689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519567/1250000) (δ := 3481/500000000) (ψ := -666227/1000000) 136 78
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t37 : ((-15081799861/1000000000000 : ℚ) : ℝ) ≤ stT136 37 := by
  have hc : ((-91739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15081799861/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-91739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c38 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((136399/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31053/125000) (δ := 3467/500000000) (ψ := -666227/1000000) 136 79
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t38 : ((221248089711/2500000000000 : ℚ) : ℝ) ≤ stT136 38 := by
  have hc : ((272773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221248089711/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((272773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c39 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-823853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 634743/1000000) (δ := 3467/500000000) (ψ := -666227/1000000) 136 79
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t39 : ((-659650521823/5000000000000 : ℚ) : ℝ) ≤ stT136 39 := by
  have hc : ((-823903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-659650521823/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-823903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c40 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((955043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -752481/10000000) (δ := 6827/1000000000) (ψ := -666227/1000000) 136 80
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t40 : ((754987861017/5000000000000 : ℚ) : ℝ) ≤ stT136 40 := by
  have hc : ((954993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((754987861017/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((954993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c41 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-996441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7643003/10000000) (δ := 6827/1000000000) (ψ := -666227/1000000) 136 80
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t41 : ((-778128930679/5000000000000 : ℚ) : ℝ) ≤ stT136 41 := by
  have hc : ((-996491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-778128930679/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-996491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c42 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((199737/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4007/312500) (δ := 6883/1000000000) (ψ := -666227/1000000) 136 81
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t42 : ((308185351991/2000000000000 : ℚ) : ℝ) ≤ stT136 42 := by
  have hc : ((199727/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308185351991/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((199727/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c43 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-993973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7579369/10000000) (δ := 699/100000000) (ψ := -666227/1000000) 136 82
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t43 : ((-757935579339/5000000000000 : ℚ) : ℝ) ≤ stT136 43 := by
  have hc : ((-994023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-757935579339/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-994023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c44 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((248877/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237061/10000000) (δ := 699/100000000) (ψ := -666227/1000000) 136 82
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t44 : ((187588585081/1250000000000 : ℚ) : ℝ) ≤ stT136 44 := by
  have hc : ((497729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187588585081/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((497729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c45 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-199991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7830151/10000000) (δ := 3453/500000000) (ψ := -666227/1000000) 136 83
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t45 : ((-37267986339/250000000000 : ℚ) : ℝ) ≤ stT136 45 := by
  have hc : ((-200001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37267986339/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-200001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c46 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((989803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14293/400000) (δ := 3453/500000000) (ψ := -666227/1000000) 136 83
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t46 : ((1459310628507/10000000000000 : ℚ) : ℝ) ≤ stT136 46 := by
  have hc : ((989753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1459310628507/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((989753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c47 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-468007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6954817/10000000) (δ := 3453/500000000) (ψ := -666227/1000000) 136 83
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t47 : ((-213342149/1562500000 : ℚ) : ℝ) ≤ stT136 47 := by
  have hc : ((-14626/15625 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213342149/1562500000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-14626/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c48 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((803291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -159499/1000000) (δ := 1361/200000000) (ψ := -666227/1000000) 136 84
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t48 : ((9275023827/80000000000 : ℚ) : ℝ) ≤ stT136 48 := by
  have hc : ((803241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9275023827/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((803241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c49 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-70107/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2707769/5000000) (δ := 1361/200000000) (ψ := -666227/1000000) 136 84
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t49 : ((-100161825779/1250000000000 : ℚ) : ℝ) ≤ stT136 49 := by
  have hc : ((-280453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100161825779/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-280453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c50 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((12503/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3423473/10000000) (δ := 27/3906250) (ψ := -666227/1000000) 136 85
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t50 : ((141419885787/5000000000000 : ℚ) : ℝ) ≤ stT136 50 := by
  have hc : ((99999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141419885787/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((99999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c51 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((244527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3309411/10000000) (δ := 27/3906250) (ψ := -666227/1000000) 136 85
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t51 : ((8558406339/250000000000 : ℚ) : ℝ) ≤ stT136 51 := by
  have hc : ((244477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8558406339/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((244477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c52 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-17/25 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5796399/10000000) (δ := 873/125000000) (ψ := -666227/1000000) 136 86
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t52 : ((-18861200351/200000000000 : ℚ) : ℝ) ≤ stT136 52 := by
  have hc : ((-13601/20000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18861200351/200000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-13601/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c53 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((963237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 679989/10000000) (δ := 873/125000000) (ψ := -666227/1000000) 136 86
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t53 : ((264607695827/2000000000000 : ℚ) : ℝ) ≤ stT136 53 := by
  have hc : ((963187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264607695827/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((963187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c54 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-946859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7035303/10000000) (δ := 873/125000000) (ψ := -666227/1000000) 136 86
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t54 : ((-322145070163/2500000000000 : ℚ) : ℝ) ≤ stT136 54 := by
  have hc : ((-946909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322145070163/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-946909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c55 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((281169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1216983/5000000) (δ := 6877/1000000000) (ψ := -666227/1000000) 136 87
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t55 : ((47386786057/625000000000 : ℚ) : ℝ) ≤ stT136 55 := by
  have hc : ((35143/62500 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47386786057/625000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((35143/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c56 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((93729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 923081/2500000) (δ := 6877/1000000000) (ψ := -666227/1000000) 136 87
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t56 : ((62591904887/5000000000000 : ℚ) : ℝ) ≤ stT136 56 := by
  have hc : ((93679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62591904887/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((93679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c57 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-92099/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239911/400000) (δ := 6833/1000000000) (ψ := -666227/1000000) 136 88
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t57 : ((-487985772393/5000000000000 : ℚ) : ℝ) ≤ stT136 57 := by
  have hc : ((-368421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-487985772393/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-368421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c58 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((249857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84563/10000000) (δ := 6833/1000000000) (ψ := -666227/1000000) 136 88
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t58 : ((82015454637/625000000000 : ℚ) : ℝ) ≤ stT136 58 := by
  have hc : ((499689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82015454637/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((499689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c59 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-164887/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5727533/10000000) (δ := 6833/1000000000) (ψ := -666227/1000000) 136 88
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t59 : ((-42936202011/500000000000 : ℚ) : ℝ) ≤ stT136 59 := by
  have hc : ((-329799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42936202011/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-329799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c60 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-27039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133313/312500) (δ := 347/50000000) (ψ := -666227/1000000) 136 89
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t60 : ((-6984024751/400000000000 : ℚ) : ℝ) ≤ stT136 60 := by
  have hc : ((-27049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6984024751/400000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-27049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c61 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((13389/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 676973/5000000) (δ := 347/50000000) (ψ := -666227/1000000) 136 89
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t61 : ((34283693729/312500000000 : ℚ) : ℝ) ≤ stT136 61 := by
  have hc : ((428423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34283693729/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((428423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c62 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-462723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1720629/2500000) (δ := 347/50000000) (ψ := -666227/1000000) 136 89
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t62 : ((-73461360687/625000000000 : ℚ) : ℝ) ≤ stT136 62 := by
  have hc : ((-115687/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73461360687/625000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-115687/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c63 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((10749/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105791/312500) (δ := 1391/200000000) (ψ := -666227/1000000) 136 90
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t63 : ((27078622333/1000000000000 : ℚ) : ℝ) ≤ stT136 63 := by
  have hc : ((21493/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27078622333/1000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((21493/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c64 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((705517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196911/1000000) (δ := 1391/200000000) (ψ := -666227/1000000) 136 90
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t64 : ((705467/8000000 : ℚ) : ℝ) ≤ stT136 64 := by
  have hc : ((705467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((705467/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((705467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c65 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-485023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3620269/5000000) (δ := 1391/200000000) (ψ := -666227/1000000) 136 90
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t65 : ((-18800884897/156250000000 : ℚ) : ℝ) ≤ stT136 65 := by
  have hc : ((-60631/62500 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18800884897/156250000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-60631/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c66 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((804/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131059/400000) (δ := 107/15625000) (ψ := -666227/1000000) 136 91
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t66 : ((15831400411/500000000000 : ℚ) : ℝ) ≤ stT136 66 := by
  have hc : ((25723/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15831400411/500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((25723/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c67 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((742123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1836411/10000000) (δ := 107/15625000) (ψ := -666227/1000000) 136 91
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t67 : ((453293065831/5000000000000 : ℚ) : ℝ) ≤ stT136 67 := by
  have hc : ((742073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453293065831/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((742073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c68 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-11551/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374709/2000000) (δ := 107/15625000) (ψ := -666227/1000000) 136 91
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t68 : ((-112067304427/1000000000000 : ℚ) : ℝ) ≤ stT136 68 := by
  have hc : ((-92413/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112067304427/1000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-92413/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c69 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((351/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1935413/5000000) (δ := 3431/500000000) (ψ := -666227/1000000) 136 92
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t69 : ((6745818303/2500000000000 : ℚ) : ℝ) ≤ stT136 69 := by
  have hc : ((11207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6745818303/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((11207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c70 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((183541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255333/2500000) (δ := 3431/500000000) (ψ := -666227/1000000) 136 92
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t70 : ((54840347517/500000000000 : ℚ) : ℝ) ≤ stT136 70 := by
  have hc : ((183531/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54840347517/500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((183531/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c71 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-138773/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45657/78125) (δ := 3431/500000000) (ψ := -666227/1000000) 136 92
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t71 : ((-82352583153/1000000000000 : ℚ) : ℝ) ≤ stT136 71 := by
  have hc : ((-138783/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82352583153/1000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-138783/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c72 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-91043/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204341/400000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 93
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t72 : ((-6706690821/125000000000 : ℚ) : ℝ) ≤ stT136 72 := by
  have hc : ((-91053/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6706690821/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-91053/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c73 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((986001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418803/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 93
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t73 : ((1153967895861/10000000000000 : ℚ) : ℝ) ≤ stT136 73 := by
  have hc : ((985951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1153967895861/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((985951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c74 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-11181/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4207101/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 93
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t74 : ((-6501733861/500000000000 : ℚ) : ℝ) ≤ stT136 74 := by
  have hc : ((-5593/50000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6501733861/500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-5593/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c75 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-233371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6937009/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 94
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t75 : ((-538976321667/5000000000000 : ℚ) : ℝ) ≤ stT136 75 := by
  have hc : ((-466767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538976321667/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-466767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c76 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((112489/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2433641/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 94
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t76 : ((64511093181/1000000000000 : ℚ) : ℝ) ≤ stT136 76 := by
  have hc : ((112479/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64511093181/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((112479/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c77 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((34679/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2010873/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 94
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t77 : ((15807005113/200000000000 : ℚ) : ℝ) ≤ stT136 77 := by
  have hc : ((69353/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15807005113/200000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((69353/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c78 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-167031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6398029/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 94
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t78 : ((-94568424699/1000000000000 : ℚ) : ℝ) ≤ stT136 78 := by
  have hc : ((-167041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94568424699/1000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-167041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c79 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-3267/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2489337/5000000) (δ := 6819/1000000000) (ψ := -666227/1000000) 136 95
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t79 : ((-574392583/12500000000 : ℚ) : ℝ) ≤ stT136 79 := by
  have hc : ((-16337/40000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-574392583/12500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-16337/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c80 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((960847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -350941/5000000) (δ := 6819/1000000000) (ψ := -666227/1000000) 136 95
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t80 : ((1074202752301/10000000000000 : ℚ) : ℝ) ≤ stT136 80 := by
  have hc : ((960797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1074202752301/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((960797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c81 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((8069/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 440221/1250000) (δ := 6819/1000000000) (ψ := -666227/1000000) 136 95
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t81 : ((17925553763/1000000000000 : ℚ) : ℝ) ≤ stT136 81 := by
  have hc : ((16133/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17925553763/1000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((16133/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c82 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-997943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3846801/5000000) (δ := 6819/1000000000) (ψ := -666227/1000000) 136 95
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t82 : ((-275524909447/2500000000000 : ℚ) : ℝ) ≤ stT136 82 := by
  have hc : ((-997993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275524909447/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-997993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c83 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((6781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -778617/2000000) (δ := 6891/1000000000) (ψ := -666227/1000000) 136 96
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t83 : ((926958669/625000000000 : ℚ) : ℝ) ≤ stT136 83 := by
  have hc : ((1689/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((926958669/625000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((1689/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c84 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((997443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89403/5000000) (δ := 13691/1000000000) (ψ := -666227/1000000) 136 96
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t84 : ((1088244530977/10000000000000 : ℚ) : ℝ) ≤ stT136 84 := by
  have hc : ((997393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1088244530977/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((997393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c85 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-27497/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4202519/10000000) (δ := 6891/1000000000) (ψ := -666227/1000000) 136 96
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t85 : ((-59676523407/5000000000000 : ℚ) : ℝ) ≤ stT136 85 := by
  have hc : ((-55019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59676523407/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-55019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c86 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-991553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1882201/2500000) (δ := 3499/500000000) (ψ := -666227/1000000) 136 97
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t86 : ((-133659159973/1250000000000 : ℚ) : ℝ) ≤ stT136 86 := by
  have hc : ((-991603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133659159973/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-991603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c87 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((65589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1799049/5000000) (δ := 3499/500000000) (ψ := -666227/1000000) 136 97
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t87 : ((1098311737/78125000000 : ℚ) : ℝ) ≤ stT136 87 := by
  have hc : ((16391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1098311737/78125000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((16391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c88 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((993387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14383/500000) (δ := 3499/500000000) (ψ := -666227/1000000) 136 97
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t88 : ((1058900222011/10000000000000 : ℚ) : ℝ) ≤ stT136 88 := by
  have hc : ((993337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1058900222011/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((993337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c89 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-80911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412949/1000000) (δ := 3499/500000000) (ψ := -666227/1000000) 136 97
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t89 : ((-42909249039/5000000000000 : ℚ) : ℝ) ≤ stT136 89 := by
  have hc : ((-80961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42909249039/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-80961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c90 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-999557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243111/312500) (δ := 3449/500000000) (ψ := -666227/1000000) 136 98
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t90 : ((-1053678741451/10000000000000 : ℚ) : ℝ) ≤ stT136 90 := by
  have hc : ((-999607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1053678741451/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-999607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c91 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-9559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4022603/10000000) (δ := 6849/500000000) (ψ := -666227/1000000) 136 98
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t91 : ((-4013463951/1000000000000 : ℚ) : ℝ) ≤ stT136 91 := by
  have hc : ((-19143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4013463951/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-19143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c92 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((992483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153363/5000000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 98
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t92 : ((258670714419/2500000000000 : ℚ) : ℝ) ≤ stT136 92 := by
  have hc : ((992433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258670714419/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((992433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c93 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((55339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 168449/500000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 98
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t93 : ((114741739003/5000000000000 : ℚ) : ℝ) ≤ stT136 93 := by
  have hc : ((110653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114741739003/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((110653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c94 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-942941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3502691/5000000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 98
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t94 : ((-486310831601/5000000000000 : ℚ) : ℝ) ≤ stT136 94 := by
  have hc : ((-942991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-486310831601/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-942991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c95 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-5673/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5104667/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 99
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t95 : ((-46568160831/1000000000000 : ℚ) : ℝ) ≤ stT136 95 := by
  have hc : ((-45389/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46568160831/1000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-45389/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c96 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((203793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61777/400000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 99
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t96 : ((20798245391/250000000000 : ℚ) : ℝ) ≤ stT136 96 := by
  have hc : ((407561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20798245391/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((407561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c97 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((702729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1978927/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 99
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t97 : ((356731155967/5000000000000 : ℚ) : ℝ) ≤ stT136 97 := by
  have hc : ((702679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356731155967/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((702679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c98 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-72187/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5466137/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 99
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t98 : ((-291704912269/5000000000000 : ℚ) : ℝ) ≤ stT136 98 := by
  have hc : ((-288773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291704912269/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-288773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c99 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-227699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -679001/1000000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 100
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t99 : ((-228858710537/2500000000000 : ℚ) : ℝ) ≤ stT136 99 := by
  have hc : ((-455423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228858710537/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-455423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c100 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((219823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -843227/2500000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 100
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t100 : ((219772780227/10000000000000 : ℚ) : ℝ) ≤ stT136 100 := by
  have hc : ((219773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219772780227/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((219773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c101 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2557/2500000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 100
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t101 : ((497489643927/5000000000000 : ℚ) : ℝ) ≤ stT136 101 := by
  have hc : ((499971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497489643927/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((499971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c102 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((224853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 336001/1000000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 100
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t102 : ((222588016041/10000000000000 : ℚ) : ℝ) ≤ stT136 102 := by
  have hc : ((224803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222588016041/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((224803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c103 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-111403/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1669271/2500000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 100
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t103 : ((-43909950521/500000000000 : ℚ) : ℝ) ≤ stT136 103 := by
  have hc : ((-445637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43909950521/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-445637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c104 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-83129/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2872917/5000000) (δ := 109/15625000) (ψ := -666227/1000000) 136 101
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t104 : ((-326083386321/5000000000000 : ℚ) : ℝ) ≤ stT136 104 := by
  have hc : ((-332541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326083386321/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-332541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c105 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((135731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -623051/2500000) (δ := 109/15625000) (ψ := -666227/1000000) 136 101
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t105 : ((2648953683/50000000000 : ℚ) : ℝ) ≤ stT136 105 := by
  have hc : ((271437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2648953683/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((271437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c106 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((478803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365277/5000000) (δ := 109/15625000) (ψ := -666227/1000000) 136 101
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t106 : ((46502988973/500000000000 : ℚ) : ℝ) ≤ stT136 106 := by
  have hc : ((239389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46502988973/500000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((239389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c107 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1961543/5000000) (δ := 109/15625000) (ψ := -666227/1000000) 136 101
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t107 : ((11419569/78125000000 : ℚ) : ℝ) ≤ stT136 107 := by
  have hc : ((189/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11419569/78125000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((189/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c108 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-476587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3542951/5000000) (δ := 109/15625000) (ψ := -666227/1000000) 136 101
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t108 : ((-114655093403/1250000000000 : ℚ) : ℝ) ≤ stT136 108 := by
  have hc : ((-119153/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114655093403/1250000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-119153/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c109 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-584749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5488417/10000000) (δ := 6869/1000000000) (ψ := -666227/1000000) 136 102
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t109 : ((-560136271773/10000000000000 : ℚ) : ℝ) ≤ stT136 109 := by
  have hc : ((-584799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560136271773/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-584799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c110 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((578957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383367/10000000) (δ := 6869/1000000000) (ψ := -666227/1000000) 136 102
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t110 : ((275982913017/5000000000000 : ℚ) : ℝ) ≤ stT136 110 := by
  have hc : ((578907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275982913017/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((578907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c111 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((6011/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693599/10000000) (δ := 6869/1000000000) (ψ := -666227/1000000) 136 102
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t111 : ((91281377847/1000000000000 : ℚ) : ℝ) ≤ stT136 111 := by
  have hc : ((96171/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91281377847/1000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((96171/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c112 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((73561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3742923/10000000) (δ := 6869/1000000000) (ψ := -666227/1000000) 136 102
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t112 : ((69461352521/10000000000000 : ℚ) : ℝ) ≤ stT136 112 := by
  have hc : ((73511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69461352521/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((73511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c113 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-906651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6765183/10000000) (δ := 6869/1000000000) (ψ := -666227/1000000) 136 102
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t113 : ((-852952671421/10000000000000 : ℚ) : ℝ) ≤ stT136 113 := by
  have hc : ((-906701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852952671421/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-906701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c114 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-361479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -743397/1250000) (δ := 6841/1000000000) (ψ := -666227/1000000) 136 103
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t114 : ((-5290306021/78125000000 : ℚ) : ℝ) ≤ stT136 114 := by
  have hc : ((-11297/15625 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5290306021/78125000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-11297/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c115 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((7413/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1488859/5000000) (δ := 6841/1000000000) (ψ := -666227/1000000) 136 103
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t115 : ((215991239/6250000000 : ℚ) : ℝ) ≤ stT136 115 := by
  have hc : ((1853/5000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215991239/6250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((1853/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c116 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((249977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16999/5000000) (δ := 6841/1000000000) (ψ := -666227/1000000) 136 103
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t116 : ((116043019551/1250000000000 : ℚ) : ℝ) ≤ stT136 116 := by
  have hc : ((499929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116043019551/1250000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((499929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c117 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((202509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1442247/5000000) (δ := 6841/1000000000) (ψ := -666227/1000000) 136 103
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t117 : ((93598229/2500000000 : ℚ) : ℝ) ≤ stT136 117 := by
  have hc : ((50621/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93598229/2500000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((50621/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c118 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-5397/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1444533/2500000) (δ := 6841/1000000000) (ψ := -666227/1000000) 136 103
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t118 : ((-993742301/16000000000 : ℚ) : ℝ) ≤ stT136 118 := by
  have hc : ((-26987/40000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-993742301/16000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-26987/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c119 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-95007/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7060639/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 104
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t119 : ((-21774351347/250000000000 : ℚ) : ℝ) ≤ stT136 119 := by
  have hc : ((-23753/25000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21774351347/250000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-23753/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c120 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-23023/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4215417/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 104
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t120 : ((-21026157743/2000000000000 : ℚ) : ℝ) ≤ stT136 120 := by
  have hc : ((-23033/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21026157743/2000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-23033/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c121 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((169713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55753/400000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 104
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t121 : ((15427530027/200000000000 : ℚ) : ℝ) ≤ stT136 121 := by
  have hc : ((169703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15427530027/200000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((169703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c122 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((52893/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 280909/2000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 104
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t122 : ((383073748483/5000000000000 : ℚ) : ℝ) ≤ stT136 122 := by
  have hc : ((423119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383073748483/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((423119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c123 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-50529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4180067/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 104
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t123 : ((-2279151259/250000000000 : ℚ) : ℝ) ≤ stT136 123 := by
  have hc : ((-25277/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2279151259/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-25277/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c124 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-233231/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1386623/2000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 104
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t124 : ((-418917921149/5000000000000 : ℚ) : ℝ) ≤ stT136 124 := by
  have hc : ((-466487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418917921149/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-466487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c125 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-749141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6043901/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 105
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t125 : ((-167524351937/2500000000000 : ℚ) : ℝ) ≤ stT136 125 := by
  have hc : ((-749191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167524351937/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-749191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c126 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((234701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3334713/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 105
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t126 : ((20904353637/1000000000000 : ℚ) : ℝ) ≤ stT136 126 := by
  have hc : ((234651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20904353637/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((234651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c127 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((9667/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -646979/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 105
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t127 : ((4288813387/50000000000 : ℚ) : ℝ) ≤ stT136 127 := by
  have hc : ((19333/20000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4288813387/50000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((19333/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c128 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((69103/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2019709/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 105
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t128 : ((30537273767/500000000000 : ℚ) : ℝ) ≤ stT136 128 := by
  have hc : ((34549/50000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30537273767/500000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((34549/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c129 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-145593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4665657/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 105
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t129 : ((-64104756859/2500000000000 : ℚ) : ℝ) ≤ stT136 129 := by
  have hc : ((-72809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64104756859/2500000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-72809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c130 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-974763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7291137/10000000) (δ := 1737/250000000) (ψ := -666227/1000000) 136 105
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t130 : ((-854968514967/10000000000000 : ℚ) : ℝ) ≤ stT136 130 := by
  have hc : ((-974813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-854968514967/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-974813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c131 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-684399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72643/125000) (δ := 171/25000000) (ψ := -666227/1000000) 136 106
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t131 : ((-119601302709/2000000000000 : ℚ) : ℝ) ≤ stT136 131 := by
  have hc : ((-684449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119601302709/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-684449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c132 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((17299/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -806469/2500000) (δ := 171/25000000) (ψ := -666227/1000000) 136 106
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t132 : ((30108244099/1250000000000 : ℚ) : ℝ) ≤ stT136 132 := by
  have hc : ((138367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30108244099/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((138367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c133 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((241343/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164957/2500000) (δ := 171/25000000) (ψ := -666227/1000000) 136 106
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t133 : ((418519697049/5000000000000 : ℚ) : ℝ) ≤ stT136 133 := by
  have hc : ((482661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418519697049/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((482661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c134 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((728411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1886993/10000000) (δ := 341/25000000) (ψ := -666227/1000000) 136 106
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t134 : ((157301940087/2500000000000 : ℚ) : ℝ) ≤ stT136 134 := by
  have hc : ((728361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157301940087/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((728361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c135 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-96959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1103719/2500000) (δ := 171/25000000) (ψ := -666227/1000000) 136 106
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t135 : ((-10433817549/625000000000 : ℚ) : ℝ) ≤ stT136 135 := by
  have hc : ((-12123/62500 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10433817549/625000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-12123/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c136 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-931621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 692411/1000000) (δ := 171/25000000) (ψ := -666227/1000000) 136 106
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t136 : ((-798901360803/10000000000000 : ℚ) : ℝ) ≤ stT136 136 := by
  have hc : ((-931671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-798901360803/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-931671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c137 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-811313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6292979/10000000) (δ := 687/100000000) (ψ := -666227/1000000) 136 107
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t137 : ((-346597234977/5000000000000 : ℚ) : ℝ) ≤ stT136 137 := by
  have hc : ((-811363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346597234977/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-811363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c138 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((42679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3820261/10000000) (δ := 687/100000000) (ψ := -666227/1000000) 136 107
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t138 : ((4536024003/1250000000000 : ℚ) : ℝ) ≤ stT136 138 := by
  have hc : ((42629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4536024003/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((42629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c139 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((427267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1365359/10000000) (δ := 687/100000000) (ψ := -666227/1000000) 136 107
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t139 : ((45297692187/625000000000 : ℚ) : ℝ) ≤ stT136 139 := by
  have hc : ((213621/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45297692187/625000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((213621/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c140 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((909477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1071931/10000000) (δ := 687/100000000) (ψ := -666227/1000000) 136 107
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t140 : ((384302933379/5000000000000 : ℚ) : ℝ) ≤ stT136 140 := by
  have hc : ((909427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384302933379/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((909427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c141 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((8659/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3491847/10000000) (δ := 687/100000000) (ψ := -666227/1000000) 136 107
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t141 : ((14580160263/1000000000000 : ℚ) : ℝ) ≤ stT136 141 := by
  have hc : ((17313/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14580160263/1000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((17313/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c142 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-88537/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1178939/2000000) (δ := 687/100000000) (ψ := -666227/1000000) 136 107
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t142 : ((-148607803243/2500000000000 : ℚ) : ℝ) ≤ stT136 142 := by
  have hc : ((-354173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148607803243/2500000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-354173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c143 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-98547/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1856821/2500000) (δ := 6977/1000000000) (ψ := -666227/1000000) 136 108
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t143 : ((-10301677517/125000000000 : ℚ) : ℝ) ≤ stT136 143 := by
  have hc : ((-12319/12500 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10301677517/125000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-12319/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c144 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-218557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126449/250000) (δ := 6977/1000000000) (ψ := -666227/1000000) 136 108
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t144 : ((-45537953097/1250000000000 : ℚ) : ℝ) ≤ stT136 144 := by
  have hc : ((-109291/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45537953097/1250000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-109291/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c145 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((469567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270499/1000000) (δ := 6977/1000000000) (ψ := -666227/1000000) 136 108
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t145 : ((194956135359/5000000000000 : ℚ) : ℝ) ≤ stT136 145 := by
  have hc : ((469517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194956135359/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((469517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c146 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((494587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92051/2500000) (δ := 6977/1000000000) (ψ := -666227/1000000) 136 108
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t146 : ((40930198401/500000000000 : ℚ) : ℝ) ≤ stT136 146 := by
  have hc : ((247281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40930198401/500000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((247281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c147 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((710181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976301/5000000) (δ := 6977/1000000000) (ψ := -666227/1000000) 136 108
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t147 : ((292853053483/5000000000000 : ℚ) : ℝ) ≤ stT136 147 := by
  have hc : ((710131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292853053483/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((710131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c148 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-65949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42577/100000) (δ := 6977/1000000000) (ψ := -666227/1000000) 136 108
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t148 : ((-5423029813/500000000000 : ℚ) : ℝ) ≤ stT136 148 := by
  have hc : ((-32987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5423029813/500000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-32987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c149 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-866487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3273647/5000000) (δ := 6977/1000000000) (ψ := -666227/1000000) 136 108
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t149 : ((-22184213737/312500000000 : ℚ) : ℝ) ≤ stT136 149 := by
  have hc : ((-866537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22184213737/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-866537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c150 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-23151/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1721611/2500000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 109
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t150 : ((-75614970673/1000000000000 : ℚ) : ℝ) ≤ stT136 150 := by
  have hc : ((-92609/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75614970673/1000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-92609/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c151 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-276467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57841/125000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 109
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t151 : ((-225026492913/10000000000000 : ℚ) : ℝ) ≤ stT136 151 := by
  have hc : ((-276517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225026492913/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-276517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c152 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((579063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1191521/5000000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 109
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t152 : ((469641497391/10000000000000 : ℚ) : ℝ) ≤ stT136 152 := by
  have hc : ((579013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469641497391/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((579013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c153 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((199623/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76763/5000000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 109
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t153 : ((40344382269/500000000000 : ℚ) : ℝ) ≤ stT136 153 := by
  have hc : ((199613/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40344382269/500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((199613/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c154 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((678859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64421/312500) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 109
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t154 : ((273499612999/5000000000000 : ℚ) : ℝ) ≤ stT136 154 := by
  have hc : ((678809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273499612999/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((678809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c155 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-133651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2131061/5000000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 109
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t155 : ((-5369565861/500000000000 : ℚ) : ℝ) ≤ stT136 155 := by
  have hc : ((-133701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5369565861/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-133701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c156 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-211529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1612157/2500000) (δ := 6919/1000000000) (ψ := -666227/1000000) 136 109
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t156 : ((-338737596203/5000000000000 : ℚ) : ℝ) ≤ stT136 156 := by
  have hc : ((-423083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338737596203/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-423083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c157 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-953283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7086803/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t157 : ((-760842673971/10000000000000 : ℚ) : ℝ) ≤ stT136 157 := by
  have hc : ((-953333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-760842673971/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-953333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c158 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-194909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197123/400000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t158 : ((-38770325793/1250000000000 : ℚ) : ℝ) ≤ stT136 158 := by
  have hc : ((-97467/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38770325793/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-97467/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c159 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((110453/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2782947/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t159 : ((175169897931/5000000000000 : ℚ) : ℝ) ≤ stT136 159 := by
  have hc : ((220881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175169897931/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((220881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c160 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((483129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -651283/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t160 : ((11935220193/156250000000 : ℚ) : ℝ) ≤ stT136 160 := by
  have hc : ((15097/15625 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11935220193/156250000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((15097/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c161 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((416349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1467087/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t161 : ((8202727691/125000000000 : ℚ) : ℝ) ≤ stT136 161 := by
  have hc : ((104081/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8202727691/125000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((104081/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c162 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((70687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3572367/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t162 : ((13879324047/1250000000000 : ℚ) : ℝ) ≤ stT136 162 := by
  have hc : ((35331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13879324047/1250000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((35331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c163 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-10007/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5664693/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t163 : ((-250838551989/5000000000000 : ℚ) : ℝ) ≤ stT136 163 := by
  have hc : ((-320249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250838551989/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-320249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c164 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-249759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7744201/10000000) (δ := 1703/250000000) (ψ := -666227/1000000) 136 110
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t164 : ((-390077642867/5000000000000 : ℚ) : ℝ) ≤ stT136 164 := by
  have hc : ((-499543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390077642867/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-499543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c165 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-708919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2948451/5000000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 111
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t165 : ((-551931657531/10000000000000 : ℚ) : ℝ) ≤ stT136 165 := by
  have hc : ((-708969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551931657531/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-708969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c166 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((16891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96063/250000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 111
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t166 : ((130905459/50000000000 : ℚ) : ℝ) ≤ stT136 166 := by
  have hc : ((8433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130905459/50000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((8433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c167 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((93961/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900223/5000000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 111
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t167 : ((290817386037/5000000000000 : ℚ) : ℝ) ≤ stT136 167 := by
  have hc : ((375819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290817386037/5000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((375819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c168 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((995793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57347/2500000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 111
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t168 : ((192057914097/2500000000000 : ℚ) : ℝ) ≤ stT136 168 := by
  have hc : ((995743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192057914097/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((995743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c169 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((622481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 112361/500000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 111
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t169 : ((47879259813/1000000000000 : ℚ) : ℝ) ≤ stT136 169 := by
  have hc : ((622431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47879259813/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((622431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c170 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-130081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2126559/5000000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 111
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t170 : ((-19961184483/2000000000000 : ℚ) : ℝ) ≤ stT136 170 := by
  have hc : ((-130131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19961184483/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-130131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c171 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-160097/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1561813/2500000) (δ := 3449/500000000) (ψ := -666227/1000000) 136 111
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t171 : ((-1530462813/25000000000 : ℚ) : ℝ) ≤ stT136 171 := by
  have hc : ((-160107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1530462813/25000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-160107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c172 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-39549/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3739103/5000000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t172 : ((-30157360643/400000000000 : ℚ) : ℝ) ≤ stT136 172 := by
  have hc : ((-39551/40000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30157360643/400000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-39551/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c173 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-23633/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -688399/1250000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t173 : ((-1796935961/40000000000 : ℚ) : ℝ) ≤ stT136 173 := by
  have hc : ((-4727/8000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1796935961/40000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-4727/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c174 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((151201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1773767/5000000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t174 : ((57293635399/5000000000000 : ℚ) : ℝ) ≤ stT136 174 := by
  have hc : ((151151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57293635399/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((151151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c175 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((100289/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199887/1250000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t175 : ((37903269321/625000000000 : ℚ) : ℝ) ≤ stT136 175 := by
  have hc : ((401131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37903269321/625000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((401131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c176 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((495431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21139/625000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t176 : ((93356535967/1250000000000 : ℚ) : ℝ) ≤ stT136 176 := by
  have hc : ((247703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93356535967/1250000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((247703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c177 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((308513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 566149/2500000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t177 : ((14492110703/312500000000 : ℚ) : ℝ) ≤ stT136 177 := by
  have hc : ((38561/62500 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14492110703/312500000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((38561/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c178 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-50533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 522511/1250000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t178 : ((-4736854857/625000000000 : ℚ) : ℝ) ≤ stT136 178 := by
  have hc : ((-25279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4736854857/625000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-25279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c179 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-151979/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608487/1000000) (δ := 6997/1000000000) (ψ := -666227/1000000) 136 112
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t179 : ((-28400512551/500000000000 : ℚ) : ℝ) ≤ stT136 179 := by
  have hc : ((-151989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28400512551/500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-151989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c180 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-799/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7728953/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t180 : ((-465288483/6250000000 : ℚ) : ℝ) ≤ stT136 180 := by
  have hc : ((-2497/2500 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465288483/6250000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-2497/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c181 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-694207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1169057/2000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t181 : ((-103207551363/2000000000000 : ℚ) : ℝ) ≤ stT136 181 := by
  have hc : ((-694257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103207551363/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-694257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c182 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-18011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3972021/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t182 : ((-10710173/8000000000 : ℚ) : ℝ) ≤ stT136 182 := by
  have hc : ((-18061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10710173/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-18061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c183 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((33239/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108991/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t183 : ((49138237533/1000000000000 : ℚ) : ℝ) ≤ stT136 183 := by
  have hc : ((66473/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49138237533/1000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((66473/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c184 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((994757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256127/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t184 : ((733306952763/10000000000000 : ℚ) : ℝ) ≤ stT136 184 := by
  have hc : ((994707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((733306952763/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((994707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c185 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((40263/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1586707/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t185 : ((29600083247/500000000000 : ℚ) : ℝ) ≤ stT136 185 := by
  have hc : ((80521/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29600083247/500000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((80521/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c186 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((100787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3419579/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t186 : ((7388222507/500000000000 : ℚ) : ℝ) ≤ stT136 186 := by
  have hc : ((50381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7388222507/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((50381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c187 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-502309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5242659/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t187 : ((-367361573007/10000000000000 : ℚ) : ℝ) ≤ stT136 187 := by
  have hc : ((-502359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367361573007/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-502359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c188 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-949487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7055981/10000000) (δ := 689/100000000) (ψ := -666227/1000000) 136 113
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t188 : ((-27700842901/400000000000 : ℚ) : ℝ) ≤ stT136 188 := by
  have hc : ((-949537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27700842901/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-949537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c189 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-184033/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -856031/1250000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t189 : ((-133871589899/2000000000000 : ℚ) : ℝ) ≤ stT136 189 := by
  have hc : ((-184043/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133871589899/2000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-184043/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c190 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-217857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263517/2500000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t190 : ((-79034189857/2500000000000 : ℚ) : ℝ) ≤ stT136 190 := by
  have hc : ((-108941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79034189857/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-108941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c191 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((260063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -408659/1250000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t191 : ((94069323231/5000000000000 : ℚ) : ℝ) ≤ stT136 191 := by
  have hc : ((260013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94069323231/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((260013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c192 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((103341/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -746913/5000000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t192 : ((298301382893/5000000000000 : ℚ) : ℝ) ≤ stT136 192 := by
  have hc : ((413339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298301382893/5000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((413339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c193 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((994069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136203/5000000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t193 : ((143101957297/2000000000000 : ℚ) : ℝ) ≤ stT136 193 := by
  have hc : ((994019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143101957297/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((994019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c194 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((344093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1014763/5000000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t194 : ((30878296643/625000000000 : ℚ) : ℝ) ≤ stT136 194 := by
  have hc : ((86017/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30878296643/625000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((86017/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c195 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((1493/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1888801/5000000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t195 : ((2136526119/500000000000 : ℚ) : ℝ) ≤ stT136 195 := by
  have hc : ((5967/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2136526119/500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((5967/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c196 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-5939/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86199/156250) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t196 : ((-4242501697/100000000000 : ℚ) : ℝ) ≤ stT136 196 := by
  have hc : ((-11879/20000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4242501697/100000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-11879/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c197 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-970673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724703/1000000) (δ := 341/50000000) (ψ := -666227/1000000) 136 114
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t197 : ((-691611986533/10000000000000 : ℚ) : ℝ) ≤ stT136 197 := by
  have hc : ((-970723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-691611986533/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-970723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c198 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-451127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6739411/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t198 : ((-2003876199/31250000000 : ℚ) : ℝ) ≤ stT136 198 := by
  have hc : ((-28197/31250 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2003876199/31250000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-28197/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c199 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-425783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5026559/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t199 : ((-150932674353/5000000000000 : ℚ) : ℝ) ≤ stT136 199 := by
  have hc : ((-425833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150932674353/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-425833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c200 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((239521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3322309/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t200 : ((84665690463/5000000000000 : ℚ) : ℝ) ≤ stT136 200 := by
  have hc : ((239471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84665690463/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((239471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c201 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((397857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65061/400000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t201 : ((7015220301/125000000000 : ℚ) : ℝ) ≤ stT136 201 := by
  have hc : ((49729/62500 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7015220301/125000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((49729/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c202 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((124963/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60793/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t202 : ((351676777719/5000000000000 : ℚ) : ℝ) ≤ stT136 202 := by
  have hc : ((499827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351676777719/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((499827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c203 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((38373/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 347963/2000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t203 : ((26930795871/500000000000 : ℚ) : ℝ) ≤ stT136 203 := by
  have hc : ((76741/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26930795871/500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((76741/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c204 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((2051/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136423/400000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t204 : ((143563707/10000000000 : ℚ) : ℝ) ≤ stT136 204 := by
  have hc : ((4101/20000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143563707/10000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((4101/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c205 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-22129/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202927/400000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t205 : ((-30914651353/1000000000000 : ℚ) : ℝ) ≤ stT136 205 := by
  have hc : ((-44263/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30914651353/1000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-44263/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c206 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-900221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6727683/10000000) (δ := 6927/1000000000) (ψ := -666227/1000000) 136 115
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t206 : ((-313624707457/5000000000000 : ℚ) : ℝ) ≤ stT136 206 := by
  have hc : ((-900271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313624707457/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-900271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c207 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-978431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7333797/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t207 : ((-680092240569/10000000000000 : ℚ) : ℝ) ≤ stT136 207 := by
  have hc : ((-978481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-680092240569/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-978481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c208 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-324891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139047/2000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t208 : ((-440017493/9765625000 : ℚ) : ℝ) ≤ stT136 208 := by
  have hc : ((-81229/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-440017493/9765625000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-81229/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c209 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-54987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4064527/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t209 : ((-7613983691/2000000000000 : ℚ) : ℝ) ≤ stT136 209 := by
  have hc : ((-55037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7613983691/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-55037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c210 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((8747/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488321/2000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t210 : ((38626940427/1000000000000 : ℚ) : ℝ) ≤ stT136 210 := by
  have hc : ((279879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38626940427/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((279879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c211 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((945861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -826401/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t211 : ((162780693777/2500000000000 : ℚ) : ℝ) ≤ stT136 211 := by
  have hc : ((945811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162780693777/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((945811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c212 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((47579/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 781153/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t212 : ((32675635353/500000000000 : ℚ) : ℝ) ≤ stT136 212 := by
  have hc : ((95153/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32675635353/500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((95153/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c213 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((579677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2381159/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t213 : ((99288366219/2500000000000 : ℚ) : ℝ) ≤ stT136 213 := by
  have hc : ((579627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99288366219/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((579627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c214 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-18677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 794737/2000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t214 : ((-6400757511/5000000000000 : ℚ) : ℝ) ≤ stT136 214 := by
  have hc : ((-18727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6400757511/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-18727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c215 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-607341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1111753/2000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t215 : ((-82847525009/2000000000000 : ℚ) : ℝ) ≤ stT136 215 := by
  have hc : ((-607391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82847525009/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-607391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c216 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-9591/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7136501/10000000) (δ := 6969/1000000000) (ψ := -666227/1000000) 136 116
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t216 : ((-6526190881/100000000000 : ℚ) : ℝ) ≤ stT136 216 := by
  have hc : ((-19183/20000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6526190881/100000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-19183/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c217 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-942361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1750259/2500000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t217 : ((-127950199059/2000000000000 : ℚ) : ℝ) ≤ stT136 217 := by
  have hc : ((-942411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127950199059/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-942411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c218 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-142053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2718909/5000000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t218 : ((-96218974233/2500000000000 : ℚ) : ℝ) ≤ stT136 218 := by
  have hc : ((-284131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96218974233/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-284131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c219 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((18099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194087/500000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t219 : ((12196377113/10000000000000 : ℚ) : ℝ) ≤ stT136 219 := by
  have hc : ((18049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12196377113/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((18049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c220 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((29767/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72899/312500) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t220 : ((40134392271/1000000000000 : ℚ) : ℝ) ≤ stT136 220 := by
  have hc : ((59529/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40134392271/1000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((59529/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c221 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((950387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1977/25000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t221 : ((19977034077/312500000000 : ℚ) : ℝ) ≤ stT136 221 := by
  have hc : ((950337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19977034077/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((950337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c222 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((119503/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186041/2500000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t222 : ((80200960743/1250000000000 : ℚ) : ℝ) ≤ stT136 222 := by
  have hc : ((477987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80200960743/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((477987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c223 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((614611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113613/500000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t223 : ((411540159089/10000000000000 : ℚ) : ℝ) ≤ stT136 223 := by
  have hc : ((614561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411540159089/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((614561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c224 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((26681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1896761/5000000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t224 : ((556571449/156250000000 : ℚ) : ℝ) ≤ stT136 224 := by
  have hc : ((833/15625 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((556571449/156250000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((833/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c225 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-524741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2654009/5000000) (δ := 6861/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t225 : ((-349860841597/10000000000000 : ℚ) : ℝ) ≤ stT136 225 := by
  have hc : ((-524791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349860841597/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-524791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c226 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-915001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1363153/2000000) (δ := 13661/1000000000) (ψ := -666227/1000000) 136 117
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t226 : ((-608683689741/10000000000000 : ℚ) : ℝ) ≤ stT136 226 := by
  have hc : ((-915051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-608683689741/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-915051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c227 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-982907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7391081/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t227 : ((-163103037967/2500000000000 : ℚ) : ℝ) ≤ stT136 227 := by
  have hc : ((-982957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163103037967/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-982957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c228 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-708827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5896577/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t228 : ((-469465844159/10000000000000 : ℚ) : ℝ) ≤ stT136 228 := by
  have hc : ((-708877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469465844159/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-708877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c229 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-38291/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4408601/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t229 : ((-25310028519/2000000000000 : ℚ) : ℝ) ≤ stT136 229 := by
  have hc : ((-38301/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25310028519/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-38301/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c230 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((389371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2927119/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t230 : ((12835524049/500000000000 : ℚ) : ℝ) ≤ stT136 230 := by
  have hc : ((389321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12835524049/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((389321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c231 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((83601/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1452063/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t231 : ((13750517949/250000000000 : ℚ) : ℝ) ≤ stT136 231 := by
  have hc : ((20899/25000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13750517949/250000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((20899/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c232 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((499989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16601/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t232 : ((20515147803/312500000000 : ℚ) : ℝ) ≤ stT136 232 := by
  have hc : ((124991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20515147803/312500000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((124991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c233 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((166011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59159/400000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t233 : ((108750741121/2000000000000 : ℚ) : ℝ) ≤ stT136 233 := by
  have hc : ((166001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108750741121/2000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((166001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c234 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((386431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2935093/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t234 : ((6314624683/250000000000 : ℚ) : ℝ) ≤ stT136 234 := by
  have hc : ((386381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6314624683/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((386381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c235 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-5693/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4384989/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t235 : ((-59435652177/5000000000000 : ℚ) : ℝ) ≤ stT136 235 := by
  have hc : ((-91113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59435652177/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-91113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c236 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-344713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5828731/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t236 : ((-22440547741/500000000000 : ℚ) : ℝ) ≤ stT136 236 := by
  have hc : ((-172369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22440547741/500000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-172369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c237 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-486251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7266353/10000000) (δ := 6849/1000000000) (ψ := -666227/1000000) 136 118
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t237 : ((-7896757533/125000000000 : ℚ) : ℝ) ≤ stT136 237 := by
  have hc : ((-121569/125000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7896757533/125000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-121569/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c238 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-23589/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175251/250000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t238 : ((-15291294411/250000000000 : ℚ) : ℝ) ≤ stT136 238 := by
  have hc : ((-94361/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15291294411/250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-94361/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c239 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-38467/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2792227/5000000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t239 : ((-199074279567/5000000000000 : ℚ) : ℝ) ≤ stT136 239 := by
  have hc : ((-307761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199074279567/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-307761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c240 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-94987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2082409/5000000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t240 : ((-30673096713/5000000000000 : ℚ) : ℝ) ≤ stT136 240 := by
  have hc : ((-95037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30673096713/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-95037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c241 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((90641/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1375549/5000000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t241 : ((14595125609/500000000000 : ℚ) : ℝ) ≤ stT136 241 := by
  have hc : ((90631/200000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14595125609/500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((90631/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c242 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((859099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671613/5000000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t242 : ((69027164297/1250000000000 : ℚ) : ℝ) ≤ stT136 242 := by
  have hc : ((859049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69027164297/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((859049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c243 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((999723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3677/625000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t243 : ((1282580459/20000000000 : ℚ) : ℝ) ≤ stT136 243 := by
  have hc : ((999673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1282580459/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((999673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c244 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((835333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181893/1250000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t244 : ((66841851509/1250000000000 : ℚ) : ℝ) ≤ stT136 244 := by
  have hc : ((835283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66841851509/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((835283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c245 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((419147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2845727/10000000) (δ := 3439/250000000) (ψ := -666227/1000000) 136 119
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t245 : ((66937753743/2500000000000 : ℚ) : ℝ) ≤ stT136 245 := by
  have hc : ((419097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66937753743/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((419097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c246 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-30293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2115333/5000000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t246 : ((-38644179547/5000000000000 : ℚ) : ℝ) ≤ stT136 246 := by
  have hc : ((-60611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38644179547/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-60611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c247 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-623487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2804989/5000000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t247 : ((-79349448009/2000000000000 : ℚ) : ℝ) ≤ stT136 247 := by
  have hc : ((-623537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79349448009/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-623537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c248 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-47001/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3491857/5000000) (δ := 1739/250000000) (ψ := -666227/1000000) 136 119
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t248 : ((-59694539007/1000000000000 : ℚ) : ℝ) ≤ stT136 248 := by
  have hc : ((-94007/100000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59694539007/1000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-94007/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c249 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-980231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -919507/1250000) (δ := 347/50000000) (ψ := -666227/1000000) 136 120
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t249 : ((-24849143069/400000000000 : ℚ) : ℝ) ≤ stT136 249 := by
  have hc : ((-980281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24849143069/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-980281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_c250 :
    |Real.cos (((136 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-735581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2996651/5000000) (δ := 347/50000000) (ψ := -666227/1000000) 136 120
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st136_t250 : ((-58156779967/1250000000000 : ℚ) : ℝ) ≤ stT136 250 := by
  have hc : ((-735631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((136 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st136_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58156779967/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-735631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st136_p1 : ((786109/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT136 (i+1) := by
  rw [Finset.sum_range_one]
  exact st136_t1

theorem st136_p2 : ((2666034283163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT136 (i+1))
      = (∑ i ∈ Finset.range 1, stT136 (i+1)) + stT136 2 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 1
    simpa using h
  have hprev := st136_p1
  have hstep := st136_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p3 : ((3534882825641/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT136 (i+1))
      = (∑ i ∈ Finset.range 2, stT136 (i+1)) + stT136 3 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 2
    simpa using h
  have hprev := st136_p2
  have hstep := st136_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p4 : ((4295341825641/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT136 (i+1))
      = (∑ i ∈ Finset.range 3, stT136 (i+1)) + stT136 4 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 3
    simpa using h
  have hprev := st136_p3
  have hstep := st136_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p5 : ((513185199411/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT136 (i+1))
      = (∑ i ∈ Finset.range 4, stT136 (i+1)) + stT136 5 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 4
    simpa using h
  have hprev := st136_p4
  have hstep := st136_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p6 : ((2878488983939/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT136 (i+1))
      = (∑ i ∈ Finset.range 5, stT136 (i+1)) + stT136 6 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 5
    simpa using h
  have hprev := st136_p5
  have hstep := st136_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p7 : ((14683301754249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT136 (i+1))
      = (∑ i ∈ Finset.range 6, stT136 (i+1)) + stT136 7 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 6
    simpa using h
  have hprev := st136_p6
  have hstep := st136_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p8 : ((8002054853961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT136 (i+1))
      = (∑ i ∈ Finset.range 7, stT136 (i+1)) + stT136 8 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 7
    simpa using h
  have hprev := st136_p7
  have hstep := st136_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p9 : ((1515668287177/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT136 (i+1))
      = (∑ i ∈ Finset.range 8, stT136 (i+1)) + stT136 9 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 8
    simpa using h
  have hprev := st136_p8
  have hstep := st136_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p10 : ((33292904242541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT136 (i+1))
      = (∑ i ∈ Finset.range 9, stT136 (i+1)) + stT136 10 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 9
    simpa using h
  have hprev := st136_p9
  have hstep := st136_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p11 : ((36303416180103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT136 (i+1))
      = (∑ i ∈ Finset.range 10, stT136 (i+1)) + stT136 11 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 10
    simpa using h
  have hprev := st136_p10
  have hstep := st136_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p12 : ((19275348492667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT136 (i+1))
      = (∑ i ∈ Finset.range 11, stT136 (i+1)) + stT136 12 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 11
    simpa using h
  have hprev := st136_p11
  have hstep := st136_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p13 : ((36583827148669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT136 (i+1))
      = (∑ i ∈ Finset.range 12, stT136 (i+1)) + stT136 13 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 12
    simpa using h
  have hprev := st136_p12
  have hstep := st136_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p14 : ((36941633770617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT136 (i+1))
      = (∑ i ∈ Finset.range 13, stT136 (i+1)) + stT136 14 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 13
    simpa using h
  have hprev := st136_p13
  have hstep := st136_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p15 : ((9122306351001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT136 (i+1))
      = (∑ i ∈ Finset.range 14, stT136 (i+1)) + stT136 15 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 14
    simpa using h
  have hprev := st136_p14
  have hstep := st136_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p16 : ((9580780726001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT136 (i+1))
      = (∑ i ∈ Finset.range 15, stT136 (i+1)) + stT136 16 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 15
    simpa using h
  have hprev := st136_p15
  have hstep := st136_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p17 : ((18060563365781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT136 (i+1))
      = (∑ i ∈ Finset.range 16, stT136 (i+1)) + stT136 17 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 16
    simpa using h
  have hprev := st136_p16
  have hstep := st136_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p18 : ((3496400757231/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT136 (i+1))
      = (∑ i ∈ Finset.range 17, stT136 (i+1)) + stT136 18 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 17
    simpa using h
  have hprev := st136_p17
  have hstep := st136_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p19 : ((4522051237341/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT136 (i+1))
      = (∑ i ∈ Finset.range 18, stT136 (i+1)) + stT136 19 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 18
    simpa using h
  have hprev := st136_p18
  have hstep := st136_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p20 : ((38297983560127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT136 (i+1))
      = (∑ i ∈ Finset.range 19, stT136 (i+1)) + stT136 20 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 19
    simpa using h
  have hprev := st136_p19
  have hstep := st136_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p21 : ((40479000641431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT136 (i+1))
      = (∑ i ∈ Finset.range 20, stT136 (i+1)) + stT136 21 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 20
    simpa using h
  have hprev := st136_p20
  have hstep := st136_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p22 : ((42604974061621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT136 (i+1))
      = (∑ i ∈ Finset.range 21, stT136 (i+1)) + stT136 22 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 21
    simpa using h
  have hprev := st136_p21
  have hstep := st136_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p23 : ((44662323092101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT136 (i+1))
      = (∑ i ∈ Finset.range 22, stT136 (i+1)) + stT136 23 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 22
    simpa using h
  have hprev := st136_p22
  have hstep := st136_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p24 : ((11569247917911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT136 (i+1))
      = (∑ i ∈ Finset.range 23, stT136 (i+1)) + stT136 24 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 23
    simpa using h
  have hprev := st136_p23
  have hstep := st136_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p25 : ((11659311917911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT136 (i+1))
      = (∑ i ∈ Finset.range 24, stT136 (i+1)) + stT136 25 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 24
    simpa using h
  have hprev := st136_p24
  have hstep := st136_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p26 : ((2829670648259/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT136 (i+1))
      = (∑ i ∈ Finset.range 25, stT136 (i+1)) + stT136 26 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 25
    simpa using h
  have hprev := st136_p25
  have hstep := st136_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p27 : ((43465304909439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT136 (i+1))
      = (∑ i ∈ Finset.range 26, stT136 (i+1)) + stT136 27 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 26
    simpa using h
  have hprev := st136_p26
  have hstep := st136_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p28 : ((43680357203929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT136 (i+1))
      = (∑ i ∈ Finset.range 27, stT136 (i+1)) + stT136 28 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 27
    simpa using h
  have hprev := st136_p27
  have hstep := st136_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p29 : ((22767252173973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT136 (i+1))
      = (∑ i ∈ Finset.range 28, stT136 (i+1)) + stT136 29 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 28
    simpa using h
  have hprev := st136_p28
  have hstep := st136_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p30 : ((22625510693803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT136 (i+1))
      = (∑ i ∈ Finset.range 29, stT136 (i+1)) + stT136 30 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 29
    simpa using h
  have hprev := st136_p29
  have hstep := st136_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p31 : ((4360288321083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT136 (i+1))
      = (∑ i ∈ Finset.range 30, stT136 (i+1)) + stT136 31 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 30
    simpa using h
  have hprev := st136_p30
  have hstep := st136_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p32 : ((22437533309663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT136 (i+1))
      = (∑ i ∈ Finset.range 31, stT136 (i+1)) + stT136 32 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 31
    simpa using h
  have hprev := st136_p31
  have hstep := st136_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p33 : ((22644354906223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT136 (i+1))
      = (∑ i ∈ Finset.range 32, stT136 (i+1)) + stT136 33 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 32
    simpa using h
  have hprev := st136_p32
  have hstep := st136_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p34 : ((4371742934933/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT136 (i+1))
      = (∑ i ∈ Finset.range 33, stT136 (i+1)) + stT136 34 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 33
    simpa using h
  have hprev := st136_p33
  have hstep := st136_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p35 : ((22640910617743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT136 (i+1))
      = (∑ i ∈ Finset.range 34, stT136 (i+1)) + stT136 35 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 34
    simpa using h
  have hprev := st136_p34
  have hstep := st136_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p36 : ((22246583872211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT136 (i+1))
      = (∑ i ∈ Finset.range 35, stT136 (i+1)) + stT136 36 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 35
    simpa using h
  have hprev := st136_p35
  have hstep := st136_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p37 : ((11085587436453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT136 (i+1))
      = (∑ i ∈ Finset.range 36, stT136 (i+1)) + stT136 37 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 36
    simpa using h
  have hprev := st136_p36
  have hstep := st136_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p38 : ((2826708881541/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT136 (i+1))
      = (∑ i ∈ Finset.range 37, stT136 (i+1)) + stT136 38 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 37
    simpa using h
  have hprev := st136_p37
  have hstep := st136_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p39 : ((4390804106101/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT136 (i+1))
      = (∑ i ∈ Finset.range 38, stT136 (i+1)) + stT136 39 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 38
    simpa using h
  have hprev := st136_p38
  have hstep := st136_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p40 : ((11354504195761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT136 (i+1))
      = (∑ i ∈ Finset.range 39, stT136 (i+1)) + stT136 40 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 39
    simpa using h
  have hprev := st136_p39
  have hstep := st136_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p41 : ((21930879460843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT136 (i+1))
      = (∑ i ∈ Finset.range 40, stT136 (i+1)) + stT136 41 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 40
    simpa using h
  have hprev := st136_p40
  have hstep := st136_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p42 : ((45402685681641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT136 (i+1))
      = (∑ i ∈ Finset.range 41, stT136 (i+1)) + stT136 42 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 41
    simpa using h
  have hprev := st136_p41
  have hstep := st136_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p43 : ((43886814522963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT136 (i+1))
      = (∑ i ∈ Finset.range 42, stT136 (i+1)) + stT136 43 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 42
    simpa using h
  have hprev := st136_p42
  have hstep := st136_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p44 : ((45387523203611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT136 (i+1))
      = (∑ i ∈ Finset.range 43, stT136 (i+1)) + stT136 44 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 43
    simpa using h
  have hprev := st136_p43
  have hstep := st136_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p45 : ((43896803750051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT136 (i+1))
      = (∑ i ∈ Finset.range 44, stT136 (i+1)) + stT136 45 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 44
    simpa using h
  have hprev := st136_p44
  have hstep := st136_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p46 : ((22678057189279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT136 (i+1))
      = (∑ i ∈ Finset.range 45, stT136 (i+1)) + stT136 46 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 45
    simpa using h
  have hprev := st136_p45
  have hstep := st136_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p47 : ((21995362312479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT136 (i+1))
      = (∑ i ∈ Finset.range 46, stT136 (i+1)) + stT136 47 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 46
    simpa using h
  have hprev := st136_p46
  have hstep := st136_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p48 : ((45150102603333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT136 (i+1))
      = (∑ i ∈ Finset.range 47, stT136 (i+1)) + stT136 48 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 47
    simpa using h
  have hprev := st136_p47
  have hstep := st136_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p49 : ((44348807997101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT136 (i+1))
      = (∑ i ∈ Finset.range 48, stT136 (i+1)) + stT136 49 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 48
    simpa using h
  have hprev := st136_p48
  have hstep := st136_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p50 : ((1785265910747/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT136 (i+1))
      = (∑ i ∈ Finset.range 49, stT136 (i+1)) + stT136 50 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 49
    simpa using h
  have hprev := st136_p49
  have hstep := st136_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p51 : ((8994796804447/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT136 (i+1))
      = (∑ i ∈ Finset.range 50, stT136 (i+1)) + stT136 51 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 50
    simpa using h
  have hprev := st136_p50
  have hstep := st136_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p52 : ((8806184800937/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT136 (i+1))
      = (∑ i ∈ Finset.range 51, stT136 (i+1)) + stT136 52 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 51
    simpa using h
  have hprev := st136_p51
  have hstep := st136_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p53 : ((2267698124191/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT136 (i+1))
      = (∑ i ∈ Finset.range 52, stT136 (i+1)) + stT136 53 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 52
    simpa using h
  have hprev := st136_p52
  have hstep := st136_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p54 : ((1377043193849/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT136 (i+1))
      = (∑ i ∈ Finset.range 53, stT136 (i+1)) + stT136 54 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 53
    simpa using h
  have hprev := st136_p53
  have hstep := st136_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p55 : ((560294634751/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT136 (i+1))
      = (∑ i ∈ Finset.range 54, stT136 (i+1)) + stT136 55 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 54
    simpa using h
  have hprev := st136_p54
  have hstep := st136_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p56 : ((22474377294927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT136 (i+1))
      = (∑ i ∈ Finset.range 55, stT136 (i+1)) + stT136 56 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 55
    simpa using h
  have hprev := st136_p55
  have hstep := st136_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p57 : ((10993195761267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT136 (i+1))
      = (∑ i ∈ Finset.range 56, stT136 (i+1)) + stT136 57 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 56
    simpa using h
  have hprev := st136_p56
  have hstep := st136_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p58 : ((2264251515963/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT136 (i+1))
      = (∑ i ∈ Finset.range 57, stT136 (i+1)) + stT136 58 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 57
    simpa using h
  have hprev := st136_p57
  have hstep := st136_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p59 : ((69416103561/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT136 (i+1))
      = (∑ i ∈ Finset.range 58, stT136 (i+1)) + stT136 59 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 58
    simpa using h
  have hprev := st136_p58
  have hstep := st136_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p60 : ((8850341132053/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT136 (i+1))
      = (∑ i ∈ Finset.range 59, stT136 (i+1)) + stT136 60 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 59
    simpa using h
  have hprev := st136_p59
  have hstep := st136_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p61 : ((45348783859593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT136 (i+1))
      = (∑ i ∈ Finset.range 60, stT136 (i+1)) + stT136 61 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 60
    simpa using h
  have hprev := st136_p60
  have hstep := st136_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p62 : ((44173402088601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT136 (i+1))
      = (∑ i ∈ Finset.range 61, stT136 (i+1)) + stT136 62 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 61
    simpa using h
  have hprev := st136_p61
  have hstep := st136_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p63 : ((44444188311931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT136 (i+1))
      = (∑ i ∈ Finset.range 62, stT136 (i+1)) + stT136 63 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 62
    simpa using h
  have hprev := st136_p62
  have hstep := st136_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p64 : ((45326022061931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT136 (i+1))
      = (∑ i ∈ Finset.range 63, stT136 (i+1)) + stT136 64 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 63
    simpa using h
  have hprev := st136_p63
  have hstep := st136_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p65 : ((44122765428523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT136 (i+1))
      = (∑ i ∈ Finset.range 64, stT136 (i+1)) + stT136 65 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 64
    simpa using h
  have hprev := st136_p64
  have hstep := st136_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p66 : ((44439393436743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT136 (i+1))
      = (∑ i ∈ Finset.range 65, stT136 (i+1)) + stT136 66 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 65
    simpa using h
  have hprev := st136_p65
  have hstep := st136_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p67 : ((9069195913681/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT136 (i+1))
      = (∑ i ∈ Finset.range 66, stT136 (i+1)) + stT136 67 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 66
    simpa using h
  have hprev := st136_p66
  have hstep := st136_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p68 : ((8845061304827/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT136 (i+1))
      = (∑ i ∈ Finset.range 67, stT136 (i+1)) + stT136 68 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 67
    simpa using h
  have hprev := st136_p67
  have hstep := st136_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p69 : ((44252289797347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT136 (i+1))
      = (∑ i ∈ Finset.range 68, stT136 (i+1)) + stT136 69 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 68
    simpa using h
  have hprev := st136_p68
  have hstep := st136_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p70 : ((45349096747687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT136 (i+1))
      = (∑ i ∈ Finset.range 69, stT136 (i+1)) + stT136 70 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 69
    simpa using h
  have hprev := st136_p69
  have hstep := st136_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p71 : ((44525570916157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT136 (i+1))
      = (∑ i ∈ Finset.range 70, stT136 (i+1)) + stT136 71 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 70
    simpa using h
  have hprev := st136_p70
  have hstep := st136_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p72 : ((43989035650477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT136 (i+1))
      = (∑ i ∈ Finset.range 71, stT136 (i+1)) + stT136 72 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 71
    simpa using h
  have hprev := st136_p71
  have hstep := st136_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p73 : ((22571501773169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT136 (i+1))
      = (∑ i ∈ Finset.range 72, stT136 (i+1)) + stT136 73 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 72
    simpa using h
  have hprev := st136_p72
  have hstep := st136_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p74 : ((22506484434559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT136 (i+1))
      = (∑ i ∈ Finset.range 73, stT136 (i+1)) + stT136 74 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 73
    simpa using h
  have hprev := st136_p73
  have hstep := st136_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p75 : ((5491877028223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT136 (i+1))
      = (∑ i ∈ Finset.range 74, stT136 (i+1)) + stT136 75 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 74
    simpa using h
  have hprev := st136_p74
  have hstep := st136_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p76 : ((22290063578797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT136 (i+1))
      = (∑ i ∈ Finset.range 75, stT136 (i+1)) + stT136 76 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 75
    simpa using h
  have hprev := st136_p75
  have hstep := st136_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p77 : ((11342619353311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT136 (i+1))
      = (∑ i ∈ Finset.range 76, stT136 (i+1)) + stT136 77 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 76
    simpa using h
  have hprev := st136_p76
  have hstep := st136_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p78 : ((22212396583127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT136 (i+1))
      = (∑ i ∈ Finset.range 77, stT136 (i+1)) + stT136 78 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 77
    simpa using h
  have hprev := st136_p77
  have hstep := st136_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p79 : ((21982639549927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT136 (i+1))
      = (∑ i ∈ Finset.range 78, stT136 (i+1)) + stT136 79 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 78
    simpa using h
  have hprev := st136_p78
  have hstep := st136_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p80 : ((9007896370431/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT136 (i+1))
      = (∑ i ∈ Finset.range 79, stT136 (i+1)) + stT136 80 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 79
    simpa using h
  have hprev := st136_p79
  have hstep := st136_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p81 : ((9043747477957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT136 (i+1))
      = (∑ i ∈ Finset.range 80, stT136 (i+1)) + stT136 81 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 80
    simpa using h
  have hprev := st136_p80
  have hstep := st136_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p82 : ((44116637751997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT136 (i+1))
      = (∑ i ∈ Finset.range 81, stT136 (i+1)) + stT136 82 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 81
    simpa using h
  have hprev := st136_p81
  have hstep := st136_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p83 : ((44131469090701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT136 (i+1))
      = (∑ i ∈ Finset.range 82, stT136 (i+1)) + stT136 83 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 82
    simpa using h
  have hprev := st136_p82
  have hstep := st136_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p84 : ((22609856810839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT136 (i+1))
      = (∑ i ∈ Finset.range 83, stT136 (i+1)) + stT136 84 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 83
    simpa using h
  have hprev := st136_p83
  have hstep := st136_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p85 : ((2818772535929/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT136 (i+1))
      = (∑ i ∈ Finset.range 84, stT136 (i+1)) + stT136 85 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 84
    simpa using h
  have hprev := st136_p84
  have hstep := st136_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p86 : ((1100777182377/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT136 (i+1))
      = (∑ i ∈ Finset.range 85, stT136 (i+1)) + stT136 86 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 85
    simpa using h
  have hprev := st136_p85
  have hstep := st136_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p87 : ((5521458899677/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT136 (i+1))
      = (∑ i ∈ Finset.range 86, stT136 (i+1)) + stT136 87 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 86
    simpa using h
  have hprev := st136_p86
  have hstep := st136_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p88 : ((45230571419427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT136 (i+1))
      = (∑ i ∈ Finset.range 87, stT136 (i+1)) + stT136 88 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 87
    simpa using h
  have hprev := st136_p87
  have hstep := st136_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p89 : ((45144752921349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT136 (i+1))
      = (∑ i ∈ Finset.range 88, stT136 (i+1)) + stT136 89 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 88
    simpa using h
  have hprev := st136_p88
  have hstep := st136_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p90 : ((22045537089949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT136 (i+1))
      = (∑ i ∈ Finset.range 89, stT136 (i+1)) + stT136 90 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 89
    simpa using h
  have hprev := st136_p89
  have hstep := st136_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p91 : ((11012734885097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT136 (i+1))
      = (∑ i ∈ Finset.range 90, stT136 (i+1)) + stT136 91 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 90
    simpa using h
  have hprev := st136_p90
  have hstep := st136_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p92 : ((2817851399879/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT136 (i+1))
      = (∑ i ∈ Finset.range 91, stT136 (i+1)) + stT136 92 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 91
    simpa using h
  have hprev := st136_p91
  have hstep := st136_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p93 : ((4531510587607/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT136 (i+1))
      = (∑ i ∈ Finset.range 92, stT136 (i+1)) + stT136 93 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 92
    simpa using h
  have hprev := st136_p92
  have hstep := st136_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p94 : ((11085621053217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT136 (i+1))
      = (∑ i ∈ Finset.range 93, stT136 (i+1)) + stT136 94 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 93
    simpa using h
  have hprev := st136_p93
  have hstep := st136_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p95 : ((21938401302279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT136 (i+1))
      = (∑ i ∈ Finset.range 94, stT136 (i+1)) + stT136 95 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 94
    simpa using h
  have hprev := st136_p94
  have hstep := st136_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p96 : ((22354366210099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT136 (i+1))
      = (∑ i ∈ Finset.range 95, stT136 (i+1)) + stT136 96 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 95
    simpa using h
  have hprev := st136_p95
  have hstep := st136_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p97 : ((11355548683033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT136 (i+1))
      = (∑ i ∈ Finset.range 96, stT136 (i+1)) + stT136 97 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 96
    simpa using h
  have hprev := st136_p96
  have hstep := st136_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p98 : ((22419392453797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT136 (i+1))
      = (∑ i ∈ Finset.range 97, stT136 (i+1)) + stT136 98 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 97
    simpa using h
  have hprev := st136_p97
  have hstep := st136_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p99 : ((21961675032723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT136 (i+1))
      = (∑ i ∈ Finset.range 98, stT136 (i+1)) + stT136 99 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 98
    simpa using h
  have hprev := st136_p98
  have hstep := st136_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p100 : ((44143122845673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT136 (i+1))
      = (∑ i ∈ Finset.range 99, stT136 (i+1)) + stT136 100 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 99
    simpa using h
  have hprev := st136_p99
  have hstep := st136_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p101 : ((45138102133527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT136 (i+1))
      = (∑ i ∈ Finset.range 100, stT136 (i+1)) + stT136 101 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 100
    simpa using h
  have hprev := st136_p100
  have hstep := st136_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p102 : ((708760783587/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT136 (i+1))
      = (∑ i ∈ Finset.range 101, stT136 (i+1)) + stT136 102 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 101
    simpa using h
  have hprev := st136_p101
  have hstep := st136_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p103 : ((11120622784787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT136 (i+1))
      = (∑ i ∈ Finset.range 102, stT136 (i+1)) + stT136 103 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 102
    simpa using h
  have hprev := st136_p102
  have hstep := st136_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p104 : ((21915162183253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT136 (i+1))
      = (∑ i ∈ Finset.range 103, stT136 (i+1)) + stT136 104 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 103
    simpa using h
  have hprev := st136_p103
  have hstep := st136_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p105 : ((22180057551553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT136 (i+1))
      = (∑ i ∈ Finset.range 104, stT136 (i+1)) + stT136 105 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 104
    simpa using h
  have hprev := st136_p104
  have hstep := st136_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p106 : ((22645087441283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT136 (i+1))
      = (∑ i ∈ Finset.range 105, stT136 (i+1)) + stT136 106 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 105
    simpa using h
  have hprev := st136_p105
  have hstep := st136_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p107 : ((22645818293699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT136 (i+1))
      = (∑ i ∈ Finset.range 106, stT136 (i+1)) + stT136 107 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 106
    simpa using h
  have hprev := st136_p106
  have hstep := st136_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p108 : ((22187197920087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT136 (i+1))
      = (∑ i ∈ Finset.range 107, stT136 (i+1)) + stT136 108 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 107
    simpa using h
  have hprev := st136_p107
  have hstep := st136_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p109 : ((43814259568401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT136 (i+1))
      = (∑ i ∈ Finset.range 108, stT136 (i+1)) + stT136 109 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 108
    simpa using h
  have hprev := st136_p108
  have hstep := st136_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p110 : ((8873245078887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT136 (i+1))
      = (∑ i ∈ Finset.range 109, stT136 (i+1)) + stT136 110 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 109
    simpa using h
  have hprev := st136_p109
  have hstep := st136_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p111 : ((9055807834581/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT136 (i+1))
      = (∑ i ∈ Finset.range 110, stT136 (i+1)) + stT136 111 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 110
    simpa using h
  have hprev := st136_p110
  have hstep := st136_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p112 : ((22674250262713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT136 (i+1))
      = (∑ i ∈ Finset.range 111, stT136 (i+1)) + stT136 112 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 111
    simpa using h
  have hprev := st136_p111
  have hstep := st136_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p113 : ((8899109570801/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT136 (i+1))
      = (∑ i ∈ Finset.range 112, stT136 (i+1)) + stT136 113 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 112
    simpa using h
  have hprev := st136_p112
  have hstep := st136_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p114 : ((43818388683317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT136 (i+1))
      = (∑ i ∈ Finset.range 113, stT136 (i+1)) + stT136 114 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 113
    simpa using h
  have hprev := st136_p113
  have hstep := st136_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p115 : ((44163974665717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT136 (i+1))
      = (∑ i ∈ Finset.range 114, stT136 (i+1)) + stT136 115 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 114
    simpa using h
  have hprev := st136_p114
  have hstep := st136_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p116 : ((360738550577/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT136 (i+1))
      = (∑ i ∈ Finset.range 115, stT136 (i+1)) + stT136 116 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 115
    simpa using h
  have hprev := st136_p115
  have hstep := st136_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p117 : ((72746738781/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT136 (i+1))
      = (∑ i ∈ Finset.range 116, stT136 (i+1)) + stT136 117 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 116
    simpa using h
  have hprev := st136_p116
  have hstep := st136_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p118 : ((112114057/25000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT136 (i+1))
      = (∑ i ∈ Finset.range 117, stT136 (i+1)) + stT136 118 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 117
    simpa using h
  have hprev := st136_p117
  have hstep := st136_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p119 : ((1099366218653/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT136 (i+1))
      = (∑ i ∈ Finset.range 118, stT136 (i+1)) + stT136 119 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 118
    simpa using h
  have hprev := st136_p118
  have hstep := st136_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p120 : ((8773903591481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT136 (i+1))
      = (∑ i ∈ Finset.range 119, stT136 (i+1)) + stT136 120 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 119
    simpa using h
  have hprev := st136_p119
  have hstep := st136_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p121 : ((8928178891751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT136 (i+1))
      = (∑ i ∈ Finset.range 120, stT136 (i+1)) + stT136 121 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 120
    simpa using h
  have hprev := st136_p120
  have hstep := st136_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p122 : ((45407041955721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT136 (i+1))
      = (∑ i ∈ Finset.range 121, stT136 (i+1)) + stT136 122 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 121
    simpa using h
  have hprev := st136_p121
  have hstep := st136_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p123 : ((45315875905361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT136 (i+1))
      = (∑ i ∈ Finset.range 122, stT136 (i+1)) + stT136 123 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 122
    simpa using h
  have hprev := st136_p122
  have hstep := st136_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p124 : ((44478040063063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT136 (i+1))
      = (∑ i ∈ Finset.range 123, stT136 (i+1)) + stT136 124 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 123
    simpa using h
  have hprev := st136_p123
  have hstep := st136_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p125 : ((8761588531063/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT136 (i+1))
      = (∑ i ∈ Finset.range 124, stT136 (i+1)) + stT136 125 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 124
    simpa using h
  have hprev := st136_p124
  have hstep := st136_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p126 : ((8803397238337/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT136 (i+1))
      = (∑ i ∈ Finset.range 125, stT136 (i+1)) + stT136 126 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 125
    simpa using h
  have hprev := st136_p125
  have hstep := st136_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p127 : ((8974949773817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT136 (i+1))
      = (∑ i ∈ Finset.range 126, stT136 (i+1)) + stT136 127 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 126
    simpa using h
  have hprev := st136_p126
  have hstep := st136_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p128 : ((1819419773777/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT136 (i+1))
      = (∑ i ∈ Finset.range 127, stT136 (i+1)) + stT136 128 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 127
    simpa using h
  have hprev := st136_p127
  have hstep := st136_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p129 : ((45229075316989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT136 (i+1))
      = (∑ i ∈ Finset.range 128, stT136 (i+1)) + stT136 129 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 128
    simpa using h
  have hprev := st136_p128
  have hstep := st136_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p130 : ((22187053401011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT136 (i+1))
      = (∑ i ∈ Finset.range 129, stT136 (i+1)) + stT136 130 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 129
    simpa using h
  have hprev := st136_p129
  have hstep := st136_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p131 : ((43776100288477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT136 (i+1))
      = (∑ i ∈ Finset.range 130, stT136 (i+1)) + stT136 131 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 130
    simpa using h
  have hprev := st136_p130
  have hstep := st136_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p132 : ((44016966241269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT136 (i+1))
      = (∑ i ∈ Finset.range 131, stT136 (i+1)) + stT136 132 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 131
    simpa using h
  have hprev := st136_p131
  have hstep := st136_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p133 : ((44854005635367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT136 (i+1))
      = (∑ i ∈ Finset.range 132, stT136 (i+1)) + stT136 133 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 132
    simpa using h
  have hprev := st136_p132
  have hstep := st136_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p134 : ((9096642679143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT136 (i+1))
      = (∑ i ∈ Finset.range 133, stT136 (i+1)) + stT136 134 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 133
    simpa using h
  have hprev := st136_p133
  have hstep := st136_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p135 : ((45316272314931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT136 (i+1))
      = (∑ i ∈ Finset.range 134, stT136 (i+1)) + stT136 135 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 134
    simpa using h
  have hprev := st136_p134
  have hstep := st136_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p136 : ((2782335684633/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT136 (i+1))
      = (∑ i ∈ Finset.range 135, stT136 (i+1)) + stT136 136 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 135
    simpa using h
  have hprev := st136_p135
  have hstep := st136_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p137 : ((21912088242087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT136 (i+1))
      = (∑ i ∈ Finset.range 136, stT136 (i+1)) + stT136 137 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 136
    simpa using h
  have hprev := st136_p136
  have hstep := st136_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p138 : ((21930232338099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT136 (i+1))
      = (∑ i ∈ Finset.range 137, stT136 (i+1)) + stT136 138 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 137
    simpa using h
  have hprev := st136_p137
  have hstep := st136_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p139 : ((4458522775119/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT136 (i+1))
      = (∑ i ∈ Finset.range 138, stT136 (i+1)) + stT136 139 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 138
    simpa using h
  have hprev := st136_p138
  have hstep := st136_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p140 : ((11338458404487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT136 (i+1))
      = (∑ i ∈ Finset.range 139, stT136 (i+1)) + stT136 140 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 139
    simpa using h
  have hprev := st136_p139
  have hstep := st136_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p141 : ((22749817610289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT136 (i+1))
      = (∑ i ∈ Finset.range 140, stT136 (i+1)) + stT136 141 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 140
    simpa using h
  have hprev := st136_p140
  have hstep := st136_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p142 : ((22452602003803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT136 (i+1))
      = (∑ i ∈ Finset.range 141, stT136 (i+1)) + stT136 142 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 141
    simpa using h
  have hprev := st136_p141
  have hstep := st136_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p143 : ((22040534903123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT136 (i+1))
      = (∑ i ∈ Finset.range 142, stT136 (i+1)) + stT136 143 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 142
    simpa using h
  have hprev := st136_p142
  have hstep := st136_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p144 : ((4371676618147/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT136 (i+1))
      = (∑ i ∈ Finset.range 143, stT136 (i+1)) + stT136 144 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 143
    simpa using h
  have hprev := st136_p143
  have hstep := st136_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p145 : ((11026669613047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT136 (i+1))
      = (∑ i ∈ Finset.range 144, stT136 (i+1)) + stT136 145 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 144
    simpa using h
  have hprev := st136_p144
  have hstep := st136_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p146 : ((2807830151263/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT136 (i+1))
      = (∑ i ∈ Finset.range 145, stT136 (i+1)) + stT136 146 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 145
    simpa using h
  have hprev := st136_p145
  have hstep := st136_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p147 : ((22755494263587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT136 (i+1))
      = (∑ i ∈ Finset.range 146, stT136 (i+1)) + stT136 147 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 146
    simpa using h
  have hprev := st136_p146
  have hstep := st136_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p148 : ((22701263965457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT136 (i+1))
      = (∑ i ∈ Finset.range 147, stT136 (i+1)) + stT136 148 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 147
    simpa using h
  have hprev := st136_p147
  have hstep := st136_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p149 : ((4469263309133/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT136 (i+1))
      = (∑ i ∈ Finset.range 148, stT136 (i+1)) + stT136 149 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 148
    simpa using h
  have hprev := st136_p148
  have hstep := st136_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p150 : ((219682416923/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT136 (i+1))
      = (∑ i ∈ Finset.range 149, stT136 (i+1)) + stT136 150 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 149
    simpa using h
  have hprev := st136_p149
  have hstep := st136_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p151 : ((43711456891687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT136 (i+1))
      = (∑ i ∈ Finset.range 150, stT136 (i+1)) + stT136 151 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 150
    simpa using h
  have hprev := st136_p150
  have hstep := st136_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p152 : ((22090549194539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT136 (i+1))
      = (∑ i ∈ Finset.range 151, stT136 (i+1)) + stT136 152 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 151
    simpa using h
  have hprev := st136_p151
  have hstep := st136_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p153 : ((22493993017229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT136 (i+1))
      = (∑ i ∈ Finset.range 152, stT136 (i+1)) + stT136 153 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 152
    simpa using h
  have hprev := st136_p152
  have hstep := st136_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p154 : ((5691873157557/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT136 (i+1))
      = (∑ i ∈ Finset.range 153, stT136 (i+1)) + stT136 154 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 153
    simpa using h
  have hprev := st136_p153
  have hstep := st136_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p155 : ((11356898485809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT136 (i+1))
      = (∑ i ∈ Finset.range 154, stT136 (i+1)) + stT136 155 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 154
    simpa using h
  have hprev := st136_p154
  have hstep := st136_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p156 : ((4475011875083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT136 (i+1))
      = (∑ i ∈ Finset.range 155, stT136 (i+1)) + stT136 156 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 155
    simpa using h
  have hprev := st136_p155
  have hstep := st136_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p157 : ((43989276076859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT136 (i+1))
      = (∑ i ∈ Finset.range 156, stT136 (i+1)) + stT136 157 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 156
    simpa using h
  have hprev := st136_p156
  have hstep := st136_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p158 : ((8735822694103/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT136 (i+1))
      = (∑ i ∈ Finset.range 157, stT136 (i+1)) + stT136 158 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 157
    simpa using h
  have hprev := st136_p157
  have hstep := st136_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p159 : ((44029453266377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT136 (i+1))
      = (∑ i ∈ Finset.range 158, stT136 (i+1)) + stT136 159 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 158
    simpa using h
  have hprev := st136_p158
  have hstep := st136_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p160 : ((44793307358729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT136 (i+1))
      = (∑ i ∈ Finset.range 159, stT136 (i+1)) + stT136 160 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 159
    simpa using h
  have hprev := st136_p159
  have hstep := st136_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p161 : ((45449525574009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT136 (i+1))
      = (∑ i ∈ Finset.range 160, stT136 (i+1)) + stT136 161 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 160
    simpa using h
  have hprev := st136_p160
  have hstep := st136_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p162 : ((9112112033277/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT136 (i+1))
      = (∑ i ∈ Finset.range 161, stT136 (i+1)) + stT136 162 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 161
    simpa using h
  have hprev := st136_p161
  have hstep := st136_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p163 : ((45058883062407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT136 (i+1))
      = (∑ i ∈ Finset.range 162, stT136 (i+1)) + stT136 163 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 162
    simpa using h
  have hprev := st136_p162
  have hstep := st136_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p164 : ((44278727776673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT136 (i+1))
      = (∑ i ∈ Finset.range 163, stT136 (i+1)) + stT136 164 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 163
    simpa using h
  have hprev := st136_p163
  have hstep := st136_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p165 : ((21863398059571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT136 (i+1))
      = (∑ i ∈ Finset.range 164, stT136 (i+1)) + stT136 165 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 164
    simpa using h
  have hprev := st136_p164
  have hstep := st136_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p166 : ((21876488605471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT136 (i+1))
      = (∑ i ∈ Finset.range 165, stT136 (i+1)) + stT136 166 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 165
    simpa using h
  have hprev := st136_p165
  have hstep := st136_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p167 : ((5541826497877/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT136 (i+1))
      = (∑ i ∈ Finset.range 166, stT136 (i+1)) + stT136 167 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 166
    simpa using h
  have hprev := st136_p166
  have hstep := st136_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p168 : ((11275710909851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT136 (i+1))
      = (∑ i ∈ Finset.range 167, stT136 (i+1)) + stT136 168 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 167
    simpa using h
  have hprev := st136_p167
  have hstep := st136_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p169 : ((22790818118767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT136 (i+1))
      = (∑ i ∈ Finset.range 168, stT136 (i+1)) + stT136 169 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 168
    simpa using h
  have hprev := st136_p168
  have hstep := st136_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p170 : ((45481830315119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT136 (i+1))
      = (∑ i ∈ Finset.range 169, stT136 (i+1)) + stT136 170 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 169
    simpa using h
  have hprev := st136_p169
  have hstep := st136_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p171 : ((44869645189919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT136 (i+1))
      = (∑ i ∈ Finset.range 170, stT136 (i+1)) + stT136 171 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 170
    simpa using h
  have hprev := st136_p170
  have hstep := st136_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p172 : ((11028927793461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT136 (i+1))
      = (∑ i ∈ Finset.range 171, stT136 (i+1)) + stT136 172 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 171
    simpa using h
  have hprev := st136_p171
  have hstep := st136_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p173 : ((21833238591797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT136 (i+1))
      = (∑ i ∈ Finset.range 172, stT136 (i+1)) + stT136 173 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 172
    simpa using h
  have hprev := st136_p172
  have hstep := st136_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p174 : ((5472633056799/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT136 (i+1))
      = (∑ i ∈ Finset.range 173, stT136 (i+1)) + stT136 174 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 173
    simpa using h
  have hprev := st136_p173
  have hstep := st136_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p175 : ((5548439595441/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT136 (i+1))
      = (∑ i ∈ Finset.range 174, stT136 (i+1)) + stT136 175 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 174
    simpa using h
  have hprev := st136_p174
  have hstep := st136_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p176 : ((352612258213/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT136 (i+1))
      = (∑ i ∈ Finset.range 175, stT136 (i+1)) + stT136 176 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 175
    simpa using h
  have hprev := st136_p175
  have hstep := st136_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p177 : ((284988228711/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT136 (i+1))
      = (∑ i ∈ Finset.range 176, stT136 (i+1)) + stT136 177 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 176
    simpa using h
  have hprev := st136_p176
  have hstep := st136_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p178 : ((2845145432253/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT136 (i+1))
      = (∑ i ∈ Finset.range 177, stT136 (i+1)) + stT136 178 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 177
    simpa using h
  have hprev := st136_p177
  have hstep := st136_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p179 : ((11238579166257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT136 (i+1))
      = (∑ i ∈ Finset.range 178, stT136 (i+1)) + stT136 179 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 178
    simpa using h
  have hprev := st136_p178
  have hstep := st136_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p180 : ((11052463773057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT136 (i+1))
      = (∑ i ∈ Finset.range 179, stT136 (i+1)) + stT136 180 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 179
    simpa using h
  have hprev := st136_p179
  have hstep := st136_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p181 : ((43693817335413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT136 (i+1))
      = (∑ i ∈ Finset.range 180, stT136 (i+1)) + stT136 181 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 180
    simpa using h
  have hprev := st136_p180
  have hstep := st136_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p182 : ((43680429619163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT136 (i+1))
      = (∑ i ∈ Finset.range 181, stT136 (i+1)) + stT136 182 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 181
    simpa using h
  have hprev := st136_p181
  have hstep := st136_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p183 : ((44171811994493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT136 (i+1))
      = (∑ i ∈ Finset.range 182, stT136 (i+1)) + stT136 183 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 182
    simpa using h
  have hprev := st136_p182
  have hstep := st136_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p184 : ((5613139868407/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT136 (i+1))
      = (∑ i ∈ Finset.range 183, stT136 (i+1)) + stT136 184 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 183
    simpa using h
  have hprev := st136_p183
  have hstep := st136_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p185 : ((11374280153049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT136 (i+1))
      = (∑ i ∈ Finset.range 184, stT136 (i+1)) + stT136 185 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 184
    simpa using h
  have hprev := st136_p184
  have hstep := st136_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p186 : ((713201329099/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT136 (i+1))
      = (∑ i ∈ Finset.range 185, stT136 (i+1)) + stT136 186 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 185
    simpa using h
  have hprev := st136_p185
  have hstep := st136_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p187 : ((45277523489329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT136 (i+1))
      = (∑ i ∈ Finset.range 186, stT136 (i+1)) + stT136 187 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 186
    simpa using h
  have hprev := st136_p186
  have hstep := st136_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p188 : ((11146250604201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT136 (i+1))
      = (∑ i ∈ Finset.range 187, stT136 (i+1)) + stT136 188 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 187
    simpa using h
  have hprev := st136_p187
  have hstep := st136_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p189 : ((43915644467309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT136 (i+1))
      = (∑ i ∈ Finset.range 188, stT136 (i+1)) + stT136 189 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 188
    simpa using h
  have hprev := st136_p188
  have hstep := st136_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p190 : ((43599507707881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT136 (i+1))
      = (∑ i ∈ Finset.range 189, stT136 (i+1)) + stT136 190 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 189
    simpa using h
  have hprev := st136_p189
  have hstep := st136_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p191 : ((43787646354343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT136 (i+1))
      = (∑ i ∈ Finset.range 190, stT136 (i+1)) + stT136 191 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 190
    simpa using h
  have hprev := st136_p190
  have hstep := st136_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p192 : ((44384249120129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT136 (i+1))
      = (∑ i ∈ Finset.range 191, stT136 (i+1)) + stT136 192 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 191
    simpa using h
  have hprev := st136_p191
  have hstep := st136_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p193 : ((22549879453307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT136 (i+1))
      = (∑ i ∈ Finset.range 192, stT136 (i+1)) + stT136 193 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 192
    simpa using h
  have hprev := st136_p192
  have hstep := st136_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p194 : ((22796905826451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT136 (i+1))
      = (∑ i ∈ Finset.range 193, stT136 (i+1)) + stT136 194 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 193
    simpa using h
  have hprev := st136_p193
  have hstep := st136_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p195 : ((22818271087641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT136 (i+1))
      = (∑ i ∈ Finset.range 194, stT136 (i+1)) + stT136 195 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 194
    simpa using h
  have hprev := st136_p194
  have hstep := st136_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p196 : ((22606146002791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT136 (i+1))
      = (∑ i ∈ Finset.range 195, stT136 (i+1)) + stT136 196 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 195
    simpa using h
  have hprev := st136_p195
  have hstep := st136_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p197 : ((44520680019049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT136 (i+1))
      = (∑ i ∈ Finset.range 196, stT136 (i+1)) + stT136 197 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 196
    simpa using h
  have hprev := st136_p196
  have hstep := st136_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p198 : ((43879439635369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT136 (i+1))
      = (∑ i ∈ Finset.range 197, stT136 (i+1)) + stT136 198 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 197
    simpa using h
  have hprev := st136_p197
  have hstep := st136_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p199 : ((43577574286663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT136 (i+1))
      = (∑ i ∈ Finset.range 198, stT136 (i+1)) + stT136 199 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 198
    simpa using h
  have hprev := st136_p198
  have hstep := st136_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p200 : ((43746905667589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT136 (i+1))
      = (∑ i ∈ Finset.range 199, stT136 (i+1)) + stT136 200 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 199
    simpa using h
  have hprev := st136_p199
  have hstep := st136_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p201 : ((44308123291669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT136 (i+1))
      = (∑ i ∈ Finset.range 200, stT136 (i+1)) + stT136 201 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 200
    simpa using h
  have hprev := st136_p200
  have hstep := st136_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p202 : ((45011476847107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT136 (i+1))
      = (∑ i ∈ Finset.range 201, stT136 (i+1)) + stT136 202 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 201
    simpa using h
  have hprev := st136_p201
  have hstep := st136_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p203 : ((45550092764527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT136 (i+1))
      = (∑ i ∈ Finset.range 202, stT136 (i+1)) + stT136 203 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 202
    simpa using h
  have hprev := st136_p202
  have hstep := st136_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p204 : ((45693656471527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT136 (i+1))
      = (∑ i ∈ Finset.range 203, stT136 (i+1)) + stT136 204 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 203
    simpa using h
  have hprev := st136_p203
  have hstep := st136_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p205 : ((45384509957997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT136 (i+1))
      = (∑ i ∈ Finset.range 204, stT136 (i+1)) + stT136 205 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 204
    simpa using h
  have hprev := st136_p204
  have hstep := st136_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p206 : ((44757260543083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT136 (i+1))
      = (∑ i ∈ Finset.range 205, stT136 (i+1)) + stT136 206 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 205
    simpa using h
  have hprev := st136_p205
  have hstep := st136_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p207 : ((22038584151257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT136 (i+1))
      = (∑ i ∈ Finset.range 206, stT136 (i+1)) + stT136 207 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 206
    simpa using h
  have hprev := st136_p206
  have hstep := st136_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p208 : ((21813295194841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT136 (i+1))
      = (∑ i ∈ Finset.range 207, stT136 (i+1)) + stT136 208 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 207
    simpa using h
  have hprev := st136_p207
  have hstep := st136_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p209 : ((43588520471227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT136 (i+1))
      = (∑ i ∈ Finset.range 208, stT136 (i+1)) + stT136 209 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 208
    simpa using h
  have hprev := st136_p208
  have hstep := st136_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p210 : ((43974789875497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT136 (i+1))
      = (∑ i ∈ Finset.range 209, stT136 (i+1)) + stT136 210 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 209
    simpa using h
  have hprev := st136_p209
  have hstep := st136_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p211 : ((8925182530121/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT136 (i+1))
      = (∑ i ∈ Finset.range 210, stT136 (i+1)) + stT136 211 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 210
    simpa using h
  have hprev := st136_p210
  have hstep := st136_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p212 : ((9055885071533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT136 (i+1))
      = (∑ i ∈ Finset.range 211, stT136 (i+1)) + stT136 212 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 211
    simpa using h
  have hprev := st136_p211
  have hstep := st136_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p213 : ((45676578822541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT136 (i+1))
      = (∑ i ∈ Finset.range 212, stT136 (i+1)) + stT136 213 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 212
    simpa using h
  have hprev := st136_p212
  have hstep := st136_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p214 : ((45663777307519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT136 (i+1))
      = (∑ i ∈ Finset.range 213, stT136 (i+1)) + stT136 214 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 213
    simpa using h
  have hprev := st136_p213
  have hstep := st136_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p215 : ((22624769841237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT136 (i+1))
      = (∑ i ∈ Finset.range 214, stT136 (i+1)) + stT136 215 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 214
    simpa using h
  have hprev := st136_p214
  have hstep := st136_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p216 : ((22298460297187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT136 (i+1))
      = (∑ i ∈ Finset.range 215, stT136 (i+1)) + stT136 216 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 215
    simpa using h
  have hprev := st136_p215
  have hstep := st136_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p217 : ((43957169599079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT136 (i+1))
      = (∑ i ∈ Finset.range 216, stT136 (i+1)) + stT136 217 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 216
    simpa using h
  have hprev := st136_p216
  have hstep := st136_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p218 : ((43572293702147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT136 (i+1))
      = (∑ i ∈ Finset.range 217, stT136 (i+1)) + stT136 218 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 217
    simpa using h
  have hprev := st136_p217
  have hstep := st136_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p219 : ((2179224503963/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT136 (i+1))
      = (∑ i ∈ Finset.range 218, stT136 (i+1)) + stT136 219 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 218
    simpa using h
  have hprev := st136_p218
  have hstep := st136_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p220 : ((4398583400197/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT136 (i+1))
      = (∑ i ∈ Finset.range 219, stT136 (i+1)) + stT136 220 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 219
    simpa using h
  have hprev := st136_p219
  have hstep := st136_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p221 : ((22312549546217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT136 (i+1))
      = (∑ i ∈ Finset.range 220, stT136 (i+1)) + stT136 221 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 220
    simpa using h
  have hprev := st136_p220
  have hstep := st136_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p222 : ((22633353389189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT136 (i+1))
      = (∑ i ∈ Finset.range 221, stT136 (i+1)) + stT136 222 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 221
    simpa using h
  have hprev := st136_p221
  have hstep := st136_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p223 : ((45678246937467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT136 (i+1))
      = (∑ i ∈ Finset.range 222, stT136 (i+1)) + stT136 223 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 222
    simpa using h
  have hprev := st136_p222
  have hstep := st136_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p224 : ((45713867510203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT136 (i+1))
      = (∑ i ∈ Finset.range 223, stT136 (i+1)) + stT136 224 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 223
    simpa using h
  have hprev := st136_p223
  have hstep := st136_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p225 : ((22682003334303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT136 (i+1))
      = (∑ i ∈ Finset.range 224, stT136 (i+1)) + stT136 225 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 224
    simpa using h
  have hprev := st136_p224
  have hstep := st136_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p226 : ((8951064595773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT136 (i+1))
      = (∑ i ∈ Finset.range 225, stT136 (i+1)) + stT136 226 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 225
    simpa using h
  have hprev := st136_p225
  have hstep := st136_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p227 : ((44102910826997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT136 (i+1))
      = (∑ i ∈ Finset.range 226, stT136 (i+1)) + stT136 227 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 226
    simpa using h
  have hprev := st136_p226
  have hstep := st136_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p228 : ((21816722491419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT136 (i+1))
      = (∑ i ∈ Finset.range 227, stT136 (i+1)) + stT136 228 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 227
    simpa using h
  have hprev := st136_p227
  have hstep := st136_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p229 : ((43506894840243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT136 (i+1))
      = (∑ i ∈ Finset.range 228, stT136 (i+1)) + stT136 229 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 228
    simpa using h
  have hprev := st136_p228
  have hstep := st136_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p230 : ((43763605321223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT136 (i+1))
      = (∑ i ∈ Finset.range 229, stT136 (i+1)) + stT136 230 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 229
    simpa using h
  have hprev := st136_p229
  have hstep := st136_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p231 : ((44313626039183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT136 (i+1))
      = (∑ i ∈ Finset.range 230, stT136 (i+1)) + stT136 231 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 230
    simpa using h
  have hprev := st136_p230
  have hstep := st136_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p232 : ((44970110768879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT136 (i+1))
      = (∑ i ∈ Finset.range 231, stT136 (i+1)) + stT136 232 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 231
    simpa using h
  have hprev := st136_p231
  have hstep := st136_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p233 : ((11378466118621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT136 (i+1))
      = (∑ i ∈ Finset.range 232, stT136 (i+1)) + stT136 233 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 232
    simpa using h
  have hprev := st136_p232
  have hstep := st136_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p234 : ((11441612365451/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT136 (i+1))
      = (∑ i ∈ Finset.range 233, stT136 (i+1)) + stT136 234 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 233
    simpa using h
  have hprev := st136_p233
  have hstep := st136_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p235 : ((912951563149/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT136 (i+1))
      = (∑ i ∈ Finset.range 234, stT136 (i+1)) + stT136 235 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 234
    simpa using h
  have hprev := st136_p234
  have hstep := st136_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p236 : ((4519876720263/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT136 (i+1))
      = (∑ i ∈ Finset.range 235, stT136 (i+1)) + stT136 236 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 235
    simpa using h
  have hprev := st136_p235
  have hstep := st136_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p237 : ((4456702659999/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT136 (i+1))
      = (∑ i ∈ Finset.range 236, stT136 (i+1)) + stT136 237 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 236
    simpa using h
  have hprev := st136_p236
  have hstep := st136_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p238 : ((879107496471/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT136 (i+1))
      = (∑ i ∈ Finset.range 237, stT136 (i+1)) + stT136 238 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 237
    simpa using h
  have hprev := st136_p237
  have hstep := st136_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p239 : ((1361163320763/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT136 (i+1))
      = (∑ i ∈ Finset.range 238, stT136 (i+1)) + stT136 239 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 238
    simpa using h
  have hprev := st136_p238
  have hstep := st136_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p240 : ((4349588007099/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT136 (i+1))
      = (∑ i ∈ Finset.range 239, stT136 (i+1)) + stT136 240 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 239
    simpa using h
  have hprev := st136_p239
  have hstep := st136_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p241 : ((4378778258317/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT136 (i+1))
      = (∑ i ∈ Finset.range 240, stT136 (i+1)) + stT136 241 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 240
    simpa using h
  have hprev := st136_p240
  have hstep := st136_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p242 : ((22169999948773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT136 (i+1))
      = (∑ i ∈ Finset.range 241, stT136 (i+1)) + stT136 242 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 241
    simpa using h
  have hprev := st136_p241
  have hstep := st136_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p243 : ((22490645063523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT136 (i+1))
      = (∑ i ∈ Finset.range 242, stT136 (i+1)) + stT136 243 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 242
    simpa using h
  have hprev := st136_p242
  have hstep := st136_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p244 : ((22758012469559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT136 (i+1))
      = (∑ i ∈ Finset.range 243, stT136 (i+1)) + stT136 244 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 243
    simpa using h
  have hprev := st136_p243
  have hstep := st136_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p245 : ((4578377595409/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT136 (i+1))
      = (∑ i ∈ Finset.range 244, stT136 (i+1)) + stT136 245 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 244
    simpa using h
  have hprev := st136_p244
  have hstep := st136_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p246 : ((11426621898749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT136 (i+1))
      = (∑ i ∈ Finset.range 245, stT136 (i+1)) + stT136 246 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 245
    simpa using h
  have hprev := st136_p245
  have hstep := st136_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p247 : ((45309740354951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT136 (i+1))
      = (∑ i ∈ Finset.range 246, stT136 (i+1)) + stT136 247 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 246
    simpa using h
  have hprev := st136_p246
  have hstep := st136_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p248 : ((44712794964881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT136 (i+1))
      = (∑ i ∈ Finset.range 247, stT136 (i+1)) + stT136 248 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 247
    simpa using h
  have hprev := st136_p247
  have hstep := st136_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p249 : ((11022891597039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT136 (i+1))
      = (∑ i ∈ Finset.range 248, stT136 (i+1)) + stT136 249 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 248
    simpa using h
  have hprev := st136_p248
  have hstep := st136_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_p250 : ((2181315607421/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT136 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT136 (i+1))
      = (∑ i ∈ Finset.range 249, stT136 (i+1)) + stT136 250 := by
    have h := Finset.sum_range_succ (fun i => stT136 (i+1)) 249
    simpa using h
  have hprev := st136_p249
  have hstep := st136_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st136_s250 :
    |Real.sin (((136 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))
      - ((-169359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -2996651/5000000) (δ := 347/50000000) (ψ := -666227/1000000) 136 120
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 136`** (evaluated boundary). -/
theorem station_136_sign : hardyG ((((136:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 136 250 (by norm_num) (by norm_num)
    ((-666227/1000000 : ℚ) : ℝ)
  have hchain := st136_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT136 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((136 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-666227/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st136_c250
  have hsinb := abs_le.mp st136_s250
  have hbdy_lo : ((23398877298793/295940000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((136 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ))) / 2
          - ((((136:ℕ)):ℝ))
            * Real.sin (((136 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-666227/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((136:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((136:ℝ) * Real.log (250:ℝ) - ((-666227/1000000 : ℚ) : ℝ))) / 2
        - ((136:ℝ)) * Real.sin ((136:ℝ) * Real.log (250:ℝ) - ((-666227/1000000 : ℚ) : ℝ))
        ≥ ((184984523/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((136:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((184984523/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((184984523/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((184984523/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((136:ℕ)):ℝ))+1) * (((((136:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((135183754321/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2181315607421/500000000000 : ℚ) : ℝ) + ((23398877298793/295940000000000 : ℚ) : ℝ)
      - ((135183754321/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-666227/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((136:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-666227/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((136:ℕ)):ℝ)))).re
      - Real.sin ((-666227/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((136:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((136:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((136:ℕ)):ℝ))
      = (((((136:ℕ)):ℝ)) * (Real.log ((((136:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((136:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_136
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
  have hθwin : |(((-666227/1000000 : ℚ) : ℝ) + ((23:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((136:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((136:ℕ)):ℝ)))
    (φ := ((-666227/1000000 : ℚ) : ℝ) + ((23:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-666227/1000000 : ℚ) : ℝ) + ((23:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-666227/1000000 : ℚ)) : ℝ) - Real.pi) + ((23:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-666227/1000000 : ℚ)) : ℝ) - Real.pi) 23).1,
    (cos_sin_shift ((((-666227/1000000 : ℚ)) : ℝ) - Real.pi) 23).2]
  exact cos_sin_flip ((-666227/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_136_sign
end AxiomAudit
