import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 181` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT181 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((181 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))

theorem st181_c1 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((232933/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 232277/2500000) (δ := 201/1000000000) (ψ := -371643/1000000) 181 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t1 : ((465841/500000 : ℚ) : ℝ) ≤ stT181 1 := by
  have hc : ((465841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((465841/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((465841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c2 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((985993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26183/625000) (δ := 1849/200000000) (ψ := -371643/1000000) 181 20
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t2 : ((6971669011181/10000000000000 : ℚ) : ℝ) ≤ stT181 2 := by
  have hc : ((985943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6971669011181/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((985943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c3 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-13369/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2301837/5000000) (δ := 567/62500000) (ψ := -371643/1000000) 181 32
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t3 : ((-154400790729/1000000000000 : ℚ) : ℝ) ≤ stT181 3 := by
  have hc : ((-26743/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154400790729/1000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-26743/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c4 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((499667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9123/1000000) (δ := 4557/500000000) (ψ := -371643/1000000) 181 40
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t4 : ((249821/500000 : ℚ) : ℝ) ≤ stT181 4 := by
  have hc : ((249821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249821/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((249821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c5 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-110397/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 663347/1000000) (δ := 577/62500000) (ψ := -371643/1000000) 181 46
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t5 : ((-246869174421/625000000000 : ℚ) : ℝ) ≤ stT181 5 := by
  have hc : ((-441613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246869174421/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-441613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c6 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-28569/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5113831/10000000) (δ := 367/40000000) (ψ := -371643/1000000) 181 52
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t6 : ((-933161716691/5000000000000 : ℚ) : ℝ) ≤ stT181 6 := by
  have hc : ((-228577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-933161716691/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-228577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c7 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((374911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1807507/10000000) (δ := 9199/1000000000) (ψ := -371643/1000000) 181 56
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t7 : ((177116952573/625000000000 : ℚ) : ℝ) ≤ stT181 7 := by
  have hc : ((187443/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177116952573/625000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((187443/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c8 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((485603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601387/10000000) (δ := 2283/250000000) (ψ := -371643/1000000) 181 60
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t8 : ((858388521537/2500000000000 : ℚ) : ℝ) ≤ stT181 8 := by
  have hc : ((242789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((858388521537/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((242789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c9 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-61139/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 557153/1000000) (δ := 9249/1000000000) (ψ := -371643/1000000) 181 63
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t9 : ((-12738335881/62500000000 : ℚ) : ℝ) ≤ stT181 9 := by
  have hc : ((-7643/12500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12738335881/62500000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-7643/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c10 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-769789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6123267/10000000) (δ := 363/40000000) (ψ := -371643/1000000) 181 66
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t10 : ((-1217222466621/5000000000000 : ℚ) : ℝ) ≤ stT181 10 := by
  have hc : ((-769839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1217222466621/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-769839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c11 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((659309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2127243/10000000) (δ := 9197/1000000000) (ψ := -371643/1000000) 181 69
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t11 : ((1987740381267/10000000000000 : ℚ) : ℝ) ≤ stT181 11 := by
  have hc : ((659259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1987740381267/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((659259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c12 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-627859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5623989/10000000) (δ := 1837/200000000) (ψ := -371643/1000000) 181 72
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t12 : ((-56644298799/312500000000 : ℚ) : ℝ) ≤ stT181 12 := by
  have hc : ((-627909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56644298799/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-627909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c13 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((236653/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -820593/10000000) (δ := 9233/1000000000) (ψ := -371643/1000000) 181 74
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t13 : ((2625289707/10000000000 : ℚ) : ℝ) ≤ stT181 13 := by
  have hc : ((473281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2625289707/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((473281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c14 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((173669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25947/200000) (δ := 283/31250000) (ψ := -371643/1000000) 181 76
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t14 : ((116030781827/500000000000 : ℚ) : ℝ) ≤ stT181 14 := by
  have hc : ((173659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116030781827/500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((173659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c15 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((90463/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1100711/10000000) (δ := 4581/500000000) (ψ := -371643/1000000) 181 78
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t15 : ((29195183813/125000000000 : ℚ) : ℝ) ≤ stT181 15 := by
  have hc : ((45229/50000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29195183813/125000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((45229/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c16 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((36111/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222309/2000000) (δ := 9227/1000000000) (ψ := -371643/1000000) 181 80
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t16 : ((36109/160000 : ℚ) : ℝ) ≤ stT181 16 := by
  have hc : ((36109/40000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36109/160000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((36109/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c17 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-225167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127371/250000) (δ := 9213/1000000000) (ψ := -371643/1000000) 181 82
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t17 : ((-68271374193/625000000000 : ℚ) : ℝ) ≤ stT181 17 := by
  have hc : ((-28149/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68271374193/625000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-28149/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c18 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-219171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5061373/10000000) (δ := 4553/500000000) (ψ := -371643/1000000) 181 83
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t18 : ((-129162503377/1250000000000 : ℚ) : ℝ) ≤ stT181 18 := by
  have hc : ((-54799/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129162503377/1250000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-54799/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c19 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((36391/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -377829/2000000) (δ := 2303/250000000) (ψ := -371643/1000000) 181 85
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t19 : ((166961863989/1000000000000 : ℚ) : ℝ) ≤ stT181 19 := by
  have hc : ((72777/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166961863989/1000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((72777/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c20 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-312233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 561311/1000000) (δ := 9219/1000000000) (ψ := -371643/1000000) 181 86
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t20 : ((-87278765193/625000000000 : ℚ) : ℝ) ≤ stT181 20 := by
  have hc : ((-156129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87278765193/625000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-156129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c21 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((2519/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3725251/10000000) (δ := 9233/1000000000) (ψ := -371643/1000000) 181 88
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t21 : ((43947973831/2500000000000 : ℚ) : ℝ) ≤ stT181 21 := by
  have hc : ((40279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43947973831/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((40279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c22 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((199499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323417/2000000) (δ := 9163/1000000000) (ψ := -371643/1000000) 181 89
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t22 : ((850613228811/5000000000000 : ℚ) : ℝ) ≤ stT181 22 := by
  have hc : ((398973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((850613228811/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((398973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c23 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-743727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3011781/5000000) (δ := 289/31250000) (ψ := -371643/1000000) 181 90
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t23 : ((-310176578533/2000000000000 : ℚ) : ℝ) ≤ stT181 23 := by
  have hc : ((-743777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310176578533/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-743777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c24 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-772559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3067073/5000000) (δ := 4531/500000000) (ψ := -371643/1000000) 181 92
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t24 : ((-788540970189/5000000000000 : ℚ) : ℝ) ≤ stT181 24 := by
  have hc : ((-772609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-788540970189/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-772609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c25 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((110449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1685077/5000000) (δ := 9169/1000000000) (ψ := -371643/1000000) 181 93
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t25 : ((13803/312500 : ℚ) : ℝ) ≤ stT181 25 := by
  have hc : ((13803/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13803/312500 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((13803/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c26 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((430821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1330751/10000000) (δ := 9127/1000000000) (ψ := -371643/1000000) 181 94
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t26 : ((211215078539/1250000000000 : ℚ) : ℝ) ≤ stT181 26 := by
  have hc : ((107699/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211215078539/1250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((107699/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c27 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((24997/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9693/2500000) (δ := 287/31250000) (ψ := -371643/1000000) 181 95
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t27 : ((384834567/2000000000 : ℚ) : ℝ) ≤ stT181 27 := by
  have hc : ((99983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384834567/2000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((99983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c28 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((475417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 787193/10000000) (δ := 9191/1000000000) (ψ := -371643/1000000) 181 96
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t28 : ((1754699727/9765625000 : ℚ) : ℝ) ≤ stT181 28 := by
  have hc : ((14856/15625 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1754699727/9765625000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((14856/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c29 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((927467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 958043/10000000) (δ := 4599/500000000) (ψ := -371643/1000000) 181 97
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t29 : ((1722169780401/10000000000000 : ℚ) : ℝ) ≤ stT181 29 := by
  have hc : ((927417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1722169780401/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((927417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c30 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((972233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147627/2500000) (δ := 4549/500000000) (ψ := -371643/1000000) 181 98
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t30 : ((1774954362603/10000000000000 : ℚ) : ℝ) ≤ stT181 30 := by
  have hc : ((972183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1774954362603/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((972183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c31 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((993733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11201/400000) (δ := 2303/250000000) (ψ := -371643/1000000) 181 99
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t31 : ((1784707333199/10000000000000 : ℚ) : ℝ) ≤ stT181 31 := by
  have hc : ((993683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1784707333199/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((993683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c32 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((796881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -810851/5000000) (δ := 2271/250000000) (ψ := -371643/1000000) 181 100
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t32 : ((704305374773/5000000000000 : ℚ) : ℝ) ≤ stT181 32 := by
  have hc : ((796831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((704305374773/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((796831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c33 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((207081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -851379/2500000) (δ := 9127/1000000000) (ψ := -371643/1000000) 181 101
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t33 : ((45049324507/1250000000000 : ℚ) : ℝ) ≤ stT181 33 := by
  have hc : ((207031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45049324507/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((207031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c34 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-77741/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5604997/10000000) (δ := 9069/1000000000) (ψ := -371643/1000000) 181 102
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t34 : ((-266670890577/2500000000000 : ℚ) : ℝ) ≤ stT181 34 := by
  have hc : ((-310989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266670890577/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-310989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c35 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-19813/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7511847/10000000) (δ := 4567/500000000) (ψ := -371643/1000000) 181 102
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t35 : ((-16745891263/100000000000 : ℚ) : ℝ) ≤ stT181 35 := by
  have hc : ((-9907/10000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16745891263/100000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-9907/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c36 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-3861/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284451/625000) (δ := 9141/1000000000) (ψ := -371643/1000000) 181 103
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t36 : ((-205961707859/5000000000000 : ℚ) : ℝ) ≤ stT181 36 := by
  have hc : ((-123577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205961707859/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-123577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c37 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((439623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12413/100000) (δ := 1811/200000000) (ψ := -371643/1000000) 181 104
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t37 : ((361347138211/2500000000000 : ℚ) : ℝ) ≤ stT181 37 := by
  have hc : ((219799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361347138211/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((219799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c38 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((143437/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2399303/10000000) (δ := 2287/250000000) (ψ := -371643/1000000) 181 105
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t38 : ((232665231843/2500000000000 : ℚ) : ℝ) ≤ stT181 38 := by
  have hc : ((286849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232665231843/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((286849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c39 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-825193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794169/1250000) (δ := 9163/1000000000) (ψ := -371643/1000000) 181 106
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t39 : ((-660723380763/5000000000000 : ℚ) : ℝ) ≤ stT181 39 := by
  have hc : ((-825243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660723380763/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-825243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c40 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-453229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 637869/1250000) (δ := 457/50000000) (ψ := -371643/1000000) 181 106
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t40 : ((-716697104781/10000000000000 : ℚ) : ℝ) ≤ stT181 40 := by
  have hc : ((-453279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-716697104781/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-453279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c41 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((487133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56839/1000000) (δ := 9233/1000000000) (ψ := -371643/1000000) 181 107
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t41 : ((190183646649/1250000000000 : ℚ) : ℝ) ≤ stT181 41 := by
  have hc : ((121777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190183646649/1250000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((121777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c42 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-24611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4235409/10000000) (δ := 4563/500000000) (ψ := -371643/1000000) 181 108
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t42 : ((-18995520057/1000000000000 : ℚ) : ℝ) ≤ stT181 42 := by
  have hc : ((-24621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18995520057/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-24621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c43 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-838247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3206071/5000000) (δ := 4613/500000000) (ψ := -371643/1000000) 181 108
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t43 : ((-639195594421/5000000000000 : ℚ) : ℝ) ≤ stT181 43 := by
  have hc : ((-838297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-639195594421/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-838297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c44 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((56473/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69183/625000) (δ := 2271/250000000) (ψ := -371643/1000000) 181 109
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t44 : ((170262997751/1250000000000 : ℚ) : ℝ) ≤ stT181 44 := by
  have hc : ((451759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170262997751/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((451759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c45 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-200669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4432093/10000000) (δ := 9191/1000000000) (ψ := -371643/1000000) 181 110
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t45 : ((-37401777741/1250000000000 : ℚ) : ℝ) ≤ stT181 45 := by
  have hc : ((-200719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37401777741/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-200719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c46 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-592813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5513359/10000000) (δ := 9091/1000000000) (ψ := -371643/1000000) 181 110
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t46 : ((-43706453223/500000000000 : ℚ) : ℝ) ≤ stT181 46 := by
  have hc : ((-592863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43706453223/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-592863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c47 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((982899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115751/2500000) (δ := 1841/200000000) (ψ := -371643/1000000) 181 111
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t47 : ((1433631711001/10000000000000 : ℚ) : ℝ) ≤ stT181 47 := by
  have hc : ((982849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1433631711001/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((982849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c48 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-885201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6644303/10000000) (δ := 4603/500000000) (ψ := -371643/1000000) 181 112
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t48 : ((-79859377961/625000000000 : ℚ) : ℝ) ≤ stT181 48 := by
  have hc : ((-885251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79859377961/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-885251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c49 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((4763/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 537177/2000000) (δ := 4603/500000000) (ψ := -371643/1000000) 181 112
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t49 : ((544285551/8000000000 : ℚ) : ℝ) ≤ stT181 49 := by
  have hc : ((381/800 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544285551/8000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((381/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c50 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((1867/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -485039/1250000) (δ := 919/100000000) (ψ := -371643/1000000) 181 113
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t50 : ((1316632303/500000000000 : ℚ) : ℝ) ≤ stT181 50 := by
  have hc : ((931/50000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1316632303/500000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((931/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c51 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-445157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1016073/2000000) (δ := 9113/1000000000) (ψ := -371643/1000000) 181 113
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t51 : ((-623414903167/10000000000000 : ℚ) : ℝ) ≤ stT181 51 := by
  have hc : ((-445207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-623414903167/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-445207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c52 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((185229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460227/2500000) (δ := 57/6250000) (ψ := -371643/1000000) 181 114
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t52 : ((2054791851/20000000000 : ℚ) : ℝ) ≤ stT181 52 := by
  have hc : ((370433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2054791851/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((370433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c53 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-908869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3389201/5000000) (δ := 9183/1000000000) (ψ := -371643/1000000) 181 114
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t53 : ((-624248295957/5000000000000 : ℚ) : ℝ) ≤ stT181 53 := by
  have hc : ((-908919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-624248295957/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-908919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c54 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((245569/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235693/5000000) (δ := 1147/125000000) (ψ := -371643/1000000) 181 115
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t54 : ((668319830451/5000000000000 : ℚ) : ℝ) ≤ stT181 54 := by
  have hc : ((491113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((668319830451/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((491113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c55 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-24999/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3915791/5000000) (δ := 2269/250000000) (ψ := -371643/1000000) 181 115
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t55 : ((-337103371/2500000000 : ℚ) : ℝ) ≤ stT181 55 := by
  have hc : ((-100001/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337103371/2500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-100001/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c56 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((248467/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27699/1000000) (δ := 9069/1000000000) (ψ := -371643/1000000) 181 116
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t56 : ((332011239077/2500000000000 : ℚ) : ℝ) ≤ stT181 56 := by
  have hc : ((496909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332011239077/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((496909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c57 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-492551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -463869/625000) (δ := 4571/500000000) (ψ := -371643/1000000) 181 117
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t57 : ((-20388536469/156250000000 : ℚ) : ℝ) ≤ stT181 57 := by
  have hc : ((-15393/15625 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20388536469/156250000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-15393/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c58 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((196799/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89577/2000000) (δ := 9161/1000000000) (ψ := -371643/1000000) 181 117
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t58 : ((32299568937/250000000000 : ℚ) : ℝ) ≤ stT181 58 := by
  have hc : ((196789/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32299568937/250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((196789/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c59 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-991347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3762431/5000000) (δ := 4527/500000000) (ψ := -371643/1000000) 181 118
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t59 : ((-129068984033/1000000000000 : ℚ) : ℝ) ≤ stT181 59 := by
  have hc : ((-991397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129068984033/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-991397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c60 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((249871/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80351/10000000) (δ := 9149/1000000000) (ψ := -371643/1000000) 181 118
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t60 : ((322565824349/2500000000000 : ℚ) : ℝ) ≤ stT181 60 := by
  have hc : ((499717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322565824349/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((499717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c61 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-993087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7559859/10000000) (δ := 4527/500000000) (ψ := -371643/1000000) 181 118
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t61 : ((-1271581827553/10000000000000 : ℚ) : ℝ) ≤ stT181 61 := by
  have hc : ((-993137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1271581827553/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-993137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c62 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((475229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197557/2500000) (δ := 283/31250000) (ψ := -371643/1000000) 181 119
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t62 : ((150877388801/1250000000000 : ℚ) : ℝ) ≤ stT181 62 := by
  have hc : ((118801/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150877388801/1250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((118801/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c63 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-423199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6449953/10000000) (δ := 283/31250000) (ψ := -371643/1000000) 181 119
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t63 : ((-33325768723/312500000000 : ℚ) : ℝ) ≤ stT181 63 := by
  have hc : ((-52903/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33325768723/312500000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-52903/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c64 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((328953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426381/2000000) (δ := 231/25000000) (ψ := -371643/1000000) 181 120
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t64 : ((10279/125000 : ℚ) : ℝ) ≤ stT181 64 := by
  have hc : ((10279/15625 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10279/125000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((10279/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c65 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-93357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2441873/5000000) (δ := 9063/1000000000) (ψ := -371643/1000000) 181 120
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t65 : ((-57905336293/1250000000000 : ℚ) : ℝ) ≤ stT181 65 := by
  have hc : ((-186739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57905336293/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-186739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c66 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((4527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957837/5000000) (δ := 9233/1000000000) (ψ := -371643/1000000) 181 121
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t66 : ((2755400989/5000000000000 : ℚ) : ℝ) ≤ stT181 66 := by
  have hc : ((4477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2755400989/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((4477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c67 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((201689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180561/625000) (δ := 9133/1000000000) (ψ := -371643/1000000) 181 121
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t67 : ((1924778897/39062500000 : ℚ) : ℝ) ≤ stT181 67 := by
  have hc : ((6302/15625 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1924778897/39062500000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((6302/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c68 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-383857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3057577/5000000) (δ := 9177/1000000000) (ψ := -371643/1000000) 181 122
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t68 : ((-232762819939/2500000000000 : ℚ) : ℝ) ≤ stT181 68 := by
  have hc : ((-191941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232762819939/2500000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-191941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c69 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((980791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490803/10000000) (δ := 9177/1000000000) (ψ := -371643/1000000) 181 122
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t69 : ((590336449389/5000000000000 : ℚ) : ℝ) ≤ stT181 69 := by
  have hc : ((980741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((590336449389/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((980741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c70 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-58903/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7001689/10000000) (δ := 4613/500000000) (ψ := -371643/1000000) 181 122
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t70 : ((-563250471021/5000000000000 : ℚ) : ℝ) ≤ stT181 70 := by
  have hc : ((-471249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563250471021/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-471249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c71 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((304857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1143871/5000000) (δ := 1837/200000000) (ψ := -371643/1000000) 181 123
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t71 : ((5652637903/78125000000 : ℚ) : ℝ) ≤ stT181 71 := by
  have hc : ((9526/15625 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5652637903/78125000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((9526/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c72 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-45611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2020529/5000000) (δ := 4609/500000000) (ψ := -371643/1000000) 181 123
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t72 : ((-3363252277/625000000000 : ℚ) : ℝ) ≤ stT181 72 := by
  have hc : ((-45661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3363252277/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-45661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c73 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-564129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5425437/10000000) (δ := 9211/1000000000) (ψ := -371643/1000000) 181 124
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t73 : ((-165080467937/2500000000000 : ℚ) : ℝ) ≤ stT181 73 := by
  have hc : ((-564179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165080467937/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-564179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c74 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((119693/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731097/10000000) (δ := 9211/1000000000) (ψ := -371643/1000000) 181 124
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t74 : ((139132974393/1250000000000 : ℚ) : ℝ) ≤ stT181 74 := by
  have hc : ((478747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139132974393/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((478747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c75 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-913263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136101/200000) (δ := 9111/1000000000) (ψ := -371643/1000000) 181 124
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t75 : ((-1054603434413/10000000000000 : ℚ) : ℝ) ≤ stT181 75 := by
  have hc : ((-913313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1054603434413/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-913313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c76 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((395867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145473/500000) (δ := 9099/1000000000) (ψ := -371643/1000000) 181 125
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t76 : ((227016486363/5000000000000 : ℚ) : ℝ) ≤ stT181 76 := by
  have hc : ((395817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227016486363/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((395817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c77 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((72049/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 601133/2000000) (δ := 569/62500000) (ψ := -371643/1000000) 181 125
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t77 : ((16419200919/400000000000 : ℚ) : ℝ) ≤ stT181 77 := by
  have hc : ((72039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16419200919/400000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((72039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c78 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-922539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686351/1000000) (δ := 9197/1000000000) (ψ := -371643/1000000) 181 126
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t78 : ((-522313613871/5000000000000 : ℚ) : ℝ) ≤ stT181 78 := by
  have hc : ((-922589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522313613871/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-922589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c79 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((904903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137389/1250000) (δ := 4553/500000000) (ψ := -371643/1000000) 181 126
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t79 : ((1018038347211/10000000000000 : ℚ) : ℝ) ≤ stT181 79 := by
  have hc : ((904853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1018038347211/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((904853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c80 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-52637/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 918559/2000000) (δ := 4553/500000000) (ψ := -371643/1000000) 181 126
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t80 : ((-29430567999/1000000000000 : ℚ) : ℝ) ≤ stT181 80 := by
  have hc : ((-52647/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29430567999/1000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-52647/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c81 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-117311/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5493987/10000000) (δ := 9113/1000000000) (ψ := -371643/1000000) 181 127
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t81 : ((-16294596369/250000000000 : ℚ) : ℝ) ≤ stT181 81 := by
  have hc : ((-117321/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16294596369/250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-117321/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c82 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((999729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58233/10000000) (δ := 909/100000000) (ψ := -371643/1000000) 181 127
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t82 : ((220792102977/2000000000000 : ℚ) : ℝ) ≤ stT181 82 := by
  have hc : ((999679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220792102977/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((999679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c83 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-602373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5543167/10000000) (δ := 9213/1000000000) (ψ := -371643/1000000) 181 127
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t83 : ((-661245388989/10000000000000 : ℚ) : ℝ) ≤ stT181 83 := by
  have hc : ((-602423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-661245388989/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-602423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c84 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-321619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4745589/10000000) (δ := 18183/1000000000) (ψ := -371643/1000000) 181 128
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t84 : ((-35096982921/1000000000000 : ℚ) : ℝ) ≤ stT181 84 := by
  have hc : ((-321669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35096982921/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-321669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c85 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((242607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1219/20000) (δ := 57/6250000) (ψ := -371643/1000000) 181 128
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t85 : ((131565304807/1250000000000 : ℚ) : ℝ) ≤ stT181 85 := by
  have hc : ((485189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131565304807/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((485189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c86 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-710339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295097/500000) (δ := 57/6250000) (ψ := -371643/1000000) 181 128
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t86 : ((-95754043699/1250000000000 : ℚ) : ℝ) ≤ stT181 86 := by
  have hc : ((-710389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95754043699/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-710389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c87 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-256201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1143679/2500000) (δ := 1141/125000000) (ψ := -371643/1000000) 181 129
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t87 : ((-274730028363/10000000000000 : ℚ) : ℝ) ≤ stT181 87 := by
  have hc : ((-256251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274730028363/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-256251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c88 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((242911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 596771/10000000) (δ := 2307/250000000) (ψ := -371643/1000000) 181 129
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t88 : ((517861059391/5000000000000 : ℚ) : ℝ) ≤ stT181 88 := by
  have hc : ((485797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517861059391/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((485797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c89 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-327099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2854897/5000000) (δ := 367/40000000) (ψ := -371643/1000000) 181 129
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t89 : ((-43343848219/625000000000 : ℚ) : ℝ) ≤ stT181 89 := by
  have hc : ((-81781/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43343848219/625000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-81781/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c90 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-395033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4942251/10000000) (δ := 573/62500000) (ψ := -371643/1000000) 181 130
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t90 : ((-416454224719/10000000000000 : ℚ) : ℝ) ≤ stT181 90 := by
  have hc : ((-395083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416454224719/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-395083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c91 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((999733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28903/5000000) (δ := 4567/250000000) (ψ := -371643/1000000) 181 130
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t91 : ((261987923493/2500000000000 : ℚ) : ℝ) ≤ stT181 91 := by
  have hc : ((999683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261987923493/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((999683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c92 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-417311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2501601/5000000) (δ := 1847/200000000) (ψ := -371643/1000000) 181 130
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t92 : ((-435129309853/10000000000000 : ℚ) : ℝ) ≤ stT181 92 := by
  have hc : ((-417361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435129309853/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-417361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c93 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-171201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5812829/10000000) (δ := 4621/500000000) (ψ := -371643/1000000) 181 131
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t93 : ((-44385045313/625000000000 : ℚ) : ℝ) ≤ stT181 93 := by
  have hc : ((-342427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44385045313/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-342427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c94 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((462591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486603/5000000) (δ := 4571/500000000) (ψ := -371643/1000000) 181 131
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t94 : ((238550143143/2500000000000 : ℚ) : ℝ) ≤ stT181 94 := by
  have hc : ((231283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238550143143/2500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((231283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c95 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((1397/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1907597/5000000) (δ := 9061/1000000000) (ψ := -371643/1000000) 181 131
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t95 : ((11453505403/2500000000000 : ℚ) : ℝ) ≤ stT181 95 := by
  have hc : ((22327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11453505403/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((22327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c96 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-961113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3577253/5000000) (δ := 4527/500000000) (ψ := -371643/1000000) 181 132
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t96 : ((-980983142223/10000000000000 : ℚ) : ℝ) ≤ stT181 96 := by
  have hc : ((-961163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-980983142223/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-961163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c97 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((137979/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2465339/10000000) (δ := 4527/500000000) (ψ := -371643/1000000) 181 132
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t97 : ((140083733909/2500000000000 : ℚ) : ℝ) ≤ stT181 97 := by
  have hc : ((275933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140083733909/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((275933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c98 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((161151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2175727/10000000) (δ := 4577/500000000) (ψ := -371643/1000000) 181 132
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t98 : ((40693594513/625000000000 : ℚ) : ℝ) ≤ stT181 98 := by
  have hc : ((322277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40693594513/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((322277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c99 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-90741/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 846211/1250000) (δ := 4577/500000000) (ψ := -371643/1000000) 181 132
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t99 : ((-22800794587/250000000000 : ℚ) : ℝ) ≤ stT181 99 := by
  have hc : ((-45373/50000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22800794587/250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-45373/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c100 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-184349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2195257/5000000) (δ := 2289/250000000) (ψ := -371643/1000000) 181 133
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t100 : ((-184399/10000000 : ℚ) : ℝ) ≤ stT181 100 := by
  have hc : ((-184399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184399/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-184399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c101 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((249749/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56021/5000000) (δ := 2289/250000000) (ψ := -371643/1000000) 181 133
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t101 : ((496994115501/5000000000000 : ℚ) : ℝ) ≤ stT181 101 := by
  have hc : ((499473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496994115501/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((499473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c102 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-254457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4570207/10000000) (δ := 9247/1000000000) (ψ := -371643/1000000) 181 133
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t102 : ((-62999899259/2500000000000 : ℚ) : ℝ) ≤ stT181 102 := by
  have hc : ((-254507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62999899259/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-254507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c103 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-35977/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6723121/10000000) (δ := 9239/1000000000) (ψ := -371643/1000000) 181 134
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t103 : ((-3545118807/40000000000 : ℚ) : ℝ) ≤ stT181 103 := by
  have hc : ((-35979/40000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3545118807/40000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-35979/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c104 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((589429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2351111/10000000) (δ := 9139/1000000000) (ψ := -371643/1000000) 181 134
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t104 : ((28896662991/500000000000 : ℚ) : ℝ) ≤ stT181 104 := by
  have hc : ((589379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28896662991/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((589379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c105 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((702683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123693/625000) (δ := 1133/125000000) (ψ := -371643/1000000) 181 134
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t105 : ((6856995447/100000000000 : ℚ) : ℝ) ≤ stT181 105 := by
  have hc : ((702633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6856995447/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((702633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c106 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-805479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31341/50000) (δ := 2291/250000000) (ψ := -371643/1000000) 181 134
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t106 : ((-391199520147/5000000000000 : ℚ) : ℝ) ≤ stT181 106 := by
  have hc : ((-805529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391199520147/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-805529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c107 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-484293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5190879/10000000) (δ := 9071/1000000000) (ψ := -371643/1000000) 181 135
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t107 : ((-468232298791/10000000000000 : ℚ) : ℝ) ≤ stT181 107 := by
  have hc : ((-484343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468232298791/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-484343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c108 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((923911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -981543/10000000) (δ := 9071/1000000000) (ψ := -371643/1000000) 181 135
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t108 : ((3555940989/40000000000 : ℚ) : ℝ) ≤ stT181 108 := by
  have hc : ((923861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3555940989/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((923861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c109 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((14547/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398621/1250000) (δ := 577/62500000) (ψ := -371643/1000000) 181 135
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t109 : ((13931100257/500000000000 : ℚ) : ℝ) ≤ stT181 109 := by
  have hc : ((29089/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13931100257/500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((29089/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c110 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-244349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292857/400000) (δ := 9171/1000000000) (ψ := -371643/1000000) 181 135
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t110 : ((-465979297749/5000000000000 : ℚ) : ℝ) ≤ stT181 110 := by
  have hc : ((-488723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465979297749/5000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-488723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c111 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-145271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4291459/10000000) (δ := 73/8000000) (ψ := -371643/1000000) 181 136
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t111 : ((-68966294859/5000000000000 : ℚ) : ℝ) ≤ stT181 111 := by
  have hc : ((-145321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68966294859/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-145321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c112 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((497827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233167/10000000) (δ := 4589/500000000) (ψ := -371643/1000000) 181 136
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t112 : ((235189292811/2500000000000 : ℚ) : ℝ) ≤ stT181 112 := by
  have hc : ((248901/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235189292811/2500000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((248901/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c113 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((27563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 757821/2000000) (δ := 73/8000000) (ψ := -371643/1000000) 181 136
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t113 : ((161909671/31250000000 : ℚ) : ℝ) ≤ stT181 113 := by
  have hc : ((13769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161909671/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((13769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c114 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-124939/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3887951/5000000) (δ := 4589/500000000) (ψ := -371643/1000000) 181 136
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t114 : ((-234043943833/2500000000000 : ℚ) : ℝ) ≤ stT181 114 := by
  have hc : ((-499781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234043943833/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-499781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c115 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-21227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1990031/5000000) (δ := 1837/200000000) (ψ := -371643/1000000) 181 137
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t115 : ((-3968181777/2000000000000 : ℚ) : ℝ) ≤ stT181 115 := by
  have hc : ((-21277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3968181777/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-21277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c116 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((999689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62317/10000000) (δ := 1837/200000000) (ψ := -371643/1000000) 181 137
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t116 : ((232035205041/2500000000000 : ℚ) : ℝ) ≤ stT181 116 := by
  have hc : ((999639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232035205041/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((999639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c117 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((42043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955463/2500000) (δ := 4559/500000000) (ψ := -371643/1000000) 181 137
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t117 : ((77645057/20000000000 : ℚ) : ℝ) ≤ stT181 117 := by
  have hc : ((41993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77645057/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((41993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c118 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-997379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 479559/625000) (δ := 1817/200000000) (ψ := -371643/1000000) 181 137
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t118 : ((-36728328067/400000000000 : ℚ) : ℝ) ≤ stT181 118 := by
  have hc : ((-997429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36728328067/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-997429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c119 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-11553/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108231/5000000) (δ := 1149/125000000) (ψ := -371643/1000000) 181 138
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t119 : ((-5297603521/500000000000 : ℚ) : ℝ) ≤ stT181 119 := by
  have hc : ((-5779/50000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5297603521/500000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-5779/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c120 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((492629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -429807/10000000) (δ := 9211/1000000000) (ψ := -371643/1000000) 181 138
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t120 : ((11242085337/125000000000 : ℚ) : ℝ) ≤ stT181 120 := by
  have hc : ((123151/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11242085337/125000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((123151/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c121 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((238321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16627/50000) (δ := 9211/1000000000) (ψ := -371643/1000000) 181 138
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t121 : ((21660978339/1000000000000 : ℚ) : ℝ) ≤ stT181 121 := by
  have hc : ((238271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21660978339/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((238271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c122 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-118587/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3524851/5000000) (δ := 1149/125000000) (ψ := -371643/1000000) 181 138
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t122 : ((-214738695267/2500000000000 : ℚ) : ℝ) ≤ stT181 122 := by
  have hc : ((-474373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214738695267/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-474373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c123 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-80629/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -310273/625000) (δ := 9199/1000000000) (ψ := -371643/1000000) 181 139
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t123 : ((-7270976713/200000000000 : ℚ) : ℝ) ≤ stT181 123 := by
  have hc : ((-80639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7270976713/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-80639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c124 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((867743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -260077/2000000) (δ := 9199/1000000000) (ψ := -371643/1000000) 181 139
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t124 : ((389605437009/5000000000000 : ℚ) : ℝ) ≤ stT181 124 := by
  have hc : ((867693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389605437009/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((867693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c125 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((118977/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 466837/2000000) (δ := 569/62500000) (ψ := -371643/1000000) 181 139
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t125 : ((106407296909/2000000000000 : ℚ) : ℝ) ≤ stT181 125 := by
  have hc : ((118967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106407296909/2000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((118967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c126 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-144183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1484949/2500000) (δ := 9199/1000000000) (ψ := -371643/1000000) 181 139
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t126 : ((-128457362103/2000000000000 : ℚ) : ℝ) ≤ stT181 126 := by
  have hc : ((-144193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128457362103/2000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-144193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c127 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-31473/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619111/1000000) (δ := 1137/125000000) (ψ := -371643/1000000) 181 140
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t127 : ((-1117182463/16000000000 : ℚ) : ℝ) ≤ stT181 127 := by
  have hc : ((-1259/1600 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1117182463/16000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-1259/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c128 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((12291/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1321031/5000000) (δ := 1137/125000000) (ψ := -371643/1000000) 181 140
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t128 : ((43450804397/1000000000000 : ℚ) : ℝ) ≤ stT181 128 := by
  have hc : ((49159/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43450804397/1000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((49159/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c129 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((93877/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109923/1250000) (δ := 9207/1000000000) (ψ := -371643/1000000) 181 140
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t129 : ((103312003/1250000000 : ℚ) : ℝ) ≤ stT181 129 := by
  have hc : ((5867/6250 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103312003/1250000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((5867/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c130 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-177691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4373589/10000000) (δ := 9207/1000000000) (ψ := -371643/1000000) 181 140
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t130 : ((-155889343719/10000000000000 : ℚ) : ℝ) ≤ stT181 130 := by
  have hc : ((-177741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155889343719/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-177741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c131 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-999987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7841051/10000000) (δ := 9107/1000000000) (ψ := -371643/1000000) 181 140
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t131 : ((-174747465417/2000000000000 : ℚ) : ℝ) ≤ stT181 131 := by
  have hc : ((-1000037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174747465417/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-1000037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c132 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-39643/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4425831/10000000) (δ := 9089/1000000000) (ψ := -371643/1000000) 181 141
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t132 : ((-34513535017/2000000000000 : ℚ) : ℝ) ≤ stT181 132 := by
  have hc : ((-39653/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34513535017/2000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-39653/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c133 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((459691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1010723/10000000) (δ := 9089/1000000000) (ψ := -371643/1000000) 181 141
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t133 : ((199290262797/2500000000000 : ℚ) : ℝ) ≤ stT181 133 := by
  have hc : ((229833/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199290262797/2500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((229833/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c134 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((580447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594699/2500000) (δ := 18189/1000000000) (ψ := -371643/1000000) 181 141
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t134 : ((125346598899/2500000000000 : ℚ) : ℝ) ≤ stT181 134 := by
  have hc : ((580397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125346598899/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((580397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c135 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-664219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5743111/10000000) (δ := 9089/1000000000) (ψ := -371643/1000000) 181 141
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t135 : ((-571711750347/10000000000000 : ℚ) : ℝ) ≤ stT181 135 := by
  have hc : ((-664269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-571711750347/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-664269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c136 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-17633/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6625357/10000000) (δ := 4541/500000000) (ψ := -371643/1000000) 181 142
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t136 : ((-7560515781/100000000000 : ℚ) : ℝ) ≤ stT181 136 := by
  have hc : ((-8817/10000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7560515781/100000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-8817/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c137 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((244183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3310297/10000000) (δ := 4591/500000000) (ψ := -371643/1000000) 181 142
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t137 : ((208576737481/10000000000000 : ℚ) : ℝ) ≤ stT181 137 := by
  have hc : ((244133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208576737481/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((244133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c138 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((99997/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97/50000) (δ := 4541/500000000) (ψ := -371643/1000000) 181 142
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t138 : ((1329981093/15625000000 : ℚ) : ℝ) ≤ stT181 138 := by
  have hc : ((12499/12500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1329981093/15625000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((12499/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c139 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((4193/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1623893/5000000) (δ := 9121/1000000000) (ψ := -371643/1000000) 181 142
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t139 : ((28446317097/1250000000000 : ℚ) : ℝ) ≤ stT181 139 := by
  have hc : ((134151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28446317097/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((134151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c140 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-427569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1622883/2500000) (δ := 4541/500000000) (ψ := -371643/1000000) 181 142
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t140 : ((-36138320707/500000000000 : ℚ) : ℝ) ≤ stT181 140 := by
  have hc : ((-213797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36138320707/500000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-213797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c141 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-36813/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187369/312500) (δ := 367/40000000) (ψ := -371643/1000000) 181 143
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t141 : ((-7751061739/125000000000 : ℚ) : ℝ) ≤ stT181 141 := by
  have hc : ((-73631/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7751061739/125000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-73631/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c142 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((218219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27979/100000) (δ := 367/40000000) (ψ := -371643/1000000) 181 143
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t142 : ((91552129557/2500000000000 : ℚ) : ℝ) ≤ stT181 142 := by
  have hc : ((109097/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91552129557/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((109097/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c143 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((988617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94391/2500000) (δ := 367/40000000) (ψ := -371643/1000000) 181 143
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t143 : ((413340622607/5000000000000 : ℚ) : ℝ) ≤ stT181 143 := by
  have hc : ((988567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((413340622607/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((988567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c144 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((4931/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441357/1250000) (δ := 1141/125000000) (ψ := -371643/1000000) 181 143
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t144 : ((65725807043/5000000000000 : ℚ) : ℝ) ≤ stT181 144 := by
  have hc : ((78871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65725807043/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((78871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c145 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-444271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3331191/5000000) (δ := 363/40000000) (ψ := -371643/1000000) 181 143
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t145 : ((-9224195867/125000000000 : ℚ) : ℝ) ≤ stT181 145 := by
  have hc : ((-55537/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9224195867/125000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-55537/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c146 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-719749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2967797/5000000) (δ := 2267/250000000) (ψ := -371643/1000000) 181 144
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t146 : ((-297854985597/5000000000000 : ℚ) : ℝ) ≤ stT181 146 := by
  have hc : ((-719799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297854985597/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-719799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c147 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((41873/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1423437/5000000) (δ := 1827/200000000) (ψ := -371643/1000000) 181 144
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t147 : ((4316517531/125000000000 : ℚ) : ℝ) ≤ stT181 147 := by
  have hc : ((10467/25000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4316517531/125000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((10467/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c148 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((996097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11047/500000) (δ := 2267/250000000) (ψ := -371643/1000000) 181 144
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t148 : ((409372328859/5000000000000 : ℚ) : ℝ) ≤ stT181 148 := by
  have hc : ((996047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409372328859/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((996047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c149 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((65127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81703/250000) (δ := 573/62500000) (ψ := -371643/1000000) 181 144
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t149 : ((106687633899/5000000000000 : ℚ) : ℝ) ≤ stT181 149 := by
  have hc : ((130229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106687633899/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((130229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c150 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-3247/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98357/156250) (δ := 1847/200000000) (ψ := -371643/1000000) 181 144
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t150 : ((-3314161323/50000000000 : ℚ) : ℝ) ≤ stT181 150 := by
  have hc : ((-4059/5000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3314161323/50000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-4059/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c151 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-837/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3203217/5000000) (δ := 9143/1000000000) (ψ := -371643/1000000) 181 145
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t151 : ((-13623641649/200000000000 : ℚ) : ℝ) ≤ stT181 151 := by
  have hc : ((-16741/20000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13623641649/200000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-16741/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c152 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((201559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3419617/10000000) (δ := 9243/1000000000) (ψ := -371643/1000000) 181 145
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t152 : ((163445360463/10000000000000 : ℚ) : ℝ) ≤ stT181 152 := by
  have hc : ((201509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163445360463/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((201509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c153 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((122959/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226197/5000000) (δ := 453/50000000) (ψ := -371643/1000000) 181 145
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t153 : ((99401396643/1250000000000 : ℚ) : ℝ) ≤ stT181 153 := by
  have hc : ((491811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99401396643/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((491811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c154 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((541813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 623877/2500000) (δ := 9143/1000000000) (ψ := -371643/1000000) 181 145
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t154 : ((218282272093/5000000000000 : ℚ) : ℝ) ≤ stT181 154 := by
  have hc : ((541763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218282272093/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((541763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c155 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-281879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2712157/5000000) (δ := 453/50000000) (ψ := -371643/1000000) 181 145
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t155 : ((-707596659/15625000000 : ℚ) : ℝ) ≤ stT181 155 := by
  have hc : ((-17619/31250 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-707596659/15625000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-17619/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c156 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-981601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7373667/10000000) (δ := 9053/1000000000) (ψ := -371643/1000000) 181 146
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t156 : ((-785950038291/10000000000000 : ℚ) : ℝ) ≤ stT181 156 := by
  have hc : ((-981651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-785950038291/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-981651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c157 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-44059/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2241141/5000000) (δ := 37/4000000) (ψ := -371643/1000000) 181 146
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t157 : ((-35170896003/2000000000000 : ℚ) : ℝ) ≤ stT181 157 := by
  have hc : ((-44069/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35170896003/2000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-44069/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c158 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((199969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1609269/10000000) (δ := 37/4000000) (ψ := -371643/1000000) 181 146
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t158 : ((318153586541/5000000000000 : ℚ) : ℝ) ≤ stT181 158 := by
  have hc : ((399913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318153586541/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((399913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c159 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((878417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311411/2500000) (δ := 37/4000000) (ψ := -371643/1000000) 181 146
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t159 : ((696589827717/10000000000000 : ℚ) : ℝ) ≤ stT181 159 := by
  have hc : ((878367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((696589827717/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((878367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c160 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-62219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2041319/5000000) (δ := 37/4000000) (ψ := -371643/1000000) 181 146
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t160 : ((-4922800333/1000000000000 : ℚ) : ℝ) ≤ stT181 160 := by
  have hc : ((-62269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4922800333/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-62269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c161 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-928361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6901939/10000000) (δ := 183/20000000) (ψ := -371643/1000000) 181 146
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t161 : ((-731690921621/10000000000000 : ℚ) : ℝ) ≤ stT181 161 := by
  have hc : ((-928411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731690921621/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-928411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c162 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-738513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1200829/2000000) (δ := 4623/500000000) (ψ := -371643/1000000) 181 147
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t162 : ((-23210819401/400000000000 : ℚ) : ℝ) ≤ stT181 162 := by
  have hc : ((-738563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23210819401/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-738563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c163 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((4363/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -643901/2000000) (δ := 4573/500000000) (ψ := -371643/1000000) 181 147
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t163 : ((5466802333/250000000000 : ℚ) : ℝ) ≤ stT181 163 := by
  have hc : ((139591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5466802333/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((139591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c164 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((491853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112981/2500000) (δ := 9157/1000000000) (ψ := -371643/1000000) 181 147
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t164 : ((24003296669/312500000000 : ℚ) : ℝ) ≤ stT181 164 := by
  have hc : ((122957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24003296669/312500000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((122957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c165 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((121239/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2298823/10000000) (δ := 4573/500000000) (ψ := -371643/1000000) 181 147
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t165 : ((47188267021/1000000000000 : ℚ) : ℝ) ≤ stT181 165 := by
  have hc : ((121229/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47188267021/1000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((121229/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c166 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-4281/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1258241/2500000) (δ := 9057/1000000000) (ψ := -371643/1000000) 181 147
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t166 : ((-6646181013/200000000000 : ℚ) : ℝ) ≤ stT181 166 := by
  have hc : ((-8563/20000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6646181013/200000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-8563/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c167 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-999147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1937681/2500000) (δ := 4573/500000000) (ψ := -371643/1000000) 181 147
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t167 : ((-12081290927/156250000000 : ℚ) : ℝ) ≤ stT181 167 := by
  have hc : ((-999197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12081290927/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-999197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c168 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-506837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5255769/10000000) (δ := 9139/1000000000) (ψ := -371643/1000000) 181 148
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t168 : ((-391071937579/10000000000000 : ℚ) : ℝ) ≤ stT181 168 := by
  have hc : ((-506887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391071937579/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-506887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c169 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((516439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80321/312500) (δ := 9139/1000000000) (ψ := -371643/1000000) 181 148
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t169 : ((39722191047/1000000000000 : ℚ) : ℝ) ≤ stT181 169 := by
  have hc : ((516389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39722191047/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((516389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c170 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((999211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49671/5000000) (δ := 9239/1000000000) (ψ := -371643/1000000) 181 148
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t170 : ((191580129301/2500000000000 : ℚ) : ℝ) ≤ stT181 170 := by
  have hc : ((999161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191580129301/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((999161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c171 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((452419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27533/100000) (δ := 9139/1000000000) (ψ := -371643/1000000) 181 148
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t171 : ((345935169311/10000000000000 : ℚ) : ℝ) ≤ stT181 171 := by
  have hc : ((452369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345935169311/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((452369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c172 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-552963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2695891/5000000) (δ := 9239/1000000000) (ψ := -371643/1000000) 181 148
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t172 : ((-421668541409/10000000000000 : ℚ) : ℝ) ≤ stT181 172 := by
  have hc : ((-553013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421668541409/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-553013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c173 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-997927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7692993/10000000) (δ := 9071/1000000000) (ψ := -371643/1000000) 181 149
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t173 : ((-379373970711/5000000000000 : ℚ) : ℝ) ≤ stT181 173 := by
  have hc : ((-997977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379373970711/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-997977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c174 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-446787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5084919/10000000) (δ := 2283/250000000) (ψ := -371643/1000000) 181 149
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t174 : ((-338746682863/10000000000000 : ℚ) : ℝ) ≤ stT181 174 := by
  have hc : ((-446837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338746682863/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-446837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c175 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((543067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2491777/10000000) (δ := 9071/1000000000) (ψ := -371643/1000000) 181 149
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t175 : ((51310219347/1250000000000 : ℚ) : ℝ) ≤ stT181 175 := by
  have hc : ((543017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51310219347/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((543017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c176 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((999401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10821/1250000) (δ := 9071/1000000000) (ψ := -371643/1000000) 181 149
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t176 : ((376644399039/5000000000000 : ℚ) : ℝ) ≤ stT181 176 := by
  have hc : ((999351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376644399039/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((999351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c177 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((488753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1325171/5000000) (δ := 577/62500000) (ψ := -371643/1000000) 181 149
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t177 : ((183665827569/5000000000000 : ℚ) : ℝ) ≤ stT181 177 := by
  have hc : ((488703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183665827569/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((488703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c178 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-97471/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5199637/10000000) (δ := 9071/1000000000) (ψ := -371643/1000000) 181 149
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t178 : ((-18266282223/500000000000 : ℚ) : ℝ) ≤ stT181 178 := by
  have hc : ((-97481/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18266282223/500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-97481/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c179 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-499431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3867339/5000000) (δ := 9171/1000000000) (ψ := -371643/1000000) 181 149
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t179 : ((-364561909/4882812500 : ℚ) : ℝ) ≤ stT181 179 := by
  have hc : ((-15608/15625 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364561909/4882812500 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-15608/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c180 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-143251/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -681551/1250000) (δ := 4539/500000000) (ψ := -371643/1000000) 181 150
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t180 : ((-53391154653/1250000000000 : ℚ) : ℝ) ≤ stT181 180 := by
  have hc : ((-286527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53391154653/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-286527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c181 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((1913/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -736367/2500000) (δ := 369/40000000) (ψ := -371643/1000000) 181 150
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t181 : ((2843471197/100000000000 : ℚ) : ℝ) ≤ stT181 181 := by
  have hc : ((7651/20000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2843471197/100000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((7651/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c182 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((983673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226187/5000000) (δ := 369/40000000) (ψ := -371643/1000000) 181 150
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t182 : ((729109565127/10000000000000 : ℚ) : ℝ) ≤ stT181 182 := by
  have hc : ((983623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((729109565127/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((983623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c183 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((68889/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20271/100000) (δ := 73/8000000) (ψ := -371643/1000000) 181 150
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t183 : ((12730124841/250000000000 : ℚ) : ℝ) ≤ stT181 183 := by
  have hc : ((17221/25000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12730124841/250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((17221/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c184 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-56123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1123261/2500000) (δ := 73/8000000) (ψ := -371643/1000000) 181 150
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t184 : ((-8276730391/500000000000 : ℚ) : ℝ) ≤ stT181 184 := by
  have hc : ((-112271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8276730391/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-112271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c185 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-233679/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6945639/10000000) (δ := 369/40000000) (ψ := -371643/1000000) 181 150
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t185 : ((-68725398469/1000000000000 : ℚ) : ℝ) ≤ stT181 185 := by
  have hc : ((-467383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68725398469/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-467383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c186 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-25571/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6322987/10000000) (δ := 9117/1000000000) (ψ := -371643/1000000) 181 151
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t186 : ((-75002893749/1250000000000 : ℚ) : ℝ) ≤ stT181 186 := by
  have hc : ((-409161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75002893749/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-409161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c187 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((12123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1948341/5000000) (δ := 9117/1000000000) (ψ := -371643/1000000) 181 151
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t187 : ((1103580857/1250000000000 : ℚ) : ℝ) ≤ stT181 187 := by
  have hc : ((12073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1103580857/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((12073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c188 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((33163/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -370841/2500000) (δ := 9217/1000000000) (ψ := -371643/1000000) 181 151
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t188 : ((6046278291/100000000000 : ℚ) : ℝ) ≤ stT181 188 := by
  have hc : ((33161/40000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6046278291/100000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((33161/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c189 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((233363/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 458597/5000000) (δ := 9117/1000000000) (ψ := -371643/1000000) 181 151
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t189 : ((10608580431/156250000000 : ℚ) : ℝ) ≤ stT181 189 := by
  have hc : ((466701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10608580431/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((466701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c190 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((246223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3305037/10000000) (δ := 4593/500000000) (ψ := -371643/1000000) 181 151
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t190 : ((44648150837/2500000000000 : ℚ) : ℝ) ≤ stT181 190 := by
  have hc : ((246173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44648150837/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((246173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c191 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-645257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568039/1000000) (δ := 9117/1000000000) (ψ := -371643/1000000) 181 151
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t191 : ((-18677120501/400000000000 : ℚ) : ℝ) ≤ stT181 191 := by
  have hc : ((-645307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18677120501/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-645307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c192 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-498567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7664663/10000000) (δ := 9193/1000000000) (ψ := -371643/1000000) 181 152
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t192 : ((-1405577591/19531250000 : ℚ) : ℝ) ≤ stT181 192 := by
  have hc : ((-15581/15625 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1405577591/19531250000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-15581/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c193 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-263391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166063/312500) (δ := 9193/1000000000) (ψ := -371643/1000000) 181 152
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t193 : ((-2962672679/78125000000 : ℚ) : ℝ) ≤ stT181 193 := by
  have hc : ((-32927/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2962672679/78125000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-32927/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c194 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((92869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371937/1250000) (δ := 9193/1000000000) (ψ := -371643/1000000) 181 152
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t194 : ((66667067027/2500000000000 : ℚ) : ℝ) ≤ stT181 194 := by
  have hc : ((185713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66667067027/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((185713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c195 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((966491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -649013/10000000) (δ := 911/100000000) (ψ := -371643/1000000) 181 152
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t195 : ((346040965137/5000000000000 : ℚ) : ℝ) ≤ stT181 195 := by
  have hc : ((966441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346040965137/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((966441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c196 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((393079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166557/1000000) (δ := 9093/1000000000) (ψ := -371643/1000000) 181 152
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t196 : ((28075257639/500000000000 : ℚ) : ℝ) ≤ stT181 196 := by
  have hc : ((196527/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28075257639/500000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((196527/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c197 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-8279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 992097/2500000) (δ := 9193/1000000000) (ψ := -371643/1000000) 181 152
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t197 : ((-369772449/312500000000 : ℚ) : ℝ) ≤ stT181 197 := by
  have hc : ((-519/31250 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369772449/312500000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-519/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c198 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-803419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6259531/10000000) (δ := 9093/1000000000) (ψ := -371643/1000000) 181 152
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t198 : ((-57100131423/1000000000000 : ℚ) : ℝ) ≤ stT181 198 := by
  have hc : ((-803469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57100131423/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-803469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c199 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-24067/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1792207/2500000) (δ := 9103/1000000000) (ψ := -371643/1000000) 181 153
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t199 : ((-34123098393/500000000000 : ℚ) : ℝ) ≤ stT181 199 := by
  have hc : ((-96273/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34123098393/500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-96273/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c200 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-3797/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76573/156250) (δ := 9203/1000000000) (ψ := -371643/1000000) 181 153
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t200 : ((-1074095533/40000000000 : ℚ) : ℝ) ≤ stT181 200 := by
  have hc : ((-1519/4000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1074095533/40000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-1519/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c201 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((3069/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2643783/10000000) (δ := 9203/1000000000) (ψ := -371643/1000000) 181 153
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t201 : ((6926346831/200000000000 : ℚ) : ℝ) ≤ stT181 201 := by
  have hc : ((49099/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6926346831/200000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((49099/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c202 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((61709/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -398161/10000000) (δ := 9103/1000000000) (ψ := -371643/1000000) 181 153
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t202 : ((347328548259/5000000000000 : ℚ) : ℝ) ≤ stT181 202 := by
  have hc : ((493647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((347328548259/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((493647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c203 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((18553/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91821/500000) (δ := 91/10000000) (ψ := -371643/1000000) 181 153
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t203 : ((26041536717/500000000000 : ℚ) : ℝ) ≤ stT181 203 := by
  have hc : ((74207/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26041536717/500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((74207/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c204 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-53181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 812001/2000000) (δ := 91/10000000) (ψ := -371643/1000000) 181 153
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t204 : ((-37269205571/10000000000000 : ℚ) : ℝ) ≤ stT181 204 := by
  have hc : ((-53231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37269205571/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-53231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c205 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-100819/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 627273/1000000) (δ := 91/10000000) (ψ := -371643/1000000) 181 153
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t205 : ((-281677920731/5000000000000 : ℚ) : ℝ) ≤ stT181 205 := by
  have hc : ((-403301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281677920731/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-403301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c206 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-121167/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3616639/5000000) (δ := 1137/125000000) (ψ := -371643/1000000) 181 154
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t206 : ((-168851046331/2500000000000 : ℚ) : ℝ) ≤ stT181 206 := by
  have hc : ((-484693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168851046331/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-484693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c207 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-107841/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5042001/10000000) (δ := 9207/1000000000) (ψ := -371643/1000000) 181 154
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t207 : ((-149926934643/5000000000000 : ℚ) : ℝ) ≤ stT181 207 := by
  have hc : ((-215707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149926934643/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-215707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c208 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((82699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -715317/2500000) (δ := 9107/1000000000) (ψ := -371643/1000000) 181 154
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t208 : ((458675883/16000000000 : ℚ) : ℝ) ≤ stT181 208 := by
  have hc : ((82689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458675883/16000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((82689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c209 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((192409/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172747/2500000) (δ := 2299/250000000) (ψ := -371643/1000000) 181 154
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t209 : ((66542540943/1000000000000 : ℚ) : ℝ) ≤ stT181 209 := by
  have hc : ((192399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66542540943/1000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((192399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c210 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((832289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1468931/10000000) (δ := 9207/1000000000) (ψ := -371643/1000000) 181 154
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t210 : ((114859801107/2000000000000 : ℚ) : ℝ) ≤ stT181 210 := by
  have hc : ((832239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114859801107/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((832239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c211 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((123053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3618577/10000000) (δ := 1137/125000000) (ψ := -371643/1000000) 181 154
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t211 : ((21169677321/2500000000000 : ℚ) : ℝ) ≤ stT181 211 := by
  have hc : ((123003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21169677321/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((123003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c212 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-668671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2879021/5000000) (δ := 2299/250000000) (ψ := -371643/1000000) 181 154
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t212 : ((-459279588963/10000000000000 : ℚ) : ℝ) ≤ stT181 212 := by
  have hc : ((-668721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459279588963/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-668721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c213 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-99991/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7820501/10000000) (δ := 4557/500000000) (ψ := -371643/1000000) 181 155
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t213 : ((-17129039811/250000000000 : ℚ) : ℝ) ≤ stT181 213 := by
  have hc : ((-24999/25000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17129039811/250000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-24999/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c214 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-81443/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1425259/2500000) (δ := 4607/500000000) (ψ := -371643/1000000) 181 155
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t214 : ((-111355134021/2500000000000 : ℚ) : ℝ) ≤ stT181 214 := by
  have hc : ((-325797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111355134021/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-325797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c215 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((133801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3591481/10000000) (δ := 4607/500000000) (ψ := -371643/1000000) 181 155
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t215 : ((45608689747/5000000000000 : ℚ) : ℝ) ≤ stT181 215 := by
  have hc : ((133751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45608689747/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((133751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c216 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((413603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14917/100000) (δ := 4607/500000000) (ψ := -371643/1000000) 181 155
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t216 : ((140701923857/2500000000000 : ℚ) : ℝ) ≤ stT181 216 := by
  have hc : ((206789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140701923857/2500000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((206789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c217 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((485747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37397/625000) (δ := 4557/500000000) (ψ := -371643/1000000) 181 155
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t217 : ((41216183171/625000000000 : ℚ) : ℝ) ≤ stT181 217 := by
  have hc : ((242861/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41216183171/625000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((242861/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c218 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((239393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2678811/10000000) (δ := 9089/1000000000) (ψ := -371643/1000000) 181 155
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t218 : ((4053008897/125000000000 : ℚ) : ℝ) ≤ stT181 218 := by
  have hc : ((29921/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4053008897/125000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((29921/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c219 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-161601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 593721/1250000) (δ := 4557/500000000) (ψ := -371643/1000000) 181 155
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t219 : ((-27304207497/1250000000000 : ℚ) : ℝ) ≤ stT181 219 := by
  have hc : ((-80813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27304207497/1250000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-80813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c220 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-914273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6811267/10000000) (δ := 9189/1000000000) (ψ := -371643/1000000) 181 155
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t220 : ((-3082182833/50000000000 : ℚ) : ℝ) ≤ stT181 220 := by
  have hc : ((-914323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3082182833/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-914323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c221 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-45979/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3422259/5000000) (δ := 9081/1000000000) (ψ := -371643/1000000) 181 156
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t221 : ((-61861027099/1000000000000 : ℚ) : ℝ) ≤ stT181 221 := by
  have hc : ((-91963/100000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61861027099/1000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-91963/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c222 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-171387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4801661/10000000) (δ := 4611/500000000) (ψ := -371643/1000000) 181 156
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t222 : ((-28761090921/1250000000000 : ℚ) : ℝ) ≤ stT181 222 := by
  have hc : ((-42853/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28761090921/1250000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-42853/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c223 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((447187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553589/2000000) (δ := 4611/500000000) (ψ := -371643/1000000) 181 156
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t223 : ((299424844913/10000000000000 : ℚ) : ℝ) ≤ stT181 223 := by
  have hc : ((447137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299424844913/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((447137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c224 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((478061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29733/400000) (δ := 9181/1000000000) (ψ := -371643/1000000) 181 156
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t224 : ((79850296877/1250000000000 : ℚ) : ℝ) ≤ stT181 224 := by
  have hc : ((119509/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79850296877/1250000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((119509/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c225 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((873273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1272291/10000000) (δ := 9181/1000000000) (ψ := -371643/1000000) 181 156
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t225 : ((291074042259/5000000000000 : ℚ) : ℝ) ≤ stT181 225 := by
  have hc : ((873223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291074042259/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((873223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c226 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((256333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131157/400000) (δ := 18181/1000000000) (ψ := -371643/1000000) 181 156
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t226 : ((17047688877/1000000000000 : ℚ) : ℝ) ≤ stT181 226 := by
  have hc : ((256283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17047688877/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((256283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c227 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-8032/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1055347/2000000) (δ := 9181/1000000000) (ψ := -371643/1000000) 181 156
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t227 : ((-42652397619/1250000000000 : ℚ) : ℝ) ≤ stT181 227 := by
  have hc : ((-257049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42652397619/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-257049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c228 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-486223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 454109/625000) (δ := 9181/1000000000) (ψ := -371643/1000000) 181 156
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t228 : ((-40253250527/625000000000 : ℚ) : ℝ) ≤ stT181 228 := by
  have hc : ((-60781/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40253250527/625000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-60781/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c229 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-848933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3230949/5000000) (δ := 4537/500000000) (ψ := -371643/1000000) 181 157
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t229 : ((-561024097077/10000000000000 : ℚ) : ℝ) ≤ stT181 229 := by
  have hc : ((-848983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-561024097077/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-848983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c230 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-223391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224511/500000) (δ := 4587/500000000) (ψ := -371643/1000000) 181 157
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t230 : ((-147332750021/10000000000000 : ℚ) : ℝ) ≤ stT181 230 := by
  have hc : ((-223441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147332750021/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-223441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c231 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((531151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263547/5000000) (δ := 4587/500000000) (ψ := -371643/1000000) 181 157
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t231 : ((349438434051/10000000000000 : ℚ) : ℝ) ≤ stT181 231 := by
  have hc : ((531101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349438434051/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((531101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c232 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((121737/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22899/400000) (δ := 4587/500000000) (ψ := -371643/1000000) 181 157
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t232 : ((79920132759/1250000000000 : ℚ) : ℝ) ≤ stT181 232 := by
  have hc : ((486923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79920132759/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((486923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c233 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((852781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1373773/10000000) (δ := 4537/500000000) (ψ := -371643/1000000) 181 157
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t233 : ((558641985451/10000000000000 : ℚ) : ℝ) ≤ stT181 233 := by
  have hc : ((852731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558641985451/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((852731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c234 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((243641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662339/2000000) (δ := 9129/1000000000) (ψ := -371643/1000000) 181 157
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t234 : ((3981007713/250000000000 : ℚ) : ℝ) ≤ stT181 234 := by
  have hc : ((243591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3981007713/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((243591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c235 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-125463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655167/1250000) (δ := 9129/1000000000) (ψ := -371643/1000000) 181 157
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t235 : ((-163702614879/5000000000000 : ℚ) : ℝ) ≤ stT181 235 := by
  have hc : ((-250951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163702614879/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-250951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c236 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-962023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7162787/10000000) (δ := 9229/1000000000) (ψ := -371643/1000000) 181 157
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t236 : ((-125251321797/2000000000000 : ℚ) : ℝ) ≤ stT181 236 := by
  have hc : ((-962073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125251321797/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-962073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c237 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-220719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6631871/10000000) (δ := 9067/1000000000) (ψ := -371643/1000000) 181 158
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t237 : ((-28676112091/500000000000 : ℚ) : ℝ) ≤ stT181 237 := by
  have hc : ((-441463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28676112091/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-441463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c238 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-157213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236331/500000) (δ := 9167/1000000000) (ψ := -371643/1000000) 181 158
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t238 : ((-12740287569/625000000000 : ℚ) : ℝ) ≤ stT181 238 := by
  have hc : ((-78619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12740287569/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-78619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c239 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((106273/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -707333/2500000) (δ := 2309/250000000) (ψ := -371643/1000000) 181 158
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t239 : ((68734179383/2500000000000 : ℚ) : ℝ) ≤ stT181 239 := by
  have hc : ((212521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68734179383/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((212521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c240 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((465073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -234991/2500000) (δ := 9067/1000000000) (ψ := -371643/1000000) 181 158
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t240 : ((37523386107/625000000000 : ℚ) : ℝ) ≤ stT181 240 := by
  have hc : ((58131/62500 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37523386107/625000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((58131/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c241 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((232479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 941531/10000000) (δ := 9067/1000000000) (ψ := -371643/1000000) 181 158
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t241 : ((74872345387/1250000000000 : ℚ) : ℝ) ≤ stT181 241 := by
  have hc : ((464933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74872345387/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((464933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c242 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((215093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2815243/10000000) (δ := 9067/1000000000) (ψ := -371643/1000000) 181 158
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t242 : ((4320339751/156250000000 : ℚ) : ℝ) ≤ stT181 242 := by
  have hc : ((53767/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4320339751/156250000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((53767/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c243 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-59427/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4681217/10000000) (δ := 9167/1000000000) (ψ := -371643/1000000) 181 158
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t243 : ((-38128894937/2000000000000 : ℚ) : ℝ) ≤ stT181 243 := by
  have hc : ((-59437/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38128894937/2000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-59437/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c244 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-172987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 817443/1250000) (δ := 9167/1000000000) (ψ := -371643/1000000) 181 158
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t244 : ((-22150016889/400000000000 : ℚ) : ℝ) ≤ stT181 244 := by
  have hc : ((-172997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22150016889/400000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-172997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c245 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-488541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7317717/10000000) (δ := 913/50000000) (ψ := -371643/1000000) 181 159
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t245 : ((-156066790191/2500000000000 : ℚ) : ℝ) ≤ stT181 245 := by
  have hc : ((-244283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156066790191/2500000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-244283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c246 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((-72529/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2737263/5000000) (δ := 229/25000000) (ψ := -371643/1000000) 181 159
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t246 : ((-184987228357/5000000000000 : ℚ) : ℝ) ≤ stT181 246 := by
  have hc : ((-290141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184987228357/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-290141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c247 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((28753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -454853/1250000) (δ := 229/25000000) (ψ := -371643/1000000) 181 159
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t247 : ((9143560151/1250000000000 : ℚ) : ℝ) ≤ stT181 247 := by
  have hc : ((57481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9143560151/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((57481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c248 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((374509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1810543/10000000) (δ := 229/25000000) (ψ := -371643/1000000) 181 159
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t248 : ((11889867/250000000 : ℚ) : ℝ) ≤ stT181 248 := by
  have hc : ((93621/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11889867/250000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((93621/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c249 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((999991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10363/10000000) (δ := 9243/1000000000) (ψ := -371643/1000000) 181 159
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t249 : ((158421652571/2500000000000 : ℚ) : ℝ) ≤ stT181 249 := by
  have hc : ((999941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158421652571/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((999941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_c250 :
    |Real.cos (((181 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((372717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 456007/2500000) (δ := 9143/1000000000) (ψ := -371643/1000000) 181 159
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st181_t250 : ((11785545943/250000000000 : ℚ) : ℝ) ≤ stT181 250 := by
  have hc : ((93173/125000 : ℚ) : ℝ)
      ≤ Real.cos (((181 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st181_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11785545943/250000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((93173/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st181_p1 : ((465841/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT181 (i+1) := by
  rw [Finset.sum_range_one]
  exact st181_t1

theorem st181_p2 : ((16288489011181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT181 (i+1))
      = (∑ i ∈ Finset.range 1, stT181 (i+1)) + stT181 2 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 1
    simpa using h
  have hprev := st181_p1
  have hstep := st181_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p3 : ((14744481103891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT181 (i+1))
      = (∑ i ∈ Finset.range 2, stT181 (i+1)) + stT181 3 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 2
    simpa using h
  have hprev := st181_p2
  have hstep := st181_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p4 : ((19740901103891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT181 (i+1))
      = (∑ i ∈ Finset.range 3, stT181 (i+1)) + stT181 4 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 3
    simpa using h
  have hprev := st181_p3
  have hstep := st181_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p5 : ((3158198862631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT181 (i+1))
      = (∑ i ∈ Finset.range 4, stT181 (i+1)) + stT181 5 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 4
    simpa using h
  have hprev := st181_p4
  have hstep := st181_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p6 : ((13924670879773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT181 (i+1))
      = (∑ i ∈ Finset.range 5, stT181 (i+1)) + stT181 6 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 5
    simpa using h
  have hprev := st181_p5
  have hstep := st181_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p7 : ((16758542120941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT181 (i+1))
      = (∑ i ∈ Finset.range 6, stT181 (i+1)) + stT181 7 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 6
    simpa using h
  have hprev := st181_p6
  have hstep := st181_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p8 : ((20192096207089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT181 (i+1))
      = (∑ i ∈ Finset.range 7, stT181 (i+1)) + stT181 8 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 7
    simpa using h
  have hprev := st181_p7
  have hstep := st181_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p9 : ((18153962466129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT181 (i+1))
      = (∑ i ∈ Finset.range 8, stT181 (i+1)) + stT181 9 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 8
    simpa using h
  have hprev := st181_p8
  have hstep := st181_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p10 : ((15719517532887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT181 (i+1))
      = (∑ i ∈ Finset.range 9, stT181 (i+1)) + stT181 10 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 9
    simpa using h
  have hprev := st181_p9
  have hstep := st181_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p11 : ((8853628957077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT181 (i+1))
      = (∑ i ∈ Finset.range 10, stT181 (i+1)) + stT181 11 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 10
    simpa using h
  have hprev := st181_p10
  have hstep := st181_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p12 : ((7947320176293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT181 (i+1))
      = (∑ i ∈ Finset.range 11, stT181 (i+1)) + stT181 12 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 11
    simpa using h
  have hprev := st181_p11
  have hstep := st181_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p13 : ((9259965029793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT181 (i+1))
      = (∑ i ∈ Finset.range 12, stT181 (i+1)) + stT181 13 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 12
    simpa using h
  have hprev := st181_p12
  have hstep := st181_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p14 : ((10420272848063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT181 (i+1))
      = (∑ i ∈ Finset.range 13, stT181 (i+1)) + stT181 14 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 13
    simpa using h
  have hprev := st181_p13
  have hstep := st181_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p15 : ((11588080200583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT181 (i+1))
      = (∑ i ∈ Finset.range 14, stT181 (i+1)) + stT181 15 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 14
    simpa using h
  have hprev := st181_p14
  have hstep := st181_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p16 : ((12716486450583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT181 (i+1))
      = (∑ i ∈ Finset.range 15, stT181 (i+1)) + stT181 16 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 15
    simpa using h
  have hprev := st181_p15
  have hstep := st181_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p17 : ((12170315457039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT181 (i+1))
      = (∑ i ∈ Finset.range 16, stT181 (i+1)) + stT181 17 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 16
    simpa using h
  have hprev := st181_p16
  have hstep := st181_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p18 : ((11653665443531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT181 (i+1))
      = (∑ i ∈ Finset.range 17, stT181 (i+1)) + stT181 18 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 17
    simpa using h
  have hprev := st181_p17
  have hstep := st181_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p19 : ((3122118690869/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT181 (i+1))
      = (∑ i ∈ Finset.range 18, stT181 (i+1)) + stT181 19 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 18
    simpa using h
  have hprev := st181_p18
  have hstep := st181_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p20 : ((2947561160483/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT181 (i+1))
      = (∑ i ∈ Finset.range 19, stT181 (i+1)) + stT181 20 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 19
    simpa using h
  have hprev := st181_p19
  have hstep := st181_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p21 : ((5939070294797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT181 (i+1))
      = (∑ i ∈ Finset.range 20, stT181 (i+1)) + stT181 21 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 20
    simpa using h
  have hprev := st181_p20
  have hstep := st181_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p22 : ((2545750763681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT181 (i+1))
      = (∑ i ∈ Finset.range 21, stT181 (i+1)) + stT181 22 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 21
    simpa using h
  have hprev := st181_p21
  have hstep := st181_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p23 : ((4781324948829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT181 (i+1))
      = (∑ i ∈ Finset.range 22, stT181 (i+1)) + stT181 23 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 22
    simpa using h
  have hprev := st181_p22
  have hstep := st181_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p24 : ((22329542803767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT181 (i+1))
      = (∑ i ∈ Finset.range 23, stT181 (i+1)) + stT181 24 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 23
    simpa using h
  have hprev := st181_p23
  have hstep := st181_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p25 : ((22771238803767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT181 (i+1))
      = (∑ i ∈ Finset.range 24, stT181 (i+1)) + stT181 25 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 24
    simpa using h
  have hprev := st181_p24
  have hstep := st181_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p26 : ((24460959432079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT181 (i+1))
      = (∑ i ∈ Finset.range 25, stT181 (i+1)) + stT181 26 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 25
    simpa using h
  have hprev := st181_p25
  have hstep := st181_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p27 : ((26385132267079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT181 (i+1))
      = (∑ i ∈ Finset.range 26, stT181 (i+1)) + stT181 27 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 26
    simpa using h
  have hprev := st181_p26
  have hstep := st181_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p28 : ((28181944787527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT181 (i+1))
      = (∑ i ∈ Finset.range 27, stT181 (i+1)) + stT181 28 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 27
    simpa using h
  have hprev := st181_p27
  have hstep := st181_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p29 : ((3738014320991/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT181 (i+1))
      = (∑ i ∈ Finset.range 28, stT181 (i+1)) + stT181 29 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 28
    simpa using h
  have hprev := st181_p28
  have hstep := st181_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p30 : ((31679068930531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT181 (i+1))
      = (∑ i ∈ Finset.range 29, stT181 (i+1)) + stT181 30 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 29
    simpa using h
  have hprev := st181_p29
  have hstep := st181_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p31 : ((3346377626373/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT181 (i+1))
      = (∑ i ∈ Finset.range 30, stT181 (i+1)) + stT181 31 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 30
    simpa using h
  have hprev := st181_p30
  have hstep := st181_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p32 : ((8718096753319/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT181 (i+1))
      = (∑ i ∈ Finset.range 31, stT181 (i+1)) + stT181 32 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 31
    simpa using h
  have hprev := st181_p31
  have hstep := st181_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p33 : ((8808195402333/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT181 (i+1))
      = (∑ i ∈ Finset.range 32, stT181 (i+1)) + stT181 33 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 32
    simpa using h
  have hprev := st181_p32
  have hstep := st181_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p34 : ((2135381127939/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT181 (i+1))
      = (∑ i ∈ Finset.range 33, stT181 (i+1)) + stT181 34 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 33
    simpa using h
  have hprev := st181_p33
  have hstep := st181_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p35 : ((8122877230181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT181 (i+1))
      = (∑ i ∈ Finset.range 34, stT181 (i+1)) + stT181 35 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 34
    simpa using h
  have hprev := st181_p34
  have hstep := st181_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p36 : ((16039792752503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT181 (i+1))
      = (∑ i ∈ Finset.range 35, stT181 (i+1)) + stT181 36 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 35
    simpa using h
  have hprev := st181_p35
  have hstep := st181_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p37 : ((670499481157/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT181 (i+1))
      = (∑ i ∈ Finset.range 36, stT181 (i+1)) + stT181 37 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 36
    simpa using h
  have hprev := st181_p36
  have hstep := st181_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p38 : ((17227817492611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT181 (i+1))
      = (∑ i ∈ Finset.range 37, stT181 (i+1)) + stT181 38 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 37
    simpa using h
  have hprev := st181_p37
  have hstep := st181_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p39 : ((2070886763981/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT181 (i+1))
      = (∑ i ∈ Finset.range 38, stT181 (i+1)) + stT181 39 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 38
    simpa using h
  have hprev := st181_p38
  have hstep := st181_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p40 : ((6483498223783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT181 (i+1))
      = (∑ i ∈ Finset.range 39, stT181 (i+1)) + stT181 40 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 39
    simpa using h
  have hprev := st181_p39
  have hstep := st181_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p41 : ((33938960292107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT181 (i+1))
      = (∑ i ∈ Finset.range 40, stT181 (i+1)) + stT181 41 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 40
    simpa using h
  have hprev := st181_p40
  have hstep := st181_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p42 : ((33749005091537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT181 (i+1))
      = (∑ i ∈ Finset.range 41, stT181 (i+1)) + stT181 42 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 41
    simpa using h
  have hprev := st181_p41
  have hstep := st181_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p43 : ((6494122780539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT181 (i+1))
      = (∑ i ∈ Finset.range 42, stT181 (i+1)) + stT181 43 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 42
    simpa using h
  have hprev := st181_p42
  have hstep := st181_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p44 : ((33832717884703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT181 (i+1))
      = (∑ i ∈ Finset.range 43, stT181 (i+1)) + stT181 44 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 43
    simpa using h
  have hprev := st181_p43
  have hstep := st181_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p45 : ((1341340146511/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT181 (i+1))
      = (∑ i ∈ Finset.range 44, stT181 (i+1)) + stT181 45 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 44
    simpa using h
  have hprev := st181_p44
  have hstep := st181_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p46 : ((6531874919663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT181 (i+1))
      = (∑ i ∈ Finset.range 45, stT181 (i+1)) + stT181 46 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 45
    simpa using h
  have hprev := st181_p45
  have hstep := st181_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p47 : ((8523251577329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT181 (i+1))
      = (∑ i ∈ Finset.range 46, stT181 (i+1)) + stT181 47 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 46
    simpa using h
  have hprev := st181_p46
  have hstep := st181_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p48 : ((1640762813097/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT181 (i+1))
      = (∑ i ∈ Finset.range 47, stT181 (i+1)) + stT181 48 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 47
    simpa using h
  have hprev := st181_p47
  have hstep := st181_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p49 : ((3349561320069/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT181 (i+1))
      = (∑ i ∈ Finset.range 48, stT181 (i+1)) + stT181 49 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 48
    simpa using h
  have hprev := st181_p48
  have hstep := st181_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p50 : ((134087783387/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT181 (i+1))
      = (∑ i ∈ Finset.range 49, stT181 (i+1)) + stT181 50 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 49
    simpa using h
  have hprev := st181_p49
  have hstep := st181_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p51 : ((32898530943583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT181 (i+1))
      = (∑ i ∈ Finset.range 50, stT181 (i+1)) + stT181 51 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 50
    simpa using h
  have hprev := st181_p50
  have hstep := st181_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p52 : ((33925926869083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT181 (i+1))
      = (∑ i ∈ Finset.range 51, stT181 (i+1)) + stT181 52 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 51
    simpa using h
  have hprev := st181_p51
  have hstep := st181_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p53 : ((32677430277169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT181 (i+1))
      = (∑ i ∈ Finset.range 52, stT181 (i+1)) + stT181 53 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 52
    simpa using h
  have hprev := st181_p52
  have hstep := st181_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p54 : ((34014069938071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT181 (i+1))
      = (∑ i ∈ Finset.range 53, stT181 (i+1)) + stT181 54 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 53
    simpa using h
  have hprev := st181_p53
  have hstep := st181_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p55 : ((32665656454071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT181 (i+1))
      = (∑ i ∈ Finset.range 54, stT181 (i+1)) + stT181 55 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 54
    simpa using h
  have hprev := st181_p54
  have hstep := st181_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p56 : ((33993701410379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT181 (i+1))
      = (∑ i ∈ Finset.range 55, stT181 (i+1)) + stT181 56 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 55
    simpa using h
  have hprev := st181_p55
  have hstep := st181_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p57 : ((32688835076363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT181 (i+1))
      = (∑ i ∈ Finset.range 56, stT181 (i+1)) + stT181 57 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 56
    simpa using h
  have hprev := st181_p56
  have hstep := st181_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p58 : ((33980817833843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT181 (i+1))
      = (∑ i ∈ Finset.range 57, stT181 (i+1)) + stT181 58 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 57
    simpa using h
  have hprev := st181_p57
  have hstep := st181_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p59 : ((32690127993513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT181 (i+1))
      = (∑ i ∈ Finset.range 58, stT181 (i+1)) + stT181 59 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 58
    simpa using h
  have hprev := st181_p58
  have hstep := st181_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p60 : ((33980391290909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT181 (i+1))
      = (∑ i ∈ Finset.range 59, stT181 (i+1)) + stT181 60 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 59
    simpa using h
  have hprev := st181_p59
  have hstep := st181_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p61 : ((8177202365839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT181 (i+1))
      = (∑ i ∈ Finset.range 60, stT181 (i+1)) + stT181 61 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 60
    simpa using h
  have hprev := st181_p60
  have hstep := st181_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p62 : ((8478957143441/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT181 (i+1))
      = (∑ i ∈ Finset.range 61, stT181 (i+1)) + stT181 62 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 61
    simpa using h
  have hprev := st181_p61
  have hstep := st181_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p63 : ((8212350993657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT181 (i+1))
      = (∑ i ∈ Finset.range 62, stT181 (i+1)) + stT181 63 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 62
    simpa using h
  have hprev := st181_p62
  have hstep := st181_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p64 : ((8417930993657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT181 (i+1))
      = (∑ i ∈ Finset.range 63, stT181 (i+1)) + stT181 64 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 63
    simpa using h
  have hprev := st181_p63
  have hstep := st181_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p65 : ((8302120321071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT181 (i+1))
      = (∑ i ∈ Finset.range 64, stT181 (i+1)) + stT181 65 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 64
    simpa using h
  have hprev := st181_p64
  have hstep := st181_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p66 : ((16606996043131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT181 (i+1))
      = (∑ i ∈ Finset.range 65, stT181 (i+1)) + stT181 66 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 65
    simpa using h
  have hprev := st181_p65
  have hstep := st181_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p67 : ((16853367741947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT181 (i+1))
      = (∑ i ∈ Finset.range 66, stT181 (i+1)) + stT181 67 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 66
    simpa using h
  have hprev := st181_p66
  have hstep := st181_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p68 : ((16387842102069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT181 (i+1))
      = (∑ i ∈ Finset.range 67, stT181 (i+1)) + stT181 68 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 67
    simpa using h
  have hprev := st181_p67
  have hstep := st181_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p69 : ((8489089275729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT181 (i+1))
      = (∑ i ∈ Finset.range 68, stT181 (i+1)) + stT181 69 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 68
    simpa using h
  have hprev := st181_p68
  have hstep := st181_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p70 : ((16414928080437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT181 (i+1))
      = (∑ i ∈ Finset.range 69, stT181 (i+1)) + stT181 70 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 69
    simpa using h
  have hprev := st181_p69
  have hstep := st181_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p71 : ((16776696906229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT181 (i+1))
      = (∑ i ∈ Finset.range 70, stT181 (i+1)) + stT181 71 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 70
    simpa using h
  have hprev := st181_p70
  have hstep := st181_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p72 : ((16749790888013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT181 (i+1))
      = (∑ i ∈ Finset.range 71, stT181 (i+1)) + stT181 72 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 71
    simpa using h
  have hprev := st181_p71
  have hstep := st181_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p73 : ((16419629952139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT181 (i+1))
      = (∑ i ∈ Finset.range 72, stT181 (i+1)) + stT181 73 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 72
    simpa using h
  have hprev := st181_p72
  have hstep := st181_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p74 : ((16976161849711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT181 (i+1))
      = (∑ i ∈ Finset.range 73, stT181 (i+1)) + stT181 74 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 73
    simpa using h
  have hprev := st181_p73
  have hstep := st181_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p75 : ((32897720265009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT181 (i+1))
      = (∑ i ∈ Finset.range 74, stT181 (i+1)) + stT181 75 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 74
    simpa using h
  have hprev := st181_p74
  have hstep := st181_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p76 : ((6670350647547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT181 (i+1))
      = (∑ i ∈ Finset.range 75, stT181 (i+1)) + stT181 76 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 75
    simpa using h
  have hprev := st181_p75
  have hstep := st181_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p77 : ((3376223326071/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT181 (i+1))
      = (∑ i ∈ Finset.range 76, stT181 (i+1)) + stT181 77 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 76
    simpa using h
  have hprev := st181_p76
  have hstep := st181_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p78 : ((4089700754121/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT181 (i+1))
      = (∑ i ∈ Finset.range 77, stT181 (i+1)) + stT181 78 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 77
    simpa using h
  have hprev := st181_p77
  have hstep := st181_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p79 : ((33735644380179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT181 (i+1))
      = (∑ i ∈ Finset.range 78, stT181 (i+1)) + stT181 79 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 78
    simpa using h
  have hprev := st181_p78
  have hstep := st181_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p80 : ((33441338700189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT181 (i+1))
      = (∑ i ∈ Finset.range 79, stT181 (i+1)) + stT181 80 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 79
    simpa using h
  have hprev := st181_p79
  have hstep := st181_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p81 : ((32789554845429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT181 (i+1))
      = (∑ i ∈ Finset.range 80, stT181 (i+1)) + stT181 81 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 80
    simpa using h
  have hprev := st181_p80
  have hstep := st181_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p82 : ((16946757680157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT181 (i+1))
      = (∑ i ∈ Finset.range 81, stT181 (i+1)) + stT181 82 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 81
    simpa using h
  have hprev := st181_p81
  have hstep := st181_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p83 : ((1329290798853/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT181 (i+1))
      = (∑ i ∈ Finset.range 82, stT181 (i+1)) + stT181 83 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 82
    simpa using h
  have hprev := st181_p82
  have hstep := st181_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p84 : ((6576260028423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT181 (i+1))
      = (∑ i ∈ Finset.range 83, stT181 (i+1)) + stT181 84 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 83
    simpa using h
  have hprev := st181_p83
  have hstep := st181_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p85 : ((33933822580571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT181 (i+1))
      = (∑ i ∈ Finset.range 84, stT181 (i+1)) + stT181 85 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 84
    simpa using h
  have hprev := st181_p84
  have hstep := st181_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p86 : ((33167790230979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT181 (i+1))
      = (∑ i ∈ Finset.range 85, stT181 (i+1)) + stT181 86 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 85
    simpa using h
  have hprev := st181_p85
  have hstep := st181_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p87 : ((4111632525327/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT181 (i+1))
      = (∑ i ∈ Finset.range 86, stT181 (i+1)) + stT181 87 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 86
    simpa using h
  have hprev := st181_p86
  have hstep := st181_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p88 : ((16964391160699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT181 (i+1))
      = (∑ i ∈ Finset.range 87, stT181 (i+1)) + stT181 88 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 87
    simpa using h
  have hprev := st181_p87
  have hstep := st181_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p89 : ((16617640374947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT181 (i+1))
      = (∑ i ∈ Finset.range 88, stT181 (i+1)) + stT181 89 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 88
    simpa using h
  have hprev := st181_p88
  have hstep := st181_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p90 : ((1312753061007/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT181 (i+1))
      = (∑ i ∈ Finset.range 89, stT181 (i+1)) + stT181 90 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 89
    simpa using h
  have hprev := st181_p89
  have hstep := st181_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p91 : ((33866778219147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT181 (i+1))
      = (∑ i ∈ Finset.range 90, stT181 (i+1)) + stT181 91 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 90
    simpa using h
  have hprev := st181_p90
  have hstep := st181_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p92 : ((16715824454647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT181 (i+1))
      = (∑ i ∈ Finset.range 91, stT181 (i+1)) + stT181 92 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 91
    simpa using h
  have hprev := st181_p91
  have hstep := st181_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p93 : ((16360744092143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT181 (i+1))
      = (∑ i ∈ Finset.range 92, stT181 (i+1)) + stT181 93 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 92
    simpa using h
  have hprev := st181_p92
  have hstep := st181_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p94 : ((16837844378429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT181 (i+1))
      = (∑ i ∈ Finset.range 93, stT181 (i+1)) + stT181 94 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 93
    simpa using h
  have hprev := st181_p93
  have hstep := st181_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p95 : ((3372150277847/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT181 (i+1))
      = (∑ i ∈ Finset.range 94, stT181 (i+1)) + stT181 95 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 94
    simpa using h
  have hprev := st181_p94
  have hstep := st181_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p96 : ((32740519636247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT181 (i+1))
      = (∑ i ∈ Finset.range 95, stT181 (i+1)) + stT181 96 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 95
    simpa using h
  have hprev := st181_p95
  have hstep := st181_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p97 : ((33300854571883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT181 (i+1))
      = (∑ i ∈ Finset.range 96, stT181 (i+1)) + stT181 97 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 96
    simpa using h
  have hprev := st181_p96
  have hstep := st181_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p98 : ((33951952084091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT181 (i+1))
      = (∑ i ∈ Finset.range 97, stT181 (i+1)) + stT181 98 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 97
    simpa using h
  have hprev := st181_p97
  have hstep := st181_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p99 : ((33039920300611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT181 (i+1))
      = (∑ i ∈ Finset.range 98, stT181 (i+1)) + stT181 99 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 98
    simpa using h
  have hprev := st181_p98
  have hstep := st181_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p100 : ((32855521300611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT181 (i+1))
      = (∑ i ∈ Finset.range 99, stT181 (i+1)) + stT181 100 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 99
    simpa using h
  have hprev := st181_p99
  have hstep := st181_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p101 : ((33849509531613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT181 (i+1))
      = (∑ i ∈ Finset.range 100, stT181 (i+1)) + stT181 101 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 100
    simpa using h
  have hprev := st181_p100
  have hstep := st181_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p102 : ((33597509934577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT181 (i+1))
      = (∑ i ∈ Finset.range 101, stT181 (i+1)) + stT181 102 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 101
    simpa using h
  have hprev := st181_p101
  have hstep := st181_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p103 : ((32711230232827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT181 (i+1))
      = (∑ i ∈ Finset.range 102, stT181 (i+1)) + stT181 103 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 102
    simpa using h
  have hprev := st181_p102
  have hstep := st181_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p104 : ((33289163492647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT181 (i+1))
      = (∑ i ∈ Finset.range 103, stT181 (i+1)) + stT181 104 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 103
    simpa using h
  have hprev := st181_p103
  have hstep := st181_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p105 : ((33974863037347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT181 (i+1))
      = (∑ i ∈ Finset.range 104, stT181 (i+1)) + stT181 105 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 104
    simpa using h
  have hprev := st181_p104
  have hstep := st181_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p106 : ((33192463997053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT181 (i+1))
      = (∑ i ∈ Finset.range 105, stT181 (i+1)) + stT181 106 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 105
    simpa using h
  have hprev := st181_p105
  have hstep := st181_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p107 : ((16362115849131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT181 (i+1))
      = (∑ i ∈ Finset.range 106, stT181 (i+1)) + stT181 107 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 106
    simpa using h
  have hprev := st181_p106
  have hstep := st181_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p108 : ((4201652118189/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT181 (i+1))
      = (∑ i ∈ Finset.range 107, stT181 (i+1)) + stT181 108 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 107
    simpa using h
  have hprev := st181_p107
  have hstep := st181_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p109 : ((8472959737663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT181 (i+1))
      = (∑ i ∈ Finset.range 108, stT181 (i+1)) + stT181 109 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 108
    simpa using h
  have hprev := st181_p108
  have hstep := st181_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p110 : ((16479940177577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT181 (i+1))
      = (∑ i ∈ Finset.range 109, stT181 (i+1)) + stT181 110 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 109
    simpa using h
  have hprev := st181_p109
  have hstep := st181_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p111 : ((8205486941359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT181 (i+1))
      = (∑ i ∈ Finset.range 110, stT181 (i+1)) + stT181 111 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 110
    simpa using h
  have hprev := st181_p110
  have hstep := st181_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p112 : ((844067623417/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT181 (i+1))
      = (∑ i ∈ Finset.range 111, stT181 (i+1)) + stT181 112 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 111
    simpa using h
  have hprev := st181_p111
  have hstep := st181_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p113 : ((169072580157/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT181 (i+1))
      = (∑ i ∈ Finset.range 112, stT181 (i+1)) + stT181 113 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 112
    simpa using h
  have hprev := st181_p112
  have hstep := st181_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p114 : ((8219585064017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT181 (i+1))
      = (∑ i ∈ Finset.range 113, stT181 (i+1)) + stT181 114 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 113
    simpa using h
  have hprev := st181_p113
  have hstep := st181_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p115 : ((32858499347183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT181 (i+1))
      = (∑ i ∈ Finset.range 114, stT181 (i+1)) + stT181 115 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 114
    simpa using h
  have hprev := st181_p114
  have hstep := st181_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p116 : ((33786640167347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT181 (i+1))
      = (∑ i ∈ Finset.range 115, stT181 (i+1)) + stT181 116 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 115
    simpa using h
  have hprev := st181_p115
  have hstep := st181_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p117 : ((33825462695847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT181 (i+1))
      = (∑ i ∈ Finset.range 116, stT181 (i+1)) + stT181 117 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 116
    simpa using h
  have hprev := st181_p116
  have hstep := st181_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p118 : ((8226813623543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT181 (i+1))
      = (∑ i ∈ Finset.range 117, stT181 (i+1)) + stT181 118 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 117
    simpa using h
  have hprev := st181_p117
  have hstep := st181_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p119 : ((4100162802969/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT181 (i+1))
      = (∑ i ∈ Finset.range 118, stT181 (i+1)) + stT181 119 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 118
    simpa using h
  have hprev := st181_p118
  have hstep := st181_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p120 : ((4212583656339/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT181 (i+1))
      = (∑ i ∈ Finset.range 119, stT181 (i+1)) + stT181 120 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 119
    simpa using h
  have hprev := st181_p119
  have hstep := st181_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p121 : ((16958639517051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT181 (i+1))
      = (∑ i ∈ Finset.range 120, stT181 (i+1)) + stT181 121 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 120
    simpa using h
  have hprev := st181_p120
  have hstep := st181_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p122 : ((16529162126517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT181 (i+1))
      = (∑ i ∈ Finset.range 121, stT181 (i+1)) + stT181 122 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 121
    simpa using h
  have hprev := st181_p121
  have hstep := st181_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p123 : ((4086846927173/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT181 (i+1))
      = (∑ i ∈ Finset.range 122, stT181 (i+1)) + stT181 123 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 122
    simpa using h
  have hprev := st181_p122
  have hstep := st181_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p124 : ((16736993145701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT181 (i+1))
      = (∑ i ∈ Finset.range 123, stT181 (i+1)) + stT181 124 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 123
    simpa using h
  have hprev := st181_p123
  have hstep := st181_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p125 : ((34006022775947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT181 (i+1))
      = (∑ i ∈ Finset.range 124, stT181 (i+1)) + stT181 125 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 124
    simpa using h
  have hprev := st181_p124
  have hstep := st181_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p126 : ((4170466995679/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT181 (i+1))
      = (∑ i ∈ Finset.range 125, stT181 (i+1)) + stT181 126 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 125
    simpa using h
  have hprev := st181_p125
  have hstep := st181_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p127 : ((32665496926057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT181 (i+1))
      = (∑ i ∈ Finset.range 126, stT181 (i+1)) + stT181 127 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 126
    simpa using h
  have hprev := st181_p126
  have hstep := st181_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p128 : ((33100004970027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT181 (i+1))
      = (∑ i ∈ Finset.range 127, stT181 (i+1)) + stT181 128 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 127
    simpa using h
  have hprev := st181_p127
  have hstep := st181_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p129 : ((33926500994027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT181 (i+1))
      = (∑ i ∈ Finset.range 128, stT181 (i+1)) + stT181 129 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 128
    simpa using h
  have hprev := st181_p128
  have hstep := st181_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p130 : ((8442652912577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT181 (i+1))
      = (∑ i ∈ Finset.range 129, stT181 (i+1)) + stT181 130 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 129
    simpa using h
  have hprev := st181_p129
  have hstep := st181_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p131 : ((32896874323223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT181 (i+1))
      = (∑ i ∈ Finset.range 130, stT181 (i+1)) + stT181 131 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 130
    simpa using h
  have hprev := st181_p130
  have hstep := st181_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p132 : ((16362153324069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT181 (i+1))
      = (∑ i ∈ Finset.range 131, stT181 (i+1)) + stT181 132 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 131
    simpa using h
  have hprev := st181_p131
  have hstep := st181_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p133 : ((16760733849663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT181 (i+1))
      = (∑ i ∈ Finset.range 132, stT181 (i+1)) + stT181 133 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 132
    simpa using h
  have hprev := st181_p132
  have hstep := st181_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p134 : ((17011427047461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT181 (i+1))
      = (∑ i ∈ Finset.range 133, stT181 (i+1)) + stT181 134 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 133
    simpa using h
  have hprev := st181_p133
  have hstep := st181_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p135 : ((1338045693783/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT181 (i+1))
      = (∑ i ∈ Finset.range 134, stT181 (i+1)) + stT181 135 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 134
    simpa using h
  have hprev := st181_p134
  have hstep := st181_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p136 : ((1307803630659/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT181 (i+1))
      = (∑ i ∈ Finset.range 135, stT181 (i+1)) + stT181 136 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 135
    simpa using h
  have hprev := st181_p135
  have hstep := st181_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p137 : ((8225916875989/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT181 (i+1))
      = (∑ i ∈ Finset.range 136, stT181 (i+1)) + stT181 137 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 136
    simpa using h
  have hprev := st181_p136
  have hstep := st181_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p138 : ((8438713850869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT181 (i+1))
      = (∑ i ∈ Finset.range 137, stT181 (i+1)) + stT181 138 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 137
    simpa using h
  have hprev := st181_p137
  have hstep := st181_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p139 : ((8495606485063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT181 (i+1))
      = (∑ i ∈ Finset.range 138, stT181 (i+1)) + stT181 139 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 138
    simpa using h
  have hprev := st181_p138
  have hstep := st181_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p140 : ((1039364360191/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT181 (i+1))
      = (∑ i ∈ Finset.range 139, stT181 (i+1)) + stT181 140 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 139
    simpa using h
  have hprev := st181_p139
  have hstep := st181_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p141 : ((2039973411687/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT181 (i+1))
      = (∑ i ∈ Finset.range 140, stT181 (i+1)) + stT181 141 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 140
    simpa using h
  have hprev := st181_p140
  have hstep := st181_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p142 : ((1650289155261/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT181 (i+1))
      = (∑ i ∈ Finset.range 141, stT181 (i+1)) + stT181 142 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 141
    simpa using h
  have hprev := st181_p141
  have hstep := st181_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p143 : ((16916232175217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT181 (i+1))
      = (∑ i ∈ Finset.range 142, stT181 (i+1)) + stT181 143 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 142
    simpa using h
  have hprev := st181_p142
  have hstep := st181_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p144 : ((849097899113/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT181 (i+1))
      = (∑ i ∈ Finset.range 143, stT181 (i+1)) + stT181 144 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 143
    simpa using h
  have hprev := st181_p143
  have hstep := st181_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p145 : ((830649507379/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT181 (i+1))
      = (∑ i ∈ Finset.range 144, stT181 (i+1)) + stT181 145 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 144
    simpa using h
  have hprev := st181_p144
  have hstep := st181_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p146 : ((16315135161983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT181 (i+1))
      = (∑ i ∈ Finset.range 145, stT181 (i+1)) + stT181 146 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 145
    simpa using h
  have hprev := st181_p145
  have hstep := st181_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p147 : ((16487795863223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT181 (i+1))
      = (∑ i ∈ Finset.range 146, stT181 (i+1)) + stT181 147 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 146
    simpa using h
  have hprev := st181_p146
  have hstep := st181_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p148 : ((8448584096041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT181 (i+1))
      = (∑ i ∈ Finset.range 147, stT181 (i+1)) + stT181 148 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 147
    simpa using h
  have hprev := st181_p147
  have hstep := st181_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p149 : ((17003855825981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT181 (i+1))
      = (∑ i ∈ Finset.range 148, stT181 (i+1)) + stT181 149 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 148
    simpa using h
  have hprev := st181_p148
  have hstep := st181_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p150 : ((16672439693681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT181 (i+1))
      = (∑ i ∈ Finset.range 149, stT181 (i+1)) + stT181 150 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 149
    simpa using h
  have hprev := st181_p149
  have hstep := st181_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p151 : ((2041481081557/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT181 (i+1))
      = (∑ i ∈ Finset.range 150, stT181 (i+1)) + stT181 151 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 150
    simpa using h
  have hprev := st181_p150
  have hstep := st181_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p152 : ((262617141323/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT181 (i+1))
      = (∑ i ∈ Finset.range 151, stT181 (i+1)) + stT181 152 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 151
    simpa using h
  have hprev := st181_p151
  have hstep := st181_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p153 : ((33622353838519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT181 (i+1))
      = (∑ i ∈ Finset.range 152, stT181 (i+1)) + stT181 153 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 152
    simpa using h
  have hprev := st181_p152
  have hstep := st181_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p154 : ((6811783676541/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT181 (i+1))
      = (∑ i ∈ Finset.range 153, stT181 (i+1)) + stT181 154 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 153
    simpa using h
  have hprev := st181_p153
  have hstep := st181_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p155 : ((6721211304189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT181 (i+1))
      = (∑ i ∈ Finset.range 154, stT181 (i+1)) + stT181 155 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 154
    simpa using h
  have hprev := st181_p154
  have hstep := st181_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p156 : ((16410053241327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT181 (i+1))
      = (∑ i ∈ Finset.range 155, stT181 (i+1)) + stT181 156 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 155
    simpa using h
  have hprev := st181_p155
  have hstep := st181_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p157 : ((32644252002639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT181 (i+1))
      = (∑ i ∈ Finset.range 156, stT181 (i+1)) + stT181 157 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 156
    simpa using h
  have hprev := st181_p156
  have hstep := st181_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p158 : ((33280559175721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT181 (i+1))
      = (∑ i ∈ Finset.range 157, stT181 (i+1)) + stT181 158 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 157
    simpa using h
  have hprev := st181_p157
  have hstep := st181_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p159 : ((16988574501719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT181 (i+1))
      = (∑ i ∈ Finset.range 158, stT181 (i+1)) + stT181 159 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 158
    simpa using h
  have hprev := st181_p158
  have hstep := st181_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p160 : ((8481980250027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT181 (i+1))
      = (∑ i ∈ Finset.range 159, stT181 (i+1)) + stT181 160 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 159
    simpa using h
  have hprev := st181_p159
  have hstep := st181_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p161 : ((33196230078487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT181 (i+1))
      = (∑ i ∈ Finset.range 160, stT181 (i+1)) + stT181 161 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 160
    simpa using h
  have hprev := st181_p160
  have hstep := st181_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p162 : ((16307979796731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT181 (i+1))
      = (∑ i ∈ Finset.range 161, stT181 (i+1)) + stT181 162 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 161
    simpa using h
  have hprev := st181_p161
  have hstep := st181_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p163 : ((16417315843391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT181 (i+1))
      = (∑ i ∈ Finset.range 162, stT181 (i+1)) + stT181 163 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 162
    simpa using h
  have hprev := st181_p162
  have hstep := st181_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p164 : ((3360273718019/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT181 (i+1))
      = (∑ i ∈ Finset.range 163, stT181 (i+1)) + stT181 164 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 163
    simpa using h
  have hprev := st181_p163
  have hstep := st181_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p165 : ((42593274813/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT181 (i+1))
      = (∑ i ∈ Finset.range 164, stT181 (i+1)) + stT181 165 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 164
    simpa using h
  have hprev := st181_p164
  have hstep := st181_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p166 : ((134969243199/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT181 (i+1))
      = (∑ i ∈ Finset.range 165, stT181 (i+1)) + stT181 166 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 165
    simpa using h
  have hprev := st181_p165
  have hstep := st181_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p167 : ((16484554090211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT181 (i+1))
      = (∑ i ∈ Finset.range 166, stT181 (i+1)) + stT181 167 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 166
    simpa using h
  have hprev := st181_p166
  have hstep := st181_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p168 : ((32578036242843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT181 (i+1))
      = (∑ i ∈ Finset.range 167, stT181 (i+1)) + stT181 168 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 167
    simpa using h
  have hprev := st181_p167
  have hstep := st181_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p169 : ((32975258153313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT181 (i+1))
      = (∑ i ∈ Finset.range 168, stT181 (i+1)) + stT181 169 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 168
    simpa using h
  have hprev := st181_p168
  have hstep := st181_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p170 : ((33741578670517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT181 (i+1))
      = (∑ i ∈ Finset.range 169, stT181 (i+1)) + stT181 170 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 169
    simpa using h
  have hprev := st181_p169
  have hstep := st181_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p171 : ((8521878459957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT181 (i+1))
      = (∑ i ∈ Finset.range 170, stT181 (i+1)) + stT181 171 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 170
    simpa using h
  have hprev := st181_p170
  have hstep := st181_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p172 : ((33665845298419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT181 (i+1))
      = (∑ i ∈ Finset.range 171, stT181 (i+1)) + stT181 172 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 171
    simpa using h
  have hprev := st181_p171
  have hstep := st181_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p173 : ((32907097356997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT181 (i+1))
      = (∑ i ∈ Finset.range 172, stT181 (i+1)) + stT181 173 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 172
    simpa using h
  have hprev := st181_p172
  have hstep := st181_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p174 : ((16284175337067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT181 (i+1))
      = (∑ i ∈ Finset.range 173, stT181 (i+1)) + stT181 174 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 173
    simpa using h
  have hprev := st181_p173
  have hstep := st181_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p175 : ((3297883242891/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT181 (i+1))
      = (∑ i ∈ Finset.range 174, stT181 (i+1)) + stT181 175 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 174
    simpa using h
  have hprev := st181_p174
  have hstep := st181_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p176 : ((8433030306747/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT181 (i+1))
      = (∑ i ∈ Finset.range 175, stT181 (i+1)) + stT181 176 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 175
    simpa using h
  have hprev := st181_p175
  have hstep := st181_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p177 : ((17049726441063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT181 (i+1))
      = (∑ i ∈ Finset.range 176, stT181 (i+1)) + stT181 177 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 176
    simpa using h
  have hprev := st181_p176
  have hstep := st181_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p178 : ((16867063618833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT181 (i+1))
      = (∑ i ∈ Finset.range 177, stT181 (i+1)) + stT181 178 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 177
    simpa using h
  have hprev := st181_p177
  have hstep := st181_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p179 : ((16493752224017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT181 (i+1))
      = (∑ i ∈ Finset.range 178, stT181 (i+1)) + stT181 179 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 178
    simpa using h
  have hprev := st181_p178
  have hstep := st181_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p180 : ((3256037521081/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT181 (i+1))
      = (∑ i ∈ Finset.range 179, stT181 (i+1)) + stT181 180 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 179
    simpa using h
  have hprev := st181_p179
  have hstep := st181_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p181 : ((3284472233051/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT181 (i+1))
      = (∑ i ∈ Finset.range 180, stT181 (i+1)) + stT181 181 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 180
    simpa using h
  have hprev := st181_p180
  have hstep := st181_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p182 : ((33573831895637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT181 (i+1))
      = (∑ i ∈ Finset.range 181, stT181 (i+1)) + stT181 182 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 181
    simpa using h
  have hprev := st181_p181
  have hstep := st181_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p183 : ((34083036889277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT181 (i+1))
      = (∑ i ∈ Finset.range 182, stT181 (i+1)) + stT181 183 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 182
    simpa using h
  have hprev := st181_p182
  have hstep := st181_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p184 : ((33917502281457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT181 (i+1))
      = (∑ i ∈ Finset.range 183, stT181 (i+1)) + stT181 184 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 183
    simpa using h
  have hprev := st181_p183
  have hstep := st181_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p185 : ((33230248296767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT181 (i+1))
      = (∑ i ∈ Finset.range 184, stT181 (i+1)) + stT181 185 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 184
    simpa using h
  have hprev := st181_p184
  have hstep := st181_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p186 : ((1305209005871/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT181 (i+1))
      = (∑ i ∈ Finset.range 185, stT181 (i+1)) + stT181 186 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 185
    simpa using h
  have hprev := st181_p185
  have hstep := st181_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p187 : ((32639053793631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT181 (i+1))
      = (∑ i ∈ Finset.range 186, stT181 (i+1)) + stT181 187 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 186
    simpa using h
  have hprev := st181_p186
  have hstep := st181_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p188 : ((33243681622731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT181 (i+1))
      = (∑ i ∈ Finset.range 187, stT181 (i+1)) + stT181 188 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 187
    simpa using h
  have hprev := st181_p187
  have hstep := st181_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p189 : ((6784526154063/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT181 (i+1))
      = (∑ i ∈ Finset.range 188, stT181 (i+1)) + stT181 189 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 188
    simpa using h
  have hprev := st181_p188
  have hstep := st181_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p190 : ((34101223373663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT181 (i+1))
      = (∑ i ∈ Finset.range 189, stT181 (i+1)) + stT181 190 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 189
    simpa using h
  have hprev := st181_p189
  have hstep := st181_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p191 : ((16817147680569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT181 (i+1))
      = (∑ i ∈ Finset.range 190, stT181 (i+1)) + stT181 191 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 190
    simpa using h
  have hprev := st181_p190
  have hstep := st181_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p192 : ((16457319817273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT181 (i+1))
      = (∑ i ∈ Finset.range 191, stT181 (i+1)) + stT181 192 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 191
    simpa using h
  have hprev := st181_p191
  have hstep := st181_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p193 : ((16267708765817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT181 (i+1))
      = (∑ i ∈ Finset.range 192, stT181 (i+1)) + stT181 193 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 192
    simpa using h
  have hprev := st181_p192
  have hstep := st181_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p194 : ((16401042899871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT181 (i+1))
      = (∑ i ∈ Finset.range 193, stT181 (i+1)) + stT181 194 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 193
    simpa using h
  have hprev := st181_p193
  have hstep := st181_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p195 : ((1046692741563/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT181 (i+1))
      = (∑ i ∈ Finset.range 194, stT181 (i+1)) + stT181 195 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 194
    simpa using h
  have hprev := st181_p194
  have hstep := st181_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p196 : ((8513918220699/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT181 (i+1))
      = (∑ i ∈ Finset.range 195, stT181 (i+1)) + stT181 196 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 195
    simpa using h
  have hprev := st181_p195
  have hstep := st181_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p197 : ((8510960041107/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT181 (i+1))
      = (∑ i ∈ Finset.range 196, stT181 (i+1)) + stT181 197 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 196
    simpa using h
  have hprev := st181_p196
  have hstep := st181_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p198 : ((16736419425099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT181 (i+1))
      = (∑ i ∈ Finset.range 197, stT181 (i+1)) + stT181 198 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 197
    simpa using h
  have hprev := st181_p197
  have hstep := st181_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p199 : ((16395188441169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT181 (i+1))
      = (∑ i ∈ Finset.range 198, stT181 (i+1)) + stT181 199 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 198
    simpa using h
  have hprev := st181_p198
  have hstep := st181_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p200 : ((2032615812443/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT181 (i+1))
      = (∑ i ∈ Finset.range 199, stT181 (i+1)) + stT181 200 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 199
    simpa using h
  have hprev := st181_p199
  have hstep := st181_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p201 : ((16434085170319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT181 (i+1))
      = (∑ i ∈ Finset.range 200, stT181 (i+1)) + stT181 201 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 200
    simpa using h
  have hprev := st181_p200
  have hstep := st181_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p202 : ((8390706859289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT181 (i+1))
      = (∑ i ∈ Finset.range 201, stT181 (i+1)) + stT181 202 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 201
    simpa using h
  have hprev := st181_p201
  have hstep := st181_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p203 : ((4260457271437/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT181 (i+1))
      = (∑ i ∈ Finset.range 202, stT181 (i+1)) + stT181 203 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 202
    simpa using h
  have hprev := st181_p202
  have hstep := st181_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p204 : ((1361855558637/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT181 (i+1))
      = (∑ i ∈ Finset.range 203, stT181 (i+1)) + stT181 204 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 203
    simpa using h
  have hprev := st181_p203
  have hstep := st181_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p205 : ((33483033124463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT181 (i+1))
      = (∑ i ∈ Finset.range 204, stT181 (i+1)) + stT181 205 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 204
    simpa using h
  have hprev := st181_p204
  have hstep := st181_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p206 : ((32807628939139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT181 (i+1))
      = (∑ i ∈ Finset.range 205, stT181 (i+1)) + stT181 206 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 205
    simpa using h
  have hprev := st181_p205
  have hstep := st181_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p207 : ((32507775069853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT181 (i+1))
      = (∑ i ∈ Finset.range 206, stT181 (i+1)) + stT181 207 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 206
    simpa using h
  have hprev := st181_p206
  have hstep := st181_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p208 : ((4099305937091/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT181 (i+1))
      = (∑ i ∈ Finset.range 207, stT181 (i+1)) + stT181 208 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 207
    simpa using h
  have hprev := st181_p207
  have hstep := st181_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p209 : ((16729936453079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT181 (i+1))
      = (∑ i ∈ Finset.range 208, stT181 (i+1)) + stT181 209 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 208
    simpa using h
  have hprev := st181_p208
  have hstep := st181_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p210 : ((34034171911693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT181 (i+1))
      = (∑ i ∈ Finset.range 209, stT181 (i+1)) + stT181 210 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 209
    simpa using h
  have hprev := st181_p209
  have hstep := st181_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p211 : ((34118850620977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT181 (i+1))
      = (∑ i ∈ Finset.range 210, stT181 (i+1)) + stT181 211 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 210
    simpa using h
  have hprev := st181_p210
  have hstep := st181_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p212 : ((16829785516007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT181 (i+1))
      = (∑ i ∈ Finset.range 211, stT181 (i+1)) + stT181 212 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 211
    simpa using h
  have hprev := st181_p211
  have hstep := st181_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p213 : ((16487204719787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT181 (i+1))
      = (∑ i ∈ Finset.range 212, stT181 (i+1)) + stT181 213 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 212
    simpa using h
  have hprev := st181_p212
  have hstep := st181_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p214 : ((3252898890349/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT181 (i+1))
      = (∑ i ∈ Finset.range 213, stT181 (i+1)) + stT181 214 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 213
    simpa using h
  have hprev := st181_p213
  have hstep := st181_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p215 : ((4077525785373/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT181 (i+1))
      = (∑ i ∈ Finset.range 214, stT181 (i+1)) + stT181 215 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 214
    simpa using h
  have hprev := st181_p214
  have hstep := st181_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p216 : ((8295753494603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT181 (i+1))
      = (∑ i ∈ Finset.range 215, stT181 (i+1)) + stT181 216 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 215
    simpa using h
  have hprev := st181_p215
  have hstep := st181_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p217 : ((8460618227287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT181 (i+1))
      = (∑ i ∈ Finset.range 216, stT181 (i+1)) + stT181 217 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 216
    simpa using h
  have hprev := st181_p216
  have hstep := st181_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p218 : ((8541678405227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT181 (i+1))
      = (∑ i ∈ Finset.range 217, stT181 (i+1)) + stT181 218 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 217
    simpa using h
  have hprev := st181_p217
  have hstep := st181_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p219 : ((8487069990233/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT181 (i+1))
      = (∑ i ∈ Finset.range 218, stT181 (i+1)) + stT181 219 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 218
    simpa using h
  have hprev := st181_p218
  have hstep := st181_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p220 : ((8332960848583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT181 (i+1))
      = (∑ i ∈ Finset.range 219, stT181 (i+1)) + stT181 220 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 219
    simpa using h
  have hprev := st181_p219
  have hstep := st181_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p221 : ((16356616561671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT181 (i+1))
      = (∑ i ∈ Finset.range 220, stT181 (i+1)) + stT181 221 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 220
    simpa using h
  have hprev := st181_p220
  have hstep := st181_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p222 : ((16241572197987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT181 (i+1))
      = (∑ i ∈ Finset.range 221, stT181 (i+1)) + stT181 222 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 221
    simpa using h
  have hprev := st181_p221
  have hstep := st181_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p223 : ((32782569240887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT181 (i+1))
      = (∑ i ∈ Finset.range 222, stT181 (i+1)) + stT181 223 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 222
    simpa using h
  have hprev := st181_p222
  have hstep := st181_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p224 : ((33421371615903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT181 (i+1))
      = (∑ i ∈ Finset.range 223, stT181 (i+1)) + stT181 224 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 223
    simpa using h
  have hprev := st181_p223
  have hstep := st181_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p225 : ((34003519700421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT181 (i+1))
      = (∑ i ∈ Finset.range 224, stT181 (i+1)) + stT181 225 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 224
    simpa using h
  have hprev := st181_p224
  have hstep := st181_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p226 : ((34173996589191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT181 (i+1))
      = (∑ i ∈ Finset.range 225, stT181 (i+1)) + stT181 226 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 225
    simpa using h
  have hprev := st181_p225
  have hstep := st181_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p227 : ((33832777408239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT181 (i+1))
      = (∑ i ∈ Finset.range 226, stT181 (i+1)) + stT181 227 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 226
    simpa using h
  have hprev := st181_p226
  have hstep := st181_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p228 : ((33188725399807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT181 (i+1))
      = (∑ i ∈ Finset.range 227, stT181 (i+1)) + stT181 228 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 227
    simpa using h
  have hprev := st181_p227
  have hstep := st181_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p229 : ((3262770130273/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT181 (i+1))
      = (∑ i ∈ Finset.range 228, stT181 (i+1)) + stT181 229 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 228
    simpa using h
  have hprev := st181_p228
  have hstep := st181_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p230 : ((32480368552709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT181 (i+1))
      = (∑ i ∈ Finset.range 229, stT181 (i+1)) + stT181 230 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 229
    simpa using h
  have hprev := st181_p229
  have hstep := st181_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p231 : ((820745174669/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT181 (i+1))
      = (∑ i ∈ Finset.range 230, stT181 (i+1)) + stT181 231 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 230
    simpa using h
  have hprev := st181_p230
  have hstep := st181_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p232 : ((522955750763/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT181 (i+1))
      = (∑ i ∈ Finset.range 231, stT181 (i+1)) + stT181 232 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 231
    simpa using h
  have hprev := st181_p231
  have hstep := st181_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p233 : ((34027810034283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT181 (i+1))
      = (∑ i ∈ Finset.range 232, stT181 (i+1)) + stT181 233 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 232
    simpa using h
  have hprev := st181_p232
  have hstep := st181_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p234 : ((34187050342803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT181 (i+1))
      = (∑ i ∈ Finset.range 233, stT181 (i+1)) + stT181 234 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 233
    simpa using h
  have hprev := st181_p233
  have hstep := st181_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p235 : ((6771929022609/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT181 (i+1))
      = (∑ i ∈ Finset.range 234, stT181 (i+1)) + stT181 235 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 234
    simpa using h
  have hprev := st181_p234
  have hstep := st181_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p236 : ((1661669425203/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT181 (i+1))
      = (∑ i ∈ Finset.range 235, stT181 (i+1)) + stT181 236 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 235
    simpa using h
  have hprev := st181_p235
  have hstep := st181_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p237 : ((204124164139/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT181 (i+1))
      = (∑ i ∈ Finset.range 236, stT181 (i+1)) + stT181 237 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 236
    simpa using h
  have hprev := st181_p236
  have hstep := st181_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p238 : ((2028501353821/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT181 (i+1))
      = (∑ i ∈ Finset.range 237, stT181 (i+1)) + stT181 238 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 237
    simpa using h
  have hprev := st181_p237
  have hstep := st181_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p239 : ((8182739594667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT181 (i+1))
      = (∑ i ∈ Finset.range 238, stT181 (i+1)) + stT181 239 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 238
    simpa using h
  have hprev := st181_p238
  have hstep := st181_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p240 : ((1666566627819/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT181 (i+1))
      = (∑ i ∈ Finset.range 239, stT181 (i+1)) + stT181 240 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 239
    simpa using h
  have hprev := st181_p239
  have hstep := st181_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p241 : ((8482577829869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT181 (i+1))
      = (∑ i ∈ Finset.range 240, stT181 (i+1)) + stT181 241 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 240
    simpa using h
  have hprev := st181_p240
  have hstep := st181_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p242 : ((1710340653177/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT181 (i+1))
      = (∑ i ∈ Finset.range 241, stT181 (i+1)) + stT181 242 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 241
    simpa using h
  have hprev := st181_p241
  have hstep := st181_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p243 : ((6803233717771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT181 (i+1))
      = (∑ i ∈ Finset.range 242, stT181 (i+1)) + stT181 243 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 242
    simpa using h
  have hprev := st181_p242
  have hstep := st181_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p244 : ((3346241816663/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT181 (i+1))
      = (∑ i ∈ Finset.range 243, stT181 (i+1)) + stT181 244 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 243
    simpa using h
  have hprev := st181_p243
  have hstep := st181_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p245 : ((16419075502933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT181 (i+1))
      = (∑ i ∈ Finset.range 244, stT181 (i+1)) + stT181 245 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 244
    simpa using h
  have hprev := st181_p244
  have hstep := st181_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p246 : ((1014630517161/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT181 (i+1))
      = (∑ i ∈ Finset.range 245, stT181 (i+1)) + stT181 246 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 245
    simpa using h
  have hprev := st181_p245
  have hstep := st181_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p247 : ((813533125759/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT181 (i+1))
      = (∑ i ∈ Finset.range 246, stT181 (i+1)) + stT181 247 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 246
    simpa using h
  have hprev := st181_p246
  have hstep := st181_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p248 : ((825422992759/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT181 (i+1))
      = (∑ i ∈ Finset.range 247, stT181 (i+1)) + stT181 248 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 247
    simpa using h
  have hprev := st181_p247
  have hstep := st181_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p249 : ((8412651580161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT181 (i+1))
      = (∑ i ∈ Finset.range 248, stT181 (i+1)) + stT181 249 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 248
    simpa using h
  have hprev := st181_p248
  have hstep := st181_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_p250 : ((8530507039591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT181 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT181 (i+1))
      = (∑ i ∈ Finset.range 249, stT181 (i+1)) + stT181 250 := by
    have h := Finset.sum_range_succ (fun i => stT181 (i+1)) 249
    simpa using h
  have hprev := st181_p249
  have hstep := st181_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st181_s250 :
    |Real.sin (((181 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))
      - ((33329/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 456007/2500000) (δ := 9143/1000000000) (ψ := -371643/1000000) 181 159
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 181`** (evaluated boundary). -/
theorem station_181_sign : 0 < hardyG ((((181:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 181 250 (by norm_num) (by norm_num)
    ((-371643/1000000 : ℚ) : ℝ)
  have hchain := st181_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT181 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((181 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-371643/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st181_c250
  have hsinb := abs_le.mp st181_s250
  have hbdy_lo : ((-2392121964001/40951562500000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((181 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ))) / 2
          - ((((181:ℕ)):ℝ))
            * Real.sin (((181 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-371643/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((181:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((181:ℝ) * Real.log (250:ℝ) - ((-371643/1000000 : ℚ) : ℝ))) / 2
        - ((181:ℝ)) * Real.sin ((181:ℝ) * Real.log (250:ℝ) - ((-371643/1000000 : ℚ) : ℝ))
        ≥ ((-30258193/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((181:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-30258193/250000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-30258193/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-30258193/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((181:ℕ)):ℝ))+1) * (((((181:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((230621364721/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8530507039591/2500000000000 : ℚ) : ℝ) + ((-2392121964001/40951562500000 : ℚ) : ℝ)
      - ((230621364721/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-371643/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((181:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-371643/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((181:ℕ)):ℝ)))).re
      - Real.sin ((-371643/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((181:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((181:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((181:ℕ)):ℝ))
      = (((((181:ℕ)):ℝ)) * (Real.log ((((181:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((181:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_181
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
  have hθwin : |(((-371643/1000000 : ℚ) : ℝ) + ((34:ℤ)) * (2*Real.pi)) - theta ((((181:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((181:ℕ)):ℝ)))
    (φ := ((-371643/1000000 : ℚ) : ℝ) + ((34:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-371643/1000000 : ℚ)) : ℝ) 34).1,
    (cos_sin_shift (((-371643/1000000 : ℚ)) : ℝ) 34).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_181_sign
end AxiomAudit
