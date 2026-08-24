import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 269` (rung-280.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT269 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((269 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-18323/62500 : ℚ) : ℝ))

theorem st269_c1 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((957333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18323/250000) (δ := 1/1000000000) (ψ := -18323/62500) 269 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t1 : ((957283/1000000 : ℚ) : ℝ) ≤ stT269 1 := by
  have hc : ((957283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((957283/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((957283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c2 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-4353/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -109113/250000) (δ := 6793/500000000) (ψ := -18323/62500) 269 30
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t2 : ((-30789197839/250000000000 : ℚ) : ℝ) ≤ stT269 2 := by
  have hc : ((-17417/100000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30789197839/250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-17417/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c3 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((872669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255077/2000000) (δ := 13639/1000000000) (ψ := -18323/62500) 269 47
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t3 : ((2519033770869/5000000000000 : ℚ) : ℝ) ≤ stT269 3 := by
  have hc : ((872619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2519033770869/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((872619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c4 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-400097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3123019/5000000) (δ := 109/8000000) (ψ := -18323/62500) 269 59
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t4 : ((-1000305200061/2500000000000 : ℚ) : ℝ) ≤ stT269 4 := by
  have hc : ((-200061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1000305200061/2500000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-200061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c5 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((952999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192381/2500000) (δ := 13497/1000000000) (ψ := -18323/62500) 269 69
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t5 : ((852343315223/2000000000000 : ℚ) : ℝ) ≤ stT269 5 := by
  have hc : ((952949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((852343315223/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((952949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c6 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((1679/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1911011/5000000) (δ := 13649/1000000000) (ψ := -18323/62500) 269 77
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t6 : ((3423161157/200000000000 : ℚ) : ℝ) ≤ stT269 6 := by
  have hc : ((1677/40000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3423161157/200000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((1677/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c7 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-619277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1119309/2000000) (δ := 13597/1000000000) (ψ := -18323/62500) 269 83
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t7 : ((-468167239783/2000000000000 : ℚ) : ℝ) ≤ stT269 7 := by
  have hc : ((-619327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468167239783/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-619327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c8 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((179259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143579/1250000) (δ := 341/25000000) (ψ := -18323/62500) 269 89
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t8 : ((633740754717/2000000000000 : ℚ) : ℝ) ≤ stT269 8 := by
  have hc : ((179249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633740754717/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((179249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c9 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((74707/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1817883/10000000) (δ := 1697/125000000) (ψ := -18323/62500) 269 94
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t9 : ((124503320883/500000000000 : ℚ) : ℝ) ≤ stT269 9 := by
  have hc : ((37351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124503320883/500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((37351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c10 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-43777/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5866997/10000000) (δ := 3403/250000000) (ψ := -18323/62500) 269 99
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t10 : ((-553779704499/2500000000000 : ℚ) : ℝ) ≤ stT269 10 := by
  have hc : ((-350241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553779704499/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-350241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c11 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-267021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4602741/10000000) (δ := 6731/500000000) (ψ := -18323/62500) 269 103
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t11 : ((-402624755547/5000000000000 : ℚ) : ℝ) ≤ stT269 11 := by
  have hc : ((-267071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402624755547/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-267071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c12 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-113819/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 848567/1250000) (δ := 13563/1000000000) (ψ := -18323/62500) 269 106
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t12 : ((-41073158511/156250000000 : ℚ) : ℝ) ≤ stT269 12 := by
  have hc : ((-455301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41073158511/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-455301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c13 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((632639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1107301/5000000) (δ := 3403/250000000) (ψ := -18323/62500) 269 110
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t13 : ((3508971183/20000000000 : ℚ) : ℝ) ≤ stT269 13 := by
  have hc : ((632589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3508971183/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((632589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c14 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((196027/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 499139/10000000) (δ := 13613/1000000000) (ψ := -18323/62500) 269 113
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t14 : ((130969346601/500000000000 : ℚ) : ℝ) ≤ stT269 14 := by
  have hc : ((196017/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130969346601/500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((196017/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c15 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((24897/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113513/5000000) (δ := 13469/1000000000) (ψ := -18323/62500) 269 116
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t15 : ((64280527751/250000000000 : ℚ) : ℝ) ≤ stT269 15 := by
  have hc : ((99583/100000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64280527751/250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((99583/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c16 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-4357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157951/400000) (δ := 13647/1000000000) (ψ := -18323/62500) 269 119
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t16 : ((-5477502191/2500000000000 : ℚ) : ℝ) ≤ stT269 16 := by
  have hc : ((-2191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5477502191/2500000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-2191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c17 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-278737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2702671/5000000) (δ := 13633/1000000000) (ψ := -18323/62500) 269 121
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t17 : ((-338048684017/2500000000000 : ℚ) : ℝ) ≤ stT269 17 := by
  have hc : ((-139381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338048684017/2500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-139381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c18 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((128051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3279523/10000000) (δ := 1699/125000000) (ψ := -18323/62500) 269 124
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t18 : ((75440024643/1250000000000 : ℚ) : ℝ) ≤ stT269 18 := by
  have hc : ((64013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75440024643/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((64013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c19 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((786363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 832371/5000000) (δ := 13497/1000000000) (ψ := -18323/62500) 269 126
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t19 : ((1803925473141/10000000000000 : ℚ) : ℝ) ≤ stT269 19 := by
  have hc : ((786313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1803925473141/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((786313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c20 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-320851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 118589/250000) (δ := 169/12500000) (ψ := -18323/62500) 269 128
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t20 : ((-179389114317/2500000000000 : ℚ) : ℝ) ≤ stT269 20 := by
  have hc : ((-320901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179389114317/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-320901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c21 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-386901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6139043/10000000) (δ := 2707/200000000) (ψ := -18323/62500) 269 130
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t21 : ((-422170895877/2500000000000 : ℚ) : ℝ) ≤ stT269 21 := by
  have hc : ((-193463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422170895877/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-193463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c22 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-369751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 750977/1250000) (δ := 6777/500000000) (ψ := -18323/62500) 269 132
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t22 : ((-6159104611/39062500000 : ℚ) : ℝ) ≤ stT269 22 := by
  have hc : ((-23111/31250 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6159104611/39062500000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-23111/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c23 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-110819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179429/400000) (δ := 13539/1000000000) (ψ := -18323/62500) 269 134
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t23 : ((-11556290619/250000000000 : ℚ) : ℝ) ≤ stT269 23 := by
  have hc : ((-27711/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11556290619/250000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-27711/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c24 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((779799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169113/1000000) (δ := 6789/500000000) (ψ := -18323/62500) 269 136
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t24 : ((1591655628509/10000000000000 : ℚ) : ℝ) ≤ stT269 24 := by
  have hc : ((779749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1591655628509/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((779749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c25 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((153673/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1136001/5000000) (δ := 13511/1000000000) (ψ := -18323/62500) 269 138
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t25 : ((307321/2500000 : ℚ) : ℝ) ≤ stT269 25 := by
  have hc : ((307321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307321/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((307321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c26 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-976593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -914001/1250000) (δ := 3399/250000000) (ψ := -18323/62500) 269 140
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t26 : ((-957677569583/5000000000000 : ℚ) : ℝ) ≤ stT269 26 := by
  have hc : ((-976643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-957677569583/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-976643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c27 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((58643/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2360381/10000000) (δ := 6757/500000000) (ψ := -18323/62500) 269 141
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t27 : ((112848831/1000000000 : ℚ) : ℝ) ≤ stT269 27 := by
  have hc : ((29319/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112848831/1000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((29319/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c28 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-16581/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4598267/10000000) (δ := 3407/250000000) (ψ := -18323/62500) 269 143
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t28 : ((-250728486879/5000000000000 : ℚ) : ℝ) ≤ stT269 28 := by
  have hc : ((-132673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250728486879/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-132673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c29 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((50203/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3292669/10000000) (δ := 2727/200000000) (ψ := -18323/62500) 269 144
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t29 : ((93206041929/2000000000000 : ℚ) : ℝ) ≤ stT269 29 := by
  have hc : ((50193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93206041929/2000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((50193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c30 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-530341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5324499/10000000) (δ := 271/20000000) (ψ := -18323/62500) 269 146
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t30 : ((-484178562561/5000000000000 : ℚ) : ℝ) ≤ stT269 30 := by
  have hc : ((-530391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484178562561/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-530391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c31 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((183623/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 203749/2000000) (δ := 6773/500000000) (ψ := -18323/62500) 269 147
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t31 : ((329778679489/2000000000000 : ℚ) : ℝ) ≤ stT269 31 := by
  have hc : ((183613/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329778679489/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((183613/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c32 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-55527/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6661783/10000000) (δ := 3391/250000000) (ψ := -18323/62500) 269 148
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t32 : ((-785314579847/5000000000000 : ℚ) : ℝ) ≤ stT269 32 := by
  have hc : ((-444241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-785314579847/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-444241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c33 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-13319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4060243/10000000) (δ := 541/40000000) (ψ := -18323/62500) 269 150
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t33 : ((-46414337151/5000000000000 : ℚ) : ℝ) ≤ stT269 33 := by
  have hc : ((-26663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46414337151/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-26663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c34 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((124053/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9623/312500) (δ := 13617/1000000000) (ψ := -18323/62500) 269 151
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t34 : ((170190652439/1000000000000 : ℚ) : ℝ) ≤ stT269 34 := by
  have hc : ((496187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170190652439/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((496187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c35 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-66781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4094067/10000000) (δ := 13493/1000000000) (ψ := -18323/62500) 269 152
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t35 : ((-112965040779/10000000000000 : ℚ) : ℝ) ≤ stT269 35 := by
  have hc : ((-66831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112965040779/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-66831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c36 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-489101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3665517/5000000) (δ := 27/2000000) (ψ := -18323/62500) 269 153
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t36 : ((-407605081521/2500000000000 : ℚ) : ℝ) ≤ stT269 36 := by
  have hc : ((-244563/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-407605081521/2500000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-244563/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c37 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-638717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1131813/2000000) (δ := 6757/500000000) (ψ := -18323/62500) 269 155
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t37 : ((-105012656033/1000000000000 : ℚ) : ℝ) ≤ stT269 37 := by
  have hc : ((-638767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105012656033/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-638767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c38 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((39289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -429083/1250000) (δ := 13481/1000000000) (ψ := -18323/62500) 269 156
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t38 : ((31859471853/1000000000000 : ℚ) : ℝ) ≤ stT269 38 := by
  have hc : ((39279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31859471853/1000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((39279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c39 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((784541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1672103/10000000) (δ := 13629/1000000000) (ψ := -18323/62500) 269 157
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t39 : ((1256190532971/10000000000000 : ℚ) : ℝ) ≤ stT269 39 := by
  have hc : ((784491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1256190532971/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((784491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c40 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((99/100 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176923/5000000) (δ := 423/31250000) (ψ := -18323/62500) 269 158
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t40 : ((15652475631/100000000000 : ℚ) : ℝ) ≤ stT269 40 := by
  have hc : ((19799/20000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15652475631/100000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((19799/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c41 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((976421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135991/2500000) (δ := 673/50000000) (ψ := -18323/62500) 269 159
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t41 : ((1524834716427/10000000000000 : ℚ) : ℝ) ≤ stT269 41 := by
  have hc : ((976371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1524834716427/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((976371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c42 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((57153/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1041637/10000000) (δ := 271/20000000) (ψ := -18323/62500) 269 160
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t42 : ((705473144567/5000000000000 : ℚ) : ℝ) ≤ stT269 42 := by
  have hc : ((457199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((705473144567/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((457199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c43 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((894639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 231587/2000000) (δ := 13557/1000000000) (ψ := -18323/62500) 269 161
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t43 : ((272846961233/2000000000000 : ℚ) : ℝ) ≤ stT269 43 := by
  have hc : ((894589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272846961233/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((894589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c44 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((467211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91041/1000000) (δ := 6769/500000000) (ψ := -18323/62500) 269 162
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t44 : ((88038632177/625000000000 : ℚ) : ℝ) ≤ stT269 44 := by
  have hc : ((233593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88038632177/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((233593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c45 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((248013/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63081/2000000) (δ := 421/31250000) (ψ := -18323/62500) 269 163
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t45 : ((739394146711/5000000000000 : ℚ) : ℝ) ≤ stT269 45 := by
  have hc : ((496001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((739394146711/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((496001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c46 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((97021/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -152937/2500000) (δ := 13479/1000000000) (ψ := -18323/62500) 269 164
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t46 : ((17880279213/125000000000 : ℚ) : ℝ) ≤ stT269 46 := by
  have hc : ((12127/12500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17880279213/125000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((12127/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c47 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((184163/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74269/400000) (δ := 13617/1000000000) (ψ := -18323/62500) 269 165
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t47 : ((537221885349/5000000000000 : ℚ) : ℝ) ≤ stT269 47 := by
  have hc : ((368301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537221885349/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((368301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c48 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((206783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -851569/2500000) (δ := 13593/1000000000) (ψ := -18323/62500) 269 166
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t48 : ((2387145951/80000000000 : ℚ) : ℝ) ≤ stT269 48 := by
  have hc : ((206733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2387145951/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((206733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c49 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-15753/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1311957/2500000) (δ := 13603/1000000000) (ψ := -18323/62500) 269 167
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t49 : ((-90026107439/1250000000000 : ℚ) : ℝ) ≤ stT269 49 := by
  have hc : ((-252073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90026107439/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-252073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c50 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-490637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115147/156250) (δ := 2699/200000000) (ψ := -18323/62500) 269 168
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t50 : ((-173475267417/1250000000000 : ℚ) : ℝ) ≤ stT269 50 := by
  have hc : ((-245331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173475267417/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-245331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c51 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-361571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5947841/10000000) (δ := 1701/125000000) (ψ := -18323/62500) 269 168
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t51 : ((-126584002119/1250000000000 : ℚ) : ℝ) ≤ stT269 51 := by
  have hc : ((-90399/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126584002119/1250000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-90399/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c52 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((248737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65971/200000) (δ := 2723/200000000) (ψ := -18323/62500) 269 169
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t52 : ((1379466789/40000000000 : ℚ) : ℝ) ≤ stT269 52 := by
  have hc : ((248687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1379466789/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((248687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c53 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((197439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400501/10000000) (δ := 6761/500000000) (ψ := -18323/62500) 269 170
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t53 : ((54237892309/400000000000 : ℚ) : ℝ) ≤ stT269 53 := by
  have hc : ((197429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54237892309/400000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((197429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c54 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((91643/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -109481/400000) (δ := 13529/1000000000) (ψ := -18323/62500) 269 171
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t54 : ((124696660491/2000000000000 : ℚ) : ℝ) ≤ stT269 54 := by
  have hc : ((91633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124696660491/2000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((91633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c55 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-765161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6105219/10000000) (δ := 13567/1000000000) (ψ := -18323/62500) 269 172
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t55 : ((-2579526281/25000000000 : ℚ) : ℝ) ≤ stT269 55 := by
  have hc : ((-765211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2579526281/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-765211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c56 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-740687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6012223/10000000) (δ := 3409/250000000) (ψ := -18323/62500) 269 172
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t56 : ((-989852038259/10000000000000 : ℚ) : ℝ) ≤ stT269 56 := by
  have hc : ((-740737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-989852038259/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-740737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c57 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((158729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55181/250000) (δ := 13559/1000000000) (ψ := -18323/62500) 269 173
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t57 : ((105112541589/1250000000000 : ℚ) : ℝ) ≤ stT269 57 := by
  have hc : ((317433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105112541589/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((317433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c58 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((150111/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1804737/10000000) (δ := 13651/1000000000) (ψ := -18323/62500) 269 174
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t58 : ((24636527433/250000000000 : ℚ) : ℝ) ≤ stT269 58 := by
  have hc : ((150101/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24636527433/250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((150101/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c59 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-370947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6016717/10000000) (δ := 2709/200000000) (ψ := -18323/62500) 269 175
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t59 : ((-12074118427/125000000000 : ℚ) : ℝ) ≤ stT269 59 := by
  have hc : ((-92743/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12074118427/125000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-92743/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c60 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-517243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2643029/5000000) (δ := 6729/500000000) (ψ := -18323/62500) 269 175
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t60 : ((-133564535307/2000000000000 : ℚ) : ℝ) ≤ stT269 60 := by
  have hc : ((-517293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133564535307/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-517293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c61 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((961711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694049/10000000) (δ := 2693/200000000) (ψ := -18323/62500) 269 176
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t61 : ((76954998203/625000000000 : ℚ) : ℝ) ≤ stT269 61 := by
  have hc : ((961661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76954998203/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((961661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c62 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-30329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -509841/1250000) (δ := 421/31250000) (ψ := -18323/62500) 269 177
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t62 : ((-9637410177/1250000000000 : ℚ) : ℝ) ≤ stT269 62 := by
  have hc : ((-15177/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9637410177/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-15177/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c63 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-892031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6681541/10000000) (δ := 421/31250000) (ψ := -18323/62500) 269 177
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t63 : ((-561958397221/5000000000000 : ℚ) : ℝ) ≤ stT269 63 := by
  have hc : ((-892081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-561958397221/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-892081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c64 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((40527/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1564309/10000000) (δ := 1703/125000000) (ψ := -18323/62500) 269 178
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t64 : ((81049/800000 : ℚ) : ℝ) ≤ stT269 64 := by
  have hc : ((81049/100000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81049/800000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((81049/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c65 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((41933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3717079/10000000) (δ := 13587/1000000000) (ψ := -18323/62500) 269 179
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t65 : ((12995115519/1250000000000 : ℚ) : ℝ) ≤ stT269 65 := by
  have hc : ((10477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12995115519/1250000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((10477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c66 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-867089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3275157/5000000) (δ := 851/62500000) (ψ := -18323/62500) 269 179
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t66 : ((-213474880437/2000000000000 : ℚ) : ℝ) ≤ stT269 66 := by
  have hc : ((-867139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213474880437/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-867139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c67 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((92787/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955339/10000000) (δ := 6747/500000000) (ψ := -18323/62500) 269 180
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t67 : ((28337803177/250000000000 : ℚ) : ℝ) ≤ stT269 67 := by
  have hc : ((46391/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28337803177/250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((46391/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c68 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-338189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478947/1000000) (δ := 6801/500000000) (ψ := -18323/62500) 269 181
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t68 : ((-410175332281/10000000000000 : ℚ) : ℝ) ≤ stT269 68 := by
  have hc : ((-338239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-410175332281/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-338239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c69 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-85277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5028223/10000000) (δ := 6801/500000000) (ψ := -18323/62500) 269 181
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t69 : ((-102673522533/2000000000000 : ℚ) : ℝ) ≤ stT269 69 := by
  have hc : ((-85287/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102673522533/2000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-85287/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c70 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((46027/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1003339/10000000) (δ := 3377/250000000) (ψ := -18323/62500) 269 182
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t70 : ((27504885543/250000000000 : ℚ) : ℝ) ≤ stT269 70 := by
  have hc : ((92049/100000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27504885543/250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((92049/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c71 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-963039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7172159/10000000) (δ := 843/62500000) (ψ := -18323/62500) 269 183
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t71 : ((-571488344799/5000000000000 : ℚ) : ℝ) ≤ stT269 71 := by
  have hc : ((-963089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-571488344799/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-963089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c72 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((313363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 558407/2500000) (δ := 2703/200000000) (ψ := -18323/62500) 269 183
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t72 : ((184636139859/2500000000000 : ℚ) : ℝ) ≤ stT269 72 := by
  have hc : ((156669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184636139859/2500000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((156669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c73 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-108327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4198341/10000000) (δ := 13523/1000000000) (ψ := -18323/62500) 269 184
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t73 : ((-31711435331/2500000000000 : ℚ) : ℝ) ≤ stT269 73 := by
  have hc : ((-108377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31711435331/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-108377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c74 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-199201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 198057/400000) (δ := 13523/1000000000) (ψ := -18323/62500) 269 184
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t74 : ((-115797821401/2500000000000 : ℚ) : ℝ) ≤ stT269 74 := by
  have hc : ((-99613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115797821401/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-99613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c75 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((385049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54047/312500) (δ := 13573/1000000000) (ψ := -18323/62500) 269 185
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t75 : ((4341672/48828125 : ℚ) : ℝ) ≤ stT269 75 := by
  have hc : ((12032/15625 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4341672/48828125 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((12032/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c76 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-192731/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7177893/10000000) (δ := 13573/1000000000) (ψ := -18323/62500) 269 185
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t76 : ((-221089153539/2000000000000 : ℚ) : ℝ) ≤ stT269 76 := by
  have hc : ((-192741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221089153539/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-192741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c77 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((994559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260917/10000000) (δ := 6783/500000000) (ψ := -18323/62500) 269 186
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t77 : ((226669485789/2000000000000 : ℚ) : ℝ) ≤ stT269 77 := by
  have hc : ((994509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226669485789/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((994509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c78 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-45369/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6769509/10000000) (δ := 3411/250000000) (ψ := -18323/62500) 269 187
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t78 : ((-51373151277/500000000000 : ℚ) : ℝ) ≤ stT269 78 := by
  have hc : ((-90743/100000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51373151277/500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-90743/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c79 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((752473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 449367/2500000) (δ := 13459/1000000000) (ψ := -18323/62500) 269 187
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t79 : ((846541335801/10000000000000 : ℚ) : ℝ) ≤ stT269 79 := by
  have hc : ((752423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((846541335801/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((752423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c80 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-4581/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1362813/2500000) (δ := 13551/1000000000) (ψ := -18323/62500) 269 188
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t80 : ((-12805402419/200000000000 : ℚ) : ℝ) ≤ stT269 80 := by
  have hc : ((-22907/40000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12805402419/200000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-22907/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c81 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((398283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2902879/10000000) (δ := 3363/250000000) (ψ := -18323/62500) 269 188
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t81 : ((442481066863/10000000000000 : ℚ) : ℝ) ≤ stT269 81 := by
  have hc : ((398233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((442481066863/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((398233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c82 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-123983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2276721/5000000) (δ := 6729/500000000) (ψ := -18323/62500) 269 189
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t82 : ((-4279500579/156250000000 : ℚ) : ℝ) ≤ stT269 82 := by
  have hc : ((-15501/62500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4279500579/156250000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-15501/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c83 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((65569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3598199/10000000) (δ := 2729/200000000) (ψ := -18323/62500) 269 189
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t83 : ((4496490453/312500000000 : ℚ) : ℝ) ≤ stT269 83 := by
  have hc : ((8193/62500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4496490453/312500000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((8193/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c84 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-25751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4055803/10000000) (δ := 26937/1000000000) (ψ := -18323/62500) 269 190
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t84 : ((-175774599/31250000000 : ℚ) : ℝ) ≤ stT269 84 := by
  have hc : ((-1611/31250 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175774599/31250000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-1611/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c85 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((193/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 780573/2000000) (δ := 6783/500000000) (ψ := -18323/62500) 269 190
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t85 : ((813489/781250000 : ℚ) : ℝ) ≤ stT269 85 := by
  have hc : ((6/625 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((813489/781250000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((6/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c86 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-5019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3939539/10000000) (δ := 1363/100000000) (ψ := -18323/62500) 269 191
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t86 : ((-683255579/1250000000000 : ℚ) : ℝ) ≤ stT269 86 := by
  have hc : ((-5069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-683255579/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-5069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c87 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((36721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3835167/10000000) (δ := 13573/1000000000) (ψ := -18323/62500) 269 191
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t87 : ((2457213697/625000000000 : ℚ) : ℝ) ≤ stT269 87 := by
  have hc : ((36671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2457213697/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((36671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c88 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-20763/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1046749/2500000) (δ := 13523/1000000000) (ψ := -18323/62500) 269 192
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t88 : ((-5536025273/500000000000 : ℚ) : ℝ) ≤ stT269 88 := by
  have hc : ((-20773/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5536025273/500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-20773/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c89 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((8183/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1705959/5000000) (δ := 337/25000000) (ψ := -18323/62500) 269 192
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t89 : ((8671835457/400000000000 : ℚ) : ℝ) ≤ stT269 89 := by
  have hc : ((8181/40000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8671835457/400000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((8181/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c90 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-20961/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4782001/10000000) (δ := 13487/1000000000) (ψ := -18323/62500) 269 193
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t90 : ((-176785099309/5000000000000 : ℚ) : ℝ) ≤ stT269 90 := by
  have hc : ((-167713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176785099309/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-167713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c91 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((489213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2649023/10000000) (δ := 6729/250000000) (ψ := -18323/62500) 269 193
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t91 : ((128195436573/2500000000000 : ℚ) : ℝ) ≤ stT269 91 := by
  have hc : ((489163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128195436573/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((489163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c92 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-163501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2854577/5000000) (δ := 6747/500000000) (ψ := -18323/62500) 269 194
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t92 : ((-340949520471/5000000000000 : ℚ) : ℝ) ≤ stT269 92 := by
  have hc : ((-327027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340949520471/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-327027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c93 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((811273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195147/1250000) (δ := 13509/1000000000) (ψ := -18323/62500) 269 194
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t93 : ((841198501073/10000000000000 : ℚ) : ℝ) ≤ stT269 93 := by
  have hc : ((811223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((841198501073/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((811223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c94 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-935927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3477099/5000000) (δ := 13501/1000000000) (ψ := -18323/62500) 269 195
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t94 : ((-482693634647/5000000000000 : ℚ) : ℝ) ≤ stT269 94 := by
  have hc : ((-935977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482693634647/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-935977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c95 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((498947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20283/1250000) (δ := 13601/1000000000) (ψ := -18323/62500) 269 195
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t95 : ((127970748929/1250000000000 : ℚ) : ℝ) ≤ stT269 95 := by
  have hc : ((249461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127970748929/1250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((249461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c96 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-483207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3602107/5000000) (δ := 6801/500000000) (ψ := -18323/62500) 269 195
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t96 : ((-15412397721/156250000000 : ℚ) : ℝ) ≤ stT269 96 := by
  have hc : ((-15101/15625 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15412397721/156250000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-15101/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c97 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((204351/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1534767/10000000) (δ := 6797/500000000) (ψ := -18323/62500) 269 196
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t97 : ((207474278621/2500000000000 : ℚ) : ℝ) ≤ stT269 97 := by
  have hc : ((408677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207474278621/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((408677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c98 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-135811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 536273/1000000) (δ := 13609/1000000000) (ψ := -18323/62500) 269 196
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t98 : ((-274405031991/5000000000000 : ℚ) : ℝ) ≤ stT269 98 := by
  have hc : ((-271647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274405031991/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-271647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c99 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((20371/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703549/2000000) (δ := 13587/1000000000) (ψ := -18323/62500) 269 197
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t99 : ((81869308983/5000000000000 : ℚ) : ℝ) ≤ stT269 99 := by
  have hc : ((81459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81869308983/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((81459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c100 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((135467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1620541/5000000) (δ := 13487/1000000000) (ψ := -18323/62500) 269 197
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t100 : ((67720932279/2500000000000 : ℚ) : ℝ) ≤ stT269 100 := by
  have hc : ((67721/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67720932279/2500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((67721/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c101 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-67377/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5775237/10000000) (δ := 13523/1000000000) (ψ := -18323/62500) 269 198
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t101 : ((-16761912629/250000000000 : ℚ) : ℝ) ≤ stT269 101 := by
  have hc : ((-33691/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16761912629/250000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-33691/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c102 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((942697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170087/2000000) (δ := 13623/1000000000) (ψ := -18323/62500) 269 198
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t102 : ((933359099109/10000000000000 : ℚ) : ℝ) ≤ stT269 102 := by
  have hc : ((942647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((933359099109/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((942647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c103 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-984371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1852853/2500000) (δ := 13523/1000000000) (ψ := -18323/62500) 269 198
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t103 : ((-96997954393/1000000000000 : ℚ) : ℝ) ≤ stT269 103 := by
  have hc : ((-984421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96997954393/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-984421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c104 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((752089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449731/2500000) (δ := 13573/1000000000) (ψ := -18323/62500) 269 199
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t104 : ((36871720131/500000000000 : ℚ) : ℝ) ≤ stT269 104 := by
  have hc : ((752039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36871720131/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((752039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c105 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-140017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927313/2000000) (δ := 13473/1000000000) (ψ := -18323/62500) 269 199
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t105 : ((-68333563921/2500000000000 : ℚ) : ℝ) ≤ stT269 105 := by
  have hc : ((-70021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68333563921/2500000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-70021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c106 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-151573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1174243/2500000) (δ := 13637/1000000000) (ψ := -18323/62500) 269 200
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t106 : ((-36811253757/1250000000000 : ℚ) : ℝ) ≤ stT269 106 := by
  have hc : ((-75799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36811253757/1250000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-75799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c107 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((159571/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404417/2500000) (δ := 6733/500000000) (ψ := -18323/62500) 269 200
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t107 : ((9640835181/125000000000 : ℚ) : ℝ) ≤ stT269 107 := by
  have hc : ((159561/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9640835181/125000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((159561/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c108 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-999969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7834431/10000000) (δ := 2709/200000000) (ψ := -18323/62500) 269 201
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t108 : ((-962269282769/10000000000000 : ℚ) : ℝ) ≤ stT269 108 := by
  have hc : ((-1000019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-962269282769/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-1000019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c109 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((198337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409067/2500000) (δ := 6779/500000000) (ψ := -18323/62500) 269 201
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t109 : ((189960362537/2500000000000 : ℚ) : ℝ) ≤ stT269 109 := by
  have hc : ((396649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189960362537/2500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((396649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c110 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-229281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4505339/10000000) (δ := 2729/200000000) (ψ := -18323/62500) 269 201
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t110 : ((-218658623253/10000000000000 : ℚ) : ℝ) ≤ stT269 110 := by
  have hc : ((-229331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218658623253/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-229331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c111 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-458077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5116567/10000000) (δ := 3363/250000000) (ψ := -18323/62500) 269 202
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t111 : ((-217417453533/5000000000000 : ℚ) : ℝ) ≤ stT269 111 := by
  have hc : ((-458127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217417453533/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-458127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c112 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((933793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7147/78125) (δ := 13651/1000000000) (ψ := -18323/62500) 269 202
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t112 : ((882304031873/10000000000000 : ℚ) : ℝ) ≤ stT269 112 := by
  have hc : ((933743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((882304031873/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((933743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c113 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-926977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6892669/10000000) (δ := 3363/250000000) (ψ := -18323/62500) 269 202
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t113 : ((-872073766467/10000000000000 : ℚ) : ℝ) ≤ stT269 113 := by
  have hc : ((-927027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-872073766467/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-927027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c114 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((402943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1445083/5000000) (δ := 1693/125000000) (ψ := -18323/62500) 269 203
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t114 : ((75468708081/2000000000000 : ℚ) : ℝ) ≤ stT269 114 := by
  have hc : ((402893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75468708081/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((402893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c115 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((73719/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2983247/10000000) (δ := 3411/250000000) (ψ := -18323/62500) 269 203
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t115 : ((8591742167/250000000000 : ℚ) : ℝ) ≤ stT269 115 := by
  have hc : ((73709/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8591742167/250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((73709/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c116 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-464201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6902211/10000000) (δ := 13537/1000000000) (ψ := -18323/62500) 269 204
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t116 : ((-215511581901/2500000000000 : ℚ) : ℝ) ≤ stT269 116 := by
  have hc : ((-232113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215511581901/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-232113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c117 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((224911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225921/2000000) (δ := 6783/500000000) (ψ := -18323/62500) 269 204
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t117 : ((831674653/10000000000 : ℚ) : ℝ) ≤ stT269 117 := by
  have hc : ((449797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((831674653/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((449797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c118 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-65897/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57423/125000) (δ := 13637/1000000000) (ψ := -18323/62500) 269 204
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t118 : ((-4853971037/200000000000 : ℚ) : ℝ) ≤ stT269 118 := by
  have hc : ((-131819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4853971037/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-131819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c119 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-56861/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -543903/1000000) (δ := 1353/100000000) (ψ := -18323/62500) 269 205
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t119 : ((-26064502667/500000000000 : ℚ) : ℝ) ≤ stT269 119 := by
  have hc : ((-28433/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26064502667/500000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-28433/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c120 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((498577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47163/2500000) (δ := 13473/1000000000) (ψ := -18323/62500) 269 205
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t120 : ((5688914553/62500000000 : ℚ) : ℝ) ≤ stT269 120 := by
  have hc : ((62319/62500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5688914553/62500000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((62319/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c121 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-6721/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1153919/2000000) (δ := 13473/1000000000) (ψ := -18323/62500) 269 205
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t121 : ((-12220910313/200000000000 : ℚ) : ℝ) ≤ stT269 121 := by
  have hc : ((-13443/20000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12220910313/200000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-13443/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c122 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-47349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4403357/10000000) (δ := 337/25000000) (ψ := -18323/62500) 269 206
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t122 : ((-42879112917/2500000000000 : ℚ) : ℝ) ≤ stT269 122 := by
  have hc : ((-94723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42879112917/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-94723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c123 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((181409/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 543231/5000000) (δ := 13523/1000000000) (ψ := -18323/62500) 269 206
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t123 : ((163561854931/2000000000000 : ℚ) : ℝ) ≤ stT269 123 := by
  have hc : ((181399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163561854931/2000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((181399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c124 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-431691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6531829/10000000) (δ := 13523/1000000000) (ψ := -18323/62500) 269 206
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t124 : ((-96923156083/1250000000000 : ℚ) : ℝ) ≤ stT269 124 := by
  have hc : ((-107929/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96923156083/1250000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-107929/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c125 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((30483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47181/125000) (δ := 2723/200000000) (ψ := -18323/62500) 269 207
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t125 : ((13621228783/2500000000000 : ℚ) : ℝ) ≤ stT269 125 := by
  have hc : ((15229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13621228783/2500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((15229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c126 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((805869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316827/2000000) (δ := 843/62500000) (ψ := -18323/62500) 269 207
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t126 : ((71787997253/1000000000000 : ℚ) : ℝ) ≤ stT269 126 := by
  have hc : ((805819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71787997253/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((805819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c127 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-23203/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1380063/2000000) (δ := 3397/250000000) (ψ := -18323/62500) 269 207
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t127 : ((-82361814669/1000000000000 : ℚ) : ℝ) ≤ stT269 127 := by
  have hc : ((-92817/100000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82361814669/1000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-92817/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c128 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((78453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3533097/10000000) (δ := 1701/125000000) (ψ := -18323/62500) 269 208
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t128 : ((17330293981/1250000000000 : ℚ) : ℝ) ≤ stT269 128 := by
  have hc : ((19607/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17330293981/1250000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((19607/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c129 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((97183/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1700433/10000000) (δ := 2699/200000000) (ψ := -18323/62500) 269 208
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t129 : ((6844741563/100000000000 : ℚ) : ℝ) ≤ stT269 129 := by
  have hc : ((388707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6844741563/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((388707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c130 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-463549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3446739/5000000) (δ := 2699/200000000) (ψ := -18323/62500) 269 208
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t130 : ((-203290874433/2500000000000 : ℚ) : ℝ) ≤ stT269 130 := by
  have hc : ((-231787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203290874433/2500000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-231787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c131 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((53061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -732237/2000000) (δ := 6751/500000000) (ψ := -18323/62500) 269 209
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t131 : ((1448055167/156250000000 : ℚ) : ℝ) ≤ stT269 131 := by
  have hc : ((13259/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1448055167/156250000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((13259/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c132 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((33433/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363227/2500000) (δ := 13601/1000000000) (ψ := -18323/62500) 269 209
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t132 : ((7274485307/100000000000 : ℚ) : ℝ) ≤ stT269 132 := by
  have hc : ((33431/40000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7274485307/100000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((33431/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c133 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-862689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16321/25000) (δ := 13601/1000000000) (ψ := -18323/62500) 269 209
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t133 : ((-74808961429/1000000000000 : ℚ) : ℝ) ≤ stT269 133 := by
  have hc : ((-862739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74808961429/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-862739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c134 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-42969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4142101/10000000) (δ := 13497/500000000) (ψ := -18323/62500) 269 210
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t134 : ((-18570591893/2500000000000 : ℚ) : ℝ) ≤ stT269 134 := by
  have hc : ((-21497/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18570591893/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-21497/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c135 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((14714/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 857903/10000000) (δ := 6747/500000000) (ψ := -18323/62500) 269 210
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t135 : ((202609732413/2500000000000 : ℚ) : ℝ) ≤ stT269 135 := by
  have hc : ((470823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202609732413/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((470823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c136 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-171797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291051/500000) (δ := 6797/500000000) (ψ := -18323/62500) 269 210
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t136 : ((-294650887167/5000000000000 : ℚ) : ℝ) ≤ stT269 136 := by
  have hc : ((-343619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294650887167/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-343619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c137 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-401597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4960141/10000000) (δ := 13587/1000000000) (ψ := -18323/62500) 269 211
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t137 : ((-171575163813/5000000000000 : ℚ) : ℝ) ≤ stT269 137 := by
  have hc : ((-401647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171575163813/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-401647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c138 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((15619/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277/40000) (δ := 13487/1000000000) (ψ := -18323/62500) 269 211
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t138 : ((53180409681/625000000000 : ℚ) : ℝ) ≤ stT269 138 := by
  have hc : ((499783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53180409681/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((499783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c139 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-168517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2393201/5000000) (δ := 3379/250000000) (ψ := -18323/62500) 269 211
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t139 : ((-71477735219/2500000000000 : ℚ) : ℝ) ≤ stT269 139 := by
  have hc : ((-84271/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71477735219/2500000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-84271/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c140 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-95501/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1220149/2000000) (δ := 3381/250000000) (ψ := -18323/62500) 269 212
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t140 : ((-64574743899/1000000000000 : ℚ) : ℝ) ≤ stT269 140 := by
  have hc : ((-382029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64574743899/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-382029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c141 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((216241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -657147/5000000) (δ := 13579/1000000000) (ψ := -18323/62500) 269 212
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t141 : ((364194095007/5000000000000 : ℚ) : ℝ) ≤ stT269 141 := by
  have hc : ((432457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364194095007/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((432457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c142 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((38839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1719199/5000000) (δ := 13579/1000000000) (ψ := -18323/62500) 269 212
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t142 : ((32584559049/2000000000000 : ℚ) : ℝ) ≤ stT269 142 := by
  have hc : ((38829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32584559049/2000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((38829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c143 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-248157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7550229/10000000) (δ := 421/31250000) (ψ := -18323/62500) 269 213
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t143 : ((-415060014377/5000000000000 : ℚ) : ℝ) ≤ stT269 143 := by
  have hc : ((-496339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415060014377/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-496339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c144 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((103139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -572769/2000000) (δ := 13631/1000000000) (ψ := -18323/62500) 269 213
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t144 : ((171877431249/5000000000000 : ℚ) : ℝ) ≤ stT269 144 := by
  have hc : ((206253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171877431249/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((206253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c145 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((754387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1790191/10000000) (δ := 13531/1000000000) (ψ := -18323/62500) 269 213
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t145 : ((313221089499/5000000000000 : ℚ) : ℝ) ≤ stT269 145 := by
  have hc : ((754337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313221089499/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((754337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c146 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-838263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 801527/1250000) (δ := 421/31250000) (ψ := -18323/62500) 269 213
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t146 : ((-346896434339/5000000000000 : ℚ) : ℝ) ≤ stT269 146 := by
  have hc : ((-838313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346896434339/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-838313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c147 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-30633/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4705329/10000000) (δ := 6819/500000000) (ψ := -18323/62500) 269 214
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t147 : ((-12634912053/500000000000 : ℚ) : ℝ) ≤ stT269 147 := by
  have hc : ((-15319/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12634912053/500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-15319/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c148 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((124787/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145981/10000000) (δ := 6769/500000000) (ψ := -18323/62500) 269 214
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t148 : ((205138055631/2500000000000 : ℚ) : ℝ) ≤ stT269 148 := by
  have hc : ((499123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205138055631/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((499123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c149 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-45319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4382701/10000000) (δ := 2693/200000000) (ψ := -18323/62500) 269 214
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t149 : ((-2321063463/156250000000 : ℚ) : ℝ) ≤ stT269 149 := by
  have hc : ((-90663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2321063463/156250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-90663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c150 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-916801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6826977/10000000) (δ := 6729/500000000) (ψ := -18323/62500) 269 215
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t150 : ((-748606090947/10000000000000 : ℚ) : ℝ) ≤ stT269 150 := by
  have hc : ((-916851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-748606090947/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-916851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c151 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((146761/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2358483/10000000) (δ := 2729/200000000) (ψ := -18323/62500) 269 215
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t151 : ((59711084159/1250000000000 : ℚ) : ℝ) ≤ stT269 151 := by
  have hc : ((293497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59711084159/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((293497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c152 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((134651/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2080487/10000000) (δ := 6779/500000000) (ψ := -18323/62500) 269 215
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t152 : ((109208257587/2000000000000 : ℚ) : ℝ) ≤ stT269 152 := by
  have hc : ((134641/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109208257587/2000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((134641/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c153 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-85489/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6490339/10000000) (δ := 2709/200000000) (ψ := -18323/62500) 269 215
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t153 : ((-34558940391/500000000000 : ℚ) : ℝ) ≤ stT269 153 := by
  have hc : ((-42747/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34558940391/500000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-42747/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c154 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-355827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4836489/10000000) (δ := 13551/1000000000) (ψ := -18323/62500) 269 216
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t154 : ((-286773871771/10000000000000 : ℚ) : ℝ) ≤ stT269 154 := by
  have hc : ((-355877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286773871771/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-355877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c155 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((981339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -483733/10000000) (δ := 13651/1000000000) (ψ := -18323/62500) 269 216
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t155 : ((788189969291/10000000000000 : ℚ) : ℝ) ≤ stT269 155 := by
  have hc : ((981289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((788189969291/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((981289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c156 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((3437/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 480131/1250000) (δ := 847/62500000) (ψ := -18323/62500) 269 216
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t156 : ((536679/195312500 : ℚ) : ℝ) ≤ stT269 156 := by
  have hc : ((429/12500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((536679/195312500 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((429/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c157 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-198709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302791/400000) (δ := 13459/1000000000) (ψ := -18323/62500) 269 217
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t157 : ((-158595050553/2000000000000 : ℚ) : ℝ) ≤ stT269 157 := by
  have hc : ((-198719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158595050553/2000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-198719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c158 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((248199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1649969/5000000) (δ := 13459/1000000000) (ψ := -18323/62500) 269 217
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t158 : ((197416673993/10000000000000 : ℚ) : ℝ) ≤ stT269 158 := by
  have hc : ((248149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197416673993/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((248149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c159 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((9297/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 942999/10000000) (δ := 13459/1000000000) (ψ := -18323/62500) 269 217
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t159 : ((14745197243/200000000000 : ℚ) : ℝ) ≤ stT269 159 := by
  have hc : ((18593/20000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14745197243/200000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((18593/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c160 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-94641/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1031861/2000000) (δ := 13459/1000000000) (ψ := -18323/62500) 269 217
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t160 : ((-7482824107/200000000000 : ℚ) : ℝ) ≤ stT269 160 := by
  have hc : ((-94651/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7482824107/200000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-94651/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c161 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-206597/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6358647/10000000) (δ := 13467/1000000000) (ψ := -18323/62500) 269 218
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t161 : ((-325662439309/5000000000000 : ℚ) : ℝ) ≤ stT269 161 := by
  have hc : ((-413219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325662439309/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-413219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c162 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((638837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2194527/10000000) (δ := 13467/1000000000) (ψ := -18323/62500) 269 218
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t162 : ((250939168719/5000000000000 : ℚ) : ℝ) ≤ stT269 162 := by
  have hc : ((638787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250939168719/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((638787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c163 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((712607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1943971/10000000) (δ := 13567/1000000000) (ψ := -18323/62500) 269 218
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t163 : ((27905869791/500000000000 : ℚ) : ℝ) ≤ stT269 163 := by
  have hc : ((712557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27905869791/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((712557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c164 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-94079/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1211423/2000000) (δ := 423/31250000) (ψ := -18323/62500) 269 218
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t164 : ((-293873020329/5000000000000 : ℚ) : ℝ) ≤ stT269 164 := by
  have hc : ((-376341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293873020329/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-376341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c165 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-304299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5562721/10000000) (δ := 13629/1000000000) (ψ := -18323/62500) 269 219
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t165 : ((-59228982419/1250000000000 : ℚ) : ℝ) ≤ stT269 165 := by
  have hc : ((-76081/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59228982419/1250000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-76081/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c166 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((1651/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -749637/5000000) (δ := 13529/1000000000) (ψ := -18323/62500) 269 219
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t166 : ((256269207/4000000000 : ℚ) : ℝ) ≤ stT269 166 := by
  have hc : ((16509/20000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256269207/4000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((16509/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c167 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((526829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 634957/2500000) (δ := 13629/1000000000) (ψ := -18323/62500) 269 219
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t167 : ((407633706117/10000000000000 : ℚ) : ℝ) ≤ stT269 167 := by
  have hc : ((526779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407633706117/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((526779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c168 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-433983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6554721/10000000) (δ := 6787/500000000) (ψ := -18323/62500) 269 219
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t168 : ((-41855568767/625000000000 : ℚ) : ℝ) ≤ stT269 168 := by
  have hc : ((-54251/62500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41855568767/625000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-54251/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c169 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-237093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -516209/1000000) (δ := 6811/500000000) (ψ := -18323/62500) 269 220
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t169 : ((-91199258129/2500000000000 : ℚ) : ℝ) ≤ stT269 169 := by
  have hc : ((-118559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91199258129/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-118559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c170 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((888001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1194541/10000000) (δ := 13581/1000000000) (ψ := -18323/62500) 269 220
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t170 : ((170256612691/2500000000000 : ℚ) : ℝ) ≤ stT269 170 := by
  have hc : ((887951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170256612691/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((887951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c171 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((45369/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374869/5000000) (δ := 6811/500000000) (ψ := -18323/62500) 269 220
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t171 : ((8672678179/250000000000 : ℚ) : ℝ) ≤ stT269 171 := by
  have hc : ((11341/25000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8672678179/250000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((11341/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c172 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-890121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6671019/10000000) (δ := 13581/1000000000) (ψ := -18323/62500) 269 220
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t172 : ((-678749156303/10000000000000 : ℚ) : ℝ) ≤ stT269 172 := by
  have hc : ((-890171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-678749156303/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-890171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c173 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-465821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1027679/2000000) (δ := 2703/200000000) (ψ := -18323/62500) 269 221
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t173 : ((-177097599553/5000000000000 : ℚ) : ℝ) ≤ stT269 173 := by
  have hc : ((-465871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177097599553/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-465871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c174 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((218803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1262307/10000000) (δ := 2723/200000000) (ψ := -18323/62500) 269 221
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t174 : ((165864640469/2500000000000 : ℚ) : ℝ) ≤ stT269 174 := by
  have hc : ((437581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165864640469/2500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((437581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c175 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((509119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2591589/10000000) (δ := 2703/200000000) (ψ := -18323/62500) 269 221
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t175 : ((48102438879/1250000000000 : ℚ) : ℝ) ≤ stT269 175 := by
  have hc : ((509069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48102438879/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((509069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c176 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-420357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3211747/5000000) (δ := 2703/200000000) (ψ := -18323/62500) 269 221
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t176 : ((-158437561789/2500000000000 : ℚ) : ℝ) ≤ stT269 176 := by
  have hc : ((-210191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158437561789/2500000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-210191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c177 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-145033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5474219/10000000) (δ := 1701/125000000) (ψ := -18323/62500) 269 222
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t177 : ((-218046029877/5000000000000 : ℚ) : ℝ) ≤ stT269 177 := by
  have hc : ((-290091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218046029877/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-290091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c178 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((78121/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105343/625000) (δ := 2699/200000000) (ψ := -18323/62500) 269 222
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t178 : ((14637590899/250000000000 : ℚ) : ℝ) ≤ stT269 178 := by
  have hc : ((19529/25000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14637590899/250000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((19529/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c179 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((672789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2082059/10000000) (δ := 2719/200000000) (ψ := -18323/62500) 269 222
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t179 : ((100565734893/2000000000000 : ℚ) : ℝ) ≤ stT269 179 := by
  have hc : ((672739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100565734893/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((672739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c180 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-1103/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1457139/2500000) (δ := 3377/250000000) (ψ := -18323/62500) 269 222
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t180 : ((-5138670603/100000000000 : ℚ) : ℝ) ≤ stT269 180 := by
  have hc : ((-27577/40000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5138670603/100000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-27577/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c181 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-777483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6153623/10000000) (δ := 17/1250000) (ψ := -18323/62500) 269 223
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t181 : ((-115587278247/2000000000000 : ℚ) : ℝ) ≤ stT269 181 := by
  have hc : ((-777533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115587278247/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-777533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c182 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((139387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2448417/10000000) (δ := 17/1250000) (ψ := -18323/62500) 269 223
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t182 : ((206622417501/5000000000000 : ℚ) : ℝ) ≤ stT269 182 := by
  have hc : ((278749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206622417501/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((278749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c183 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((17603/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1236547/10000000) (δ := 27/2000000) (ψ := -18323/62500) 269 223
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t183 : ((6505884021/100000000000 : ℚ) : ℝ) ≤ stT269 183 := by
  have hc : ((8801/10000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6505884021/100000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((8801/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c184 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-379971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4901403/10000000) (δ := 27/2000000) (ψ := -18323/62500) 269 223
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t184 : ((-28015528141/1000000000000 : ℚ) : ℝ) ≤ stT269 184 := by
  have hc : ((-380021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28015528141/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-380021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c185 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-961887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7161543/10000000) (δ := 13493/1000000000) (ψ := -18323/62500) 269 224
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t185 : ((-141446102291/2000000000000 : ℚ) : ℝ) ≤ stT269 185 := by
  have hc : ((-961937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141446102291/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-961937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c186 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((155669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353623/1000000) (δ := 13493/1000000000) (ψ := -18323/62500) 269 224
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t186 : ((22821059493/2000000000000 : ℚ) : ℝ) ≤ stT269 186 := by
  have hc : ((155619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22821059493/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((155619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c187 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((999611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13943/2000000) (δ := 13493/1000000000) (ψ := -18323/62500) 269 224
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t187 : ((91368871449/1250000000000 : ℚ) : ℝ) ≤ stT269 187 := by
  have hc : ((999561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91368871449/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((999561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c188 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((108041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3656359/10000000) (δ := 13593/1000000000) (ψ := -18323/62500) 269 224
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t188 : ((19690107021/2500000000000 : ℚ) : ℝ) ≤ stT269 188 := by
  have hc : ((107991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19690107021/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((107991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c189 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-968421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7224039/10000000) (δ := 13493/1000000000) (ψ := -18323/62500) 269 224
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t189 : ((-704459026103/10000000000000 : ℚ) : ℝ) ≤ stT269 189 := by
  have hc : ((-968471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-704459026103/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-968471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c190 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-392419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2467571/5000000) (δ := 6793/500000000) (ψ := -18323/62500) 269 225
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t190 : ((-284727232713/10000000000000 : ℚ) : ℝ) ≤ stT269 190 := by
  have hc : ((-392469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284727232713/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-392469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c191 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((13222/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35123/250000) (δ := 13517/1000000000) (ψ := -18323/62500) 269 225
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t191 : ((153064482173/2500000000000 : ℚ) : ℝ) ≤ stT269 191 := by
  have hc : ((423079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153064482173/2500000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((423079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c192 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((665433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 263351/1250000) (δ := 13617/1000000000) (ψ := -18323/62500) 269 225
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t192 : ((480198261121/10000000000000 : ℚ) : ℝ) ≤ stT269 192 := by
  have hc : ((665383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480198261121/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((665383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c193 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-620459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5600311/10000000) (δ := 13617/1000000000) (ψ := -18323/62500) 269 225
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t193 : ((-55831538293/1250000000000 : ℚ) : ℝ) ≤ stT269 193 := by
  have hc : ((-620509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55831538293/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-620509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c194 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-882933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6632173/10000000) (δ := 13579/1000000000) (ψ := -18323/62500) 269 226
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t194 : ((-633945591697/10000000000000 : ℚ) : ℝ) ≤ stT269 194 := by
  have hc : ((-882983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-633945591697/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-882983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c195 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((296441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3174581/10000000) (δ := 3381/250000000) (ψ := -18323/62500) 269 226
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t195 : ((106124872287/5000000000000 : ℚ) : ℝ) ≤ stT269 195 := by
  have hc : ((296391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106124872287/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((296391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c196 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((497187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66331/2500000) (δ := 1703/125000000) (ψ := -18323/62500) 269 226
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t196 : ((35511535917/500000000000 : ℚ) : ℝ) ≤ stT269 196 := by
  have hc : ((248581/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35511535917/500000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((248581/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c197 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((95553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3687743/10000000) (δ := 13579/1000000000) (ψ := -18323/62500) 269 226
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t197 : ((6804302241/1000000000000 : ℚ) : ℝ) ≤ stT269 197 := by
  have hc : ((95503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6804302241/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((95503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c198 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-954007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7092813/10000000) (δ := 1703/125000000) (ψ := -18323/62500) 269 226
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t198 : ((-67801968819/1000000000000 : ℚ) : ℝ) ≤ stT269 198 := by
  have hc : ((-954057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67801968819/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-954057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c199 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-496963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -522723/1000000) (δ := 13531/1000000000) (ψ := -18323/62500) 269 227
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t199 : ((-176161784733/5000000000000 : ℚ) : ℝ) ≤ stT269 199 := by
  have hc : ((-497013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176161784733/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-497013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c200 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((736761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -464081/2500000) (δ := 421/31250000) (ψ := -18323/62500) 269 227
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t200 : ((260466384183/5000000000000 : ℚ) : ℝ) ≤ stT269 200 := by
  have hc : ((736711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260466384183/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((736711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c201 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((25807/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1497837/10000000) (δ := 421/31250000) (ψ := -18323/62500) 269 227
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t201 : ((58245556203/1000000000000 : ℚ) : ℝ) ≤ stT269 201 := by
  have hc : ((412887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58245556203/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((412887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c202 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-71073/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4835253/10000000) (δ := 13531/1000000000) (ψ := -18323/62500) 269 227
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t202 : ((-25006928317/1000000000000 : ℚ) : ℝ) ≤ stT269 202 := by
  have hc : ((-71083/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25006928317/1000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-71083/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c203 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-992699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -943963/1250000) (δ := 2713/200000000) (ψ := -18323/62500) 269 228
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t203 : ((-696773791387/10000000000000 : ℚ) : ℝ) ≤ stT269 203 := by
  have hc : ((-992749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-696773791387/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-992749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c204 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-12767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4247039/10000000) (δ := 2713/200000000) (ψ := -18323/62500) 269 228
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t204 : ((-2235550213/250000000000 : ℚ) : ℝ) ≤ stT269 204 := by
  have hc : ((-3193/25000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2235550213/250000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-3193/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c205 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((231849/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479257/5000000) (δ := 2713/200000000) (ψ := -18323/62500) 269 228
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t205 : ((32384313339/500000000000 : ℚ) : ℝ) ≤ stT269 205 := by
  have hc : ((463673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32384313339/500000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((463673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c206 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((601353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1157003/5000000) (δ := 6769/500000000) (ψ := -18323/62500) 269 228
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t206 : ((418947643099/10000000000000 : ℚ) : ℝ) ≤ stT269 206 := by
  have hc : ((601303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418947643099/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((601303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c207 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-76389/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2785327/5000000) (δ := 2713/200000000) (ψ := -18323/62500) 269 228
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t207 : ((-212393768469/5000000000000 : ℚ) : ℝ) ≤ stT269 207 := by
  have hc : ((-305581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212393768469/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-305581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c208 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-37101/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -689633/1000000) (δ := 13557/1000000000) (ψ := -18323/62500) 269 229
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t208 : ((-200986951/3125000000 : ℚ) : ℝ) ≤ stT269 208 := by
  have hc : ((-37103/40000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200986951/3125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-37103/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c209 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((102263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -734177/2000000) (δ := 6773/500000000) (ψ := -18323/62500) 269 229
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t209 : ((35351081541/5000000000000 : ℚ) : ℝ) ≤ stT269 209 := by
  have hc : ((102213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35351081541/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((102213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c210 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((491529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460841/10000000) (δ := 13457/1000000000) (ψ := -18323/62500) 269 229
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t210 : ((4239621347/62500000000 : ℚ) : ℝ) ≤ stT269 210 := by
  have hc : ((30719/31250 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4239621347/62500000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((30719/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c211 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((459313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1366969/5000000) (δ := 6823/500000000) (ψ := -18323/62500) 269 229
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t211 : ((79042377141/2500000000000 : ℚ) : ℝ) ≤ stT269 211 := by
  have hc : ((459263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79042377141/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((459263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c212 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-71361/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1182717/2000000) (δ := 6773/500000000) (ψ := -18323/62500) 269 229
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t212 : ((-24507191449/500000000000 : ℚ) : ℝ) ≤ stT269 212 := by
  have hc : ((-35683/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24507191449/500000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-35683/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c213 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-882461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6629661/10000000) (δ := 271/20000000) (ψ := -18323/62500) 269 230
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t213 : ((-604686829579/10000000000000 : ℚ) : ℝ) ≤ stT269 213 := by
  have hc : ((-882511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604686829579/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-882511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c214 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((44487/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1739869/5000000) (δ := 13453/1000000000) (ψ := -18323/62500) 269 230
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t214 : ((12160840433/1000000000000 : ℚ) : ℝ) ≤ stT269 214 := by
  have hc : ((88949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12160840433/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((88949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c215 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((495259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -344543/10000000) (δ := 13453/1000000000) (ψ := -18323/62500) 269 230
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t215 : ((84436654149/1250000000000 : ℚ) : ℝ) ≤ stT269 215 := by
  have hc : ((247617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84436654149/1250000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((247617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c216 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((222129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1388063/5000000) (δ := 13453/1000000000) (ψ := -18323/62500) 269 230
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t216 : ((18890306119/625000000000 : ℚ) : ℝ) ≤ stT269 216 := by
  have hc : ((27763/62500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18890306119/625000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((27763/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c217 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-352399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183823/312500) (δ := 271/20000000) (ψ := -18323/62500) 269 230
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t217 : ((-5981031757/125000000000 : ℚ) : ℝ) ≤ stT269 217 := by
  have hc : ((-44053/62500 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5981031757/125000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-44053/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c218 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-450631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3366837/5000000) (δ := 13543/1000000000) (ψ := -18323/62500) 269 231
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t218 : ((-4769109369/78125000000 : ℚ) : ℝ) ≤ stT269 218 := by
  have hc : ((-14083/15625 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4769109369/78125000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-14083/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c219 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((108247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3655843/10000000) (δ := 673/50000000) (ψ := -18323/62500) 269 231
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t219 : ((73112716189/10000000000000 : ℚ) : ℝ) ≤ stT269 219 := by
  have hc : ((108197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73112716189/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((108197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c220 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((972087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148017/2500000) (δ := 13643/1000000000) (ψ := -18323/62500) 269 231
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t220 : ((655346373363/10000000000000 : ℚ) : ℝ) ≤ stT269 220 := by
  have hc : ((972037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((655346373363/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((972037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c221 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((554411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1228927/5000000) (δ := 13643/1000000000) (ψ := -18323/62500) 269 231
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t221 : ((11653222581/312500000000 : ℚ) : ℝ) ≤ stT269 221 := by
  have hc : ((554361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11653222581/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((554361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c222 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-293267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5493923/10000000) (δ := 673/50000000) (ψ := -18323/62500) 269 231
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t222 : ((-49211244711/1250000000000 : ℚ) : ℝ) ≤ stT269 222 := by
  have hc : ((-73323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49211244711/1250000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-73323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c223 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-9651/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1797889/2500000) (δ := 13567/1000000000) (ψ := -18323/62500) 269 232
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t223 : ((-258525079/4000000000 : ℚ) : ℝ) ≤ stT269 223 := by
  have hc : ((-19303/20000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258525079/4000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-19303/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c224 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-51031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418259/1000000) (δ := 3409/250000000) (ψ := -18323/62500) 269 232
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t224 : ((-1066039707/156250000000 : ℚ) : ℝ) ≤ stT269 224 := by
  have hc : ((-3191/31250 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1066039707/156250000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-3191/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c225 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((889383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -593503/5000000) (δ := 3409/250000000) (ψ := -18323/62500) 269 232
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t225 : ((296444036889/5000000000000 : ℚ) : ℝ) ≤ stT269 225 := by
  have hc : ((889333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296444036889/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((889333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c226 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((753063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1795229/10000000) (δ := 6759/250000000) (ψ := -18323/62500) 269 232
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t226 : ((50089671747/1000000000000 : ℚ) : ℝ) ≤ stT269 226 := by
  have hc : ((753013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50089671747/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((753013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c227 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-82179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95287/200000) (δ := 3409/250000000) (ψ := -18323/62500) 269 232
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t227 : ((-27276235573/1250000000000 : ℚ) : ℝ) ≤ stT269 227 := by
  have hc : ((-164383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27276235573/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-164383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c228 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-998573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7720391/10000000) (δ := 3409/250000000) (ψ := -18323/62500) 269 232
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t228 : ((-661355058341/10000000000000 : ℚ) : ℝ) ≤ stT269 228 := by
  have hc : ((-998623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-661355058341/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-998623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c229 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-86449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5044443/10000000) (δ := 13529/1000000000) (ψ := -18323/62500) 269 233
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t229 : ((-57133749921/2000000000000 : ℚ) : ℝ) ≤ stT269 229 := by
  have hc : ((-86459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57133749921/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-86459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c230 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((132647/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2114159/10000000) (δ := 13629/1000000000) (ψ := -18323/62500) 269 233
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t230 : ((4372909253/100000000000 : ℚ) : ℝ) ≤ stT269 230 := by
  have hc : ((132637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4372909253/100000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((132637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c231 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((189761/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160683/2000000) (δ := 13629/1000000000) (ψ := -18323/62500) 269 233
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t231 : ((124846860201/2000000000000 : ℚ) : ℝ) ≤ stT269 231 := by
  have hc : ((189751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124846860201/2000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((189751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c232 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((43673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1854173/5000000) (δ := 13629/1000000000) (ψ := -18323/62500) 269 233
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t232 : ((55969353/9765625000 : ℚ) : ℝ) ≤ stT269 232 := by
  have hc : ((1364/15625 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55969353/9765625000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((1364/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c233 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-876979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1650209/2500000) (δ := 13529/1000000000) (ψ := -18323/62500) 269 233
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t233 : ((-287280496269/5000000000000 : ℚ) : ℝ) ≤ stT269 233 := by
  have hc : ((-877029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287280496269/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-877029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c234 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-795607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6227011/10000000) (δ := 6791/500000000) (ψ := -18323/62500) 269 234
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t234 : ((-520137689697/10000000000000 : ℚ) : ℝ) ≤ stT269 234 := by
  have hc : ((-795657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-520137689697/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-795657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c235 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((14073/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1679601/5000000) (δ := 6791/500000000) (ψ := -18323/62500) 269 234
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t235 : ((9178173419/625000000000 : ℚ) : ℝ) ≤ stT269 235 := by
  have hc : ((112559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9178173419/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((112559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c236 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((489891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251783/5000000) (δ := 13621/1000000000) (ψ := -18323/62500) 269 234
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t236 : ((2491213543/39062500000 : ℚ) : ℝ) ≤ stT269 236 := by
  have hc : ((244933/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2491213543/39062500000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((244933/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c237 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((9266/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1169983/5000000) (δ := 13521/1000000000) (ψ := -18323/62500) 269 234
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t237 : ((192588764103/5000000000000 : ℚ) : ℝ) ≤ stT269 237 := by
  have hc : ((296487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192588764103/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((296487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c238 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-238753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5171527/10000000) (δ := 13621/1000000000) (ψ := -18323/62500) 269 234
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t238 : ((-19347106839/625000000000 : ℚ) : ℝ) ≤ stT269 238 := by
  have hc : ((-119389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19347106839/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-119389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c239 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-998493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7716711/10000000) (δ := 6807/500000000) (ψ := -18323/62500) 269 235
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t239 : ((-645904543921/10000000000000 : ℚ) : ℝ) ≤ stT269 239 := by
  have hc : ((-998543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-645904543921/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-998543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c240 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-382689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2454377/5000000) (δ := 13489/1000000000) (ψ := -18323/62500) 269 235
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t240 : ((-123528629511/5000000000000 : ℚ) : ℝ) ≤ stT269 240 := by
  have hc : ((-382739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123528629511/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-382739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c241 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((165933/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2112499/10000000) (δ := 13489/1000000000) (ψ := -18323/62500) 269 235
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t241 : ((53439342799/1250000000000 : ℚ) : ℝ) ≤ stT269 241 := by
  have hc : ((331841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53439342799/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((331841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c242 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((96407/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 672189/10000000) (δ := 13489/1000000000) (ψ := -18323/62500) 269 235
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t242 : ((3873094953/62500000000 : ℚ) : ℝ) ≤ stT269 242 := by
  have hc : ((48201/50000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3873094953/62500000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((48201/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c243 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((5983/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3445377/10000000) (δ := 6757/500000000) (ψ := -18323/62500) 269 235
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t243 : ((122786949/10000000000 : ℚ) : ℝ) ≤ stT269 243 := by
  have hc : ((95703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122786949/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((95703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c244 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-790781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7759/12500) (δ := 6757/500000000) (ψ := -18323/62500) 269 235
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t244 : ((-101255628747/2000000000000 : ℚ) : ℝ) ≤ stT269 244 := by
  have hc : ((-790831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101255628747/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-790831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c245 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-904119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105473/156250) (δ := 27007/1000000000) (ψ := -18323/62500) 269 236
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t245 : ((-577652778213/10000000000000 : ℚ) : ℝ) ≤ stT269 245 := by
  have hc : ((-904169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-577652778213/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-904169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c246 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-1343/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62671/156250) (δ := 13507/1000000000) (ψ := -18323/62500) 269 236
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t246 : ((-171508213/80000000000 : ℚ) : ℝ) ≤ stT269 246 := by
  have hc : ((-269/8000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171508213/80000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-269/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c247 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((217807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641373/5000000) (δ := 13507/1000000000) (ψ := -18323/62500) 269 236
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t247 : ((69289577819/1250000000000 : ℚ) : ℝ) ≤ stT269 247 := by
  have hc : ((435589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69289577819/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((435589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c248 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((839861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1434423/10000000) (δ := 13507/1000000000) (ψ := -18323/62500) 269 236
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t248 : ((106655997/2000000000 : ℚ) : ℝ) ≤ stT269 248 := by
  have hc : ((839811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106655997/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((839811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c249 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-10669/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414063/1000000) (δ := 13607/1000000000) (ψ := -18323/62500) 269 236
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t249 : ((-1082427649/200000000000 : ℚ) : ℝ) ≤ stT269 249 := by
  have hc : ((-42701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1082427649/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-42701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_c250 :
    |Real.cos (((269 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((-918249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3418039/5000000) (δ := 3399/250000000) (ψ := -18323/62500) 269 236
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st269_t250 : ((-72597964043/1250000000000 : ℚ) : ℝ) ≤ stT269 250 := by
  have hc : ((-918299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((269 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st269_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72597964043/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-918299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st269_p1 : ((957283/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT269 (i+1) := by
  rw [Finset.sum_range_one]
  exact st269_t1

theorem st269_p2 : ((208531552161/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT269 (i+1))
      = (∑ i ∈ Finset.range 1, stT269 (i+1)) + stT269 2 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 1
    simpa using h
  have hprev := st269_p1
  have hstep := st269_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p3 : ((6689664814089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT269 (i+1))
      = (∑ i ∈ Finset.range 2, stT269 (i+1)) + stT269 3 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 2
    simpa using h
  have hprev := st269_p2
  have hstep := st269_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p4 : ((4689054413967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT269 (i+1))
      = (∑ i ∈ Finset.range 3, stT269 (i+1)) + stT269 4 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 3
    simpa using h
  have hprev := st269_p3
  have hstep := st269_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p5 : ((13639825404049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT269 (i+1))
      = (∑ i ∈ Finset.range 4, stT269 (i+1)) + stT269 5 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 4
    simpa using h
  have hprev := st269_p4
  have hstep := st269_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p6 : ((13810983461899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT269 (i+1))
      = (∑ i ∈ Finset.range 5, stT269 (i+1)) + stT269 6 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 5
    simpa using h
  have hprev := st269_p5
  have hstep := st269_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p7 : ((1433768407873/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT269 (i+1))
      = (∑ i ∈ Finset.range 6, stT269 (i+1)) + stT269 7 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 6
    simpa using h
  have hprev := st269_p6
  have hstep := st269_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p8 : ((14638851036569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT269 (i+1))
      = (∑ i ∈ Finset.range 7, stT269 (i+1)) + stT269 8 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 7
    simpa using h
  have hprev := st269_p7
  have hstep := st269_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p9 : ((17128917454229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT269 (i+1))
      = (∑ i ∈ Finset.range 8, stT269 (i+1)) + stT269 9 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 8
    simpa using h
  have hprev := st269_p8
  have hstep := st269_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p10 : ((14913798636233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT269 (i+1))
      = (∑ i ∈ Finset.range 9, stT269 (i+1)) + stT269 10 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 9
    simpa using h
  have hprev := st269_p9
  have hstep := st269_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p11 : ((14108549125139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT269 (i+1))
      = (∑ i ∈ Finset.range 10, stT269 (i+1)) + stT269 11 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 10
    simpa using h
  have hprev := st269_p10
  have hstep := st269_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p12 : ((2295973396087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT269 (i+1))
      = (∑ i ∈ Finset.range 11, stT269 (i+1)) + stT269 12 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 11
    simpa using h
  have hprev := st269_p11
  have hstep := st269_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p13 : ((2646870514387/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT269 (i+1))
      = (∑ i ∈ Finset.range 12, stT269 (i+1)) + stT269 13 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 12
    simpa using h
  have hprev := st269_p12
  have hstep := st269_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p14 : ((3170747900791/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT269 (i+1))
      = (∑ i ∈ Finset.range 13, stT269 (i+1)) + stT269 14 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 13
    simpa using h
  have hprev := st269_p13
  have hstep := st269_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p15 : ((3684992122799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT269 (i+1))
      = (∑ i ∈ Finset.range 14, stT269 (i+1)) + stT269 15 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 14
    simpa using h
  have hprev := st269_p14
  have hstep := st269_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p16 : ((18403050605231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT269 (i+1))
      = (∑ i ∈ Finset.range 15, stT269 (i+1)) + stT269 16 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 15
    simpa using h
  have hprev := st269_p15
  have hstep := st269_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p17 : ((17050855869163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT269 (i+1))
      = (∑ i ∈ Finset.range 16, stT269 (i+1)) + stT269 17 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 16
    simpa using h
  have hprev := st269_p16
  have hstep := st269_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p18 : ((17654376066307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT269 (i+1))
      = (∑ i ∈ Finset.range 17, stT269 (i+1)) + stT269 18 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 17
    simpa using h
  have hprev := st269_p17
  have hstep := st269_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p19 : ((2432287692431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT269 (i+1))
      = (∑ i ∈ Finset.range 18, stT269 (i+1)) + stT269 19 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 18
    simpa using h
  have hprev := st269_p18
  have hstep := st269_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p20 : ((937037254109/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT269 (i+1))
      = (∑ i ∈ Finset.range 19, stT269 (i+1)) + stT269 20 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 19
    simpa using h
  have hprev := st269_p19
  have hstep := st269_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p21 : ((1065753843667/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT269 (i+1))
      = (∑ i ∈ Finset.range 20, stT269 (i+1)) + stT269 21 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 20
    simpa using h
  have hprev := st269_p20
  have hstep := st269_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p22 : ((967208169891/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT269 (i+1))
      = (∑ i ∈ Finset.range 21, stT269 (i+1)) + stT269 22 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 21
    simpa using h
  have hprev := st269_p21
  have hstep := st269_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p23 : ((1876634886687/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT269 (i+1))
      = (∑ i ∈ Finset.range 22, stT269 (i+1)) + stT269 23 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 22
    simpa using h
  have hprev := st269_p22
  have hstep := st269_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p24 : ((3320946944401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT269 (i+1))
      = (∑ i ∈ Finset.range 23, stT269 (i+1)) + stT269 24 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 23
    simpa using h
  have hprev := st269_p23
  have hstep := st269_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p25 : ((3566803744401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT269 (i+1))
      = (∑ i ∈ Finset.range 24, stT269 (i+1)) + stT269 25 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 24
    simpa using h
  have hprev := st269_p24
  have hstep := st269_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p26 : ((15918663582839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT269 (i+1))
      = (∑ i ∈ Finset.range 25, stT269 (i+1)) + stT269 26 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 25
    simpa using h
  have hprev := st269_p25
  have hstep := st269_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p27 : ((17047151892839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT269 (i+1))
      = (∑ i ∈ Finset.range 26, stT269 (i+1)) + stT269 27 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 26
    simpa using h
  have hprev := st269_p26
  have hstep := st269_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p28 : ((16545694919081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT269 (i+1))
      = (∑ i ∈ Finset.range 27, stT269 (i+1)) + stT269 28 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 27
    simpa using h
  have hprev := st269_p27
  have hstep := st269_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p29 : ((8505862564363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT269 (i+1))
      = (∑ i ∈ Finset.range 28, stT269 (i+1)) + stT269 29 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 28
    simpa using h
  have hprev := st269_p28
  have hstep := st269_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p30 : ((4010842000901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT269 (i+1))
      = (∑ i ∈ Finset.range 29, stT269 (i+1)) + stT269 30 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 29
    simpa using h
  have hprev := st269_p29
  have hstep := st269_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p31 : ((17692261401049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT269 (i+1))
      = (∑ i ∈ Finset.range 30, stT269 (i+1)) + stT269 31 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 30
    simpa using h
  have hprev := st269_p30
  have hstep := st269_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p32 : ((3224326448271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT269 (i+1))
      = (∑ i ∈ Finset.range 31, stT269 (i+1)) + stT269 32 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 31
    simpa using h
  have hprev := st269_p31
  have hstep := st269_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p33 : ((16028803567053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT269 (i+1))
      = (∑ i ∈ Finset.range 32, stT269 (i+1)) + stT269 33 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 32
    simpa using h
  have hprev := st269_p32
  have hstep := st269_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p34 : ((17730710091443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT269 (i+1))
      = (∑ i ∈ Finset.range 33, stT269 (i+1)) + stT269 34 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 33
    simpa using h
  have hprev := st269_p33
  have hstep := st269_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p35 : ((2202218131333/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT269 (i+1))
      = (∑ i ∈ Finset.range 34, stT269 (i+1)) + stT269 35 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 34
    simpa using h
  have hprev := st269_p34
  have hstep := st269_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p36 : ((799366236229/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT269 (i+1))
      = (∑ i ∈ Finset.range 35, stT269 (i+1)) + stT269 36 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 35
    simpa using h
  have hprev := st269_p35
  have hstep := st269_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p37 : ((59748792657/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT269 (i+1))
      = (∑ i ∈ Finset.range 36, stT269 (i+1)) + stT269 37 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 36
    simpa using h
  have hprev := st269_p36
  have hstep := st269_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p38 : ((762789644139/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT269 (i+1))
      = (∑ i ∈ Finset.range 37, stT269 (i+1)) + stT269 38 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 37
    simpa using h
  have hprev := st269_p37
  have hstep := st269_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p39 : ((16511983415751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT269 (i+1))
      = (∑ i ∈ Finset.range 38, stT269 (i+1)) + stT269 39 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 38
    simpa using h
  have hprev := st269_p38
  have hstep := st269_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p40 : ((18077230978851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT269 (i+1))
      = (∑ i ∈ Finset.range 39, stT269 (i+1)) + stT269 40 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 39
    simpa using h
  have hprev := st269_p39
  have hstep := st269_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p41 : ((9801032847639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT269 (i+1))
      = (∑ i ∈ Finset.range 40, stT269 (i+1)) + stT269 41 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 40
    simpa using h
  have hprev := st269_p40
  have hstep := st269_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p42 : ((5253252996103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT269 (i+1))
      = (∑ i ∈ Finset.range 41, stT269 (i+1)) + stT269 42 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 41
    simpa using h
  have hprev := st269_p41
  have hstep := st269_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p43 : ((22377246790577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT269 (i+1))
      = (∑ i ∈ Finset.range 42, stT269 (i+1)) + stT269 43 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 42
    simpa using h
  have hprev := st269_p42
  have hstep := st269_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p44 : ((23785864905409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT269 (i+1))
      = (∑ i ∈ Finset.range 43, stT269 (i+1)) + stT269 44 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 43
    simpa using h
  have hprev := st269_p43
  have hstep := st269_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p45 : ((25264653198831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT269 (i+1))
      = (∑ i ∈ Finset.range 44, stT269 (i+1)) + stT269 45 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 44
    simpa using h
  have hprev := st269_p44
  have hstep := st269_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p46 : ((26695075535871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT269 (i+1))
      = (∑ i ∈ Finset.range 45, stT269 (i+1)) + stT269 46 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 45
    simpa using h
  have hprev := st269_p45
  have hstep := st269_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p47 : ((27769519306569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT269 (i+1))
      = (∑ i ∈ Finset.range 46, stT269 (i+1)) + stT269 47 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 46
    simpa using h
  have hprev := st269_p46
  have hstep := st269_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p48 : ((7016978137611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT269 (i+1))
      = (∑ i ∈ Finset.range 47, stT269 (i+1)) + stT269 48 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 47
    simpa using h
  have hprev := st269_p47
  have hstep := st269_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p49 : ((6836925922733/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT269 (i+1))
      = (∑ i ∈ Finset.range 48, stT269 (i+1)) + stT269 49 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 48
    simpa using h
  have hprev := st269_p48
  have hstep := st269_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p50 : ((6489975387899/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT269 (i+1))
      = (∑ i ∈ Finset.range 49, stT269 (i+1)) + stT269 50 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 49
    simpa using h
  have hprev := st269_p49
  have hstep := st269_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p51 : ((6236807383661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT269 (i+1))
      = (∑ i ∈ Finset.range 50, stT269 (i+1)) + stT269 51 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 50
    simpa using h
  have hprev := st269_p50
  have hstep := st269_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p52 : ((12646048115947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT269 (i+1))
      = (∑ i ∈ Finset.range 51, stT269 (i+1)) + stT269 52 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 51
    simpa using h
  have hprev := st269_p51
  have hstep := st269_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p53 : ((26648043539619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT269 (i+1))
      = (∑ i ∈ Finset.range 52, stT269 (i+1)) + stT269 53 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 52
    simpa using h
  have hprev := st269_p52
  have hstep := st269_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p54 : ((13635763421037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT269 (i+1))
      = (∑ i ∈ Finset.range 53, stT269 (i+1)) + stT269 54 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 53
    simpa using h
  have hprev := st269_p53
  have hstep := st269_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p55 : ((13119858164837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT269 (i+1))
      = (∑ i ∈ Finset.range 54, stT269 (i+1)) + stT269 55 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 54
    simpa using h
  have hprev := st269_p54
  have hstep := st269_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p56 : ((5049972858283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT269 (i+1))
      = (∑ i ∈ Finset.range 55, stT269 (i+1)) + stT269 56 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 55
    simpa using h
  have hprev := st269_p55
  have hstep := st269_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p57 : ((26090764624127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT269 (i+1))
      = (∑ i ∈ Finset.range 56, stT269 (i+1)) + stT269 57 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 56
    simpa using h
  have hprev := st269_p56
  have hstep := st269_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p58 : ((27076225721447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT269 (i+1))
      = (∑ i ∈ Finset.range 57, stT269 (i+1)) + stT269 58 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 57
    simpa using h
  have hprev := st269_p57
  have hstep := st269_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p59 : ((26110296247287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT269 (i+1))
      = (∑ i ∈ Finset.range 58, stT269 (i+1)) + stT269 59 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 58
    simpa using h
  have hprev := st269_p58
  have hstep := st269_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p60 : ((397538649543/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT269 (i+1))
      = (∑ i ∈ Finset.range 59, stT269 (i+1)) + stT269 60 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 59
    simpa using h
  have hprev := st269_p59
  have hstep := st269_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p61 : ((13336876771/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT269 (i+1))
      = (∑ i ∈ Finset.range 60, stT269 (i+1)) + stT269 61 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 60
    simpa using h
  have hprev := st269_p60
  have hstep := st269_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p62 : ((3324581782573/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT269 (i+1))
      = (∑ i ∈ Finset.range 61, stT269 (i+1)) + stT269 62 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 61
    simpa using h
  have hprev := st269_p61
  have hstep := st269_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p63 : ((12736368733071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT269 (i+1))
      = (∑ i ∈ Finset.range 62, stT269 (i+1)) + stT269 63 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 62
    simpa using h
  have hprev := st269_p62
  have hstep := st269_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p64 : ((13242924983071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT269 (i+1))
      = (∑ i ∈ Finset.range 63, stT269 (i+1)) + stT269 64 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 63
    simpa using h
  have hprev := st269_p63
  have hstep := st269_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p65 : ((13294905445147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT269 (i+1))
      = (∑ i ∈ Finset.range 64, stT269 (i+1)) + stT269 65 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 64
    simpa using h
  have hprev := st269_p64
  have hstep := st269_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p66 : ((25522436488109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT269 (i+1))
      = (∑ i ∈ Finset.range 65, stT269 (i+1)) + stT269 66 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 65
    simpa using h
  have hprev := st269_p65
  have hstep := st269_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p67 : ((26655948615189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT269 (i+1))
      = (∑ i ∈ Finset.range 66, stT269 (i+1)) + stT269 67 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 66
    simpa using h
  have hprev := st269_p66
  have hstep := st269_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p68 : ((6561443320727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT269 (i+1))
      = (∑ i ∈ Finset.range 67, stT269 (i+1)) + stT269 68 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 67
    simpa using h
  have hprev := st269_p67
  have hstep := st269_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p69 : ((25732405670243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT269 (i+1))
      = (∑ i ∈ Finset.range 68, stT269 (i+1)) + stT269 69 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 68
    simpa using h
  have hprev := st269_p68
  have hstep := st269_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p70 : ((26832601091963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT269 (i+1))
      = (∑ i ∈ Finset.range 69, stT269 (i+1)) + stT269 70 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 69
    simpa using h
  have hprev := st269_p69
  have hstep := st269_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p71 : ((5137924880473/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT269 (i+1))
      = (∑ i ∈ Finset.range 70, stT269 (i+1)) + stT269 71 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 70
    simpa using h
  have hprev := st269_p70
  have hstep := st269_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p72 : ((26428168961801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT269 (i+1))
      = (∑ i ∈ Finset.range 71, stT269 (i+1)) + stT269 72 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 71
    simpa using h
  have hprev := st269_p71
  have hstep := st269_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p73 : ((26301323220477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT269 (i+1))
      = (∑ i ∈ Finset.range 72, stT269 (i+1)) + stT269 73 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 72
    simpa using h
  have hprev := st269_p72
  have hstep := st269_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p74 : ((25838131934873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT269 (i+1))
      = (∑ i ∈ Finset.range 73, stT269 (i+1)) + stT269 74 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 73
    simpa using h
  have hprev := st269_p73
  have hstep := st269_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p75 : ((26727306360473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT269 (i+1))
      = (∑ i ∈ Finset.range 74, stT269 (i+1)) + stT269 75 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 74
    simpa using h
  have hprev := st269_p74
  have hstep := st269_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p76 : ((12810930296389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT269 (i+1))
      = (∑ i ∈ Finset.range 75, stT269 (i+1)) + stT269 76 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 75
    simpa using h
  have hprev := st269_p75
  have hstep := st269_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p77 : ((26755208021723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT269 (i+1))
      = (∑ i ∈ Finset.range 76, stT269 (i+1)) + stT269 77 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 76
    simpa using h
  have hprev := st269_p76
  have hstep := st269_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p78 : ((25727744996183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT269 (i+1))
      = (∑ i ∈ Finset.range 77, stT269 (i+1)) + stT269 78 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 77
    simpa using h
  have hprev := st269_p77
  have hstep := st269_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p79 : ((1660892895749/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT269 (i+1))
      = (∑ i ∈ Finset.range 78, stT269 (i+1)) + stT269 79 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 78
    simpa using h
  have hprev := st269_p78
  have hstep := st269_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p80 : ((12967008105517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT269 (i+1))
      = (∑ i ∈ Finset.range 79, stT269 (i+1)) + stT269 80 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 79
    simpa using h
  have hprev := st269_p79
  have hstep := st269_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p81 : ((26376497277897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT269 (i+1))
      = (∑ i ∈ Finset.range 80, stT269 (i+1)) + stT269 81 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 80
    simpa using h
  have hprev := st269_p80
  have hstep := st269_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p82 : ((26102609240841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT269 (i+1))
      = (∑ i ∈ Finset.range 81, stT269 (i+1)) + stT269 82 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 81
    simpa using h
  have hprev := st269_p81
  have hstep := st269_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p83 : ((26246496935337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT269 (i+1))
      = (∑ i ∈ Finset.range 82, stT269 (i+1)) + stT269 83 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 82
    simpa using h
  have hprev := st269_p82
  have hstep := st269_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p84 : ((26190249063657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT269 (i+1))
      = (∑ i ∈ Finset.range 83, stT269 (i+1)) + stT269 84 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 83
    simpa using h
  have hprev := st269_p83
  have hstep := st269_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p85 : ((26200661722857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT269 (i+1))
      = (∑ i ∈ Finset.range 84, stT269 (i+1)) + stT269 85 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 84
    simpa using h
  have hprev := st269_p84
  have hstep := st269_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p86 : ((1047807827129/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT269 (i+1))
      = (∑ i ∈ Finset.range 85, stT269 (i+1)) + stT269 86 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 85
    simpa using h
  have hprev := st269_p85
  have hstep := st269_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p87 : ((26234511097377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT269 (i+1))
      = (∑ i ∈ Finset.range 86, stT269 (i+1)) + stT269 87 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 86
    simpa using h
  have hprev := st269_p86
  have hstep := st269_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p88 : ((26123790591917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT269 (i+1))
      = (∑ i ∈ Finset.range 87, stT269 (i+1)) + stT269 88 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 87
    simpa using h
  have hprev := st269_p87
  have hstep := st269_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p89 : ((13170293239171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT269 (i+1))
      = (∑ i ∈ Finset.range 88, stT269 (i+1)) + stT269 89 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 88
    simpa using h
  have hprev := st269_p88
  have hstep := st269_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p90 : ((6496754069931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT269 (i+1))
      = (∑ i ∈ Finset.range 89, stT269 (i+1)) + stT269 90 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 89
    simpa using h
  have hprev := st269_p89
  have hstep := st269_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p91 : ((828118688313/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT269 (i+1))
      = (∑ i ∈ Finset.range 90, stT269 (i+1)) + stT269 91 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 90
    simpa using h
  have hprev := st269_p90
  have hstep := st269_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p92 : ((12908949492537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT269 (i+1))
      = (∑ i ∈ Finset.range 91, stT269 (i+1)) + stT269 92 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 91
    simpa using h
  have hprev := st269_p91
  have hstep := st269_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p93 : ((26659097486147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT269 (i+1))
      = (∑ i ∈ Finset.range 92, stT269 (i+1)) + stT269 93 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 92
    simpa using h
  have hprev := st269_p92
  have hstep := st269_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p94 : ((25693710216853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT269 (i+1))
      = (∑ i ∈ Finset.range 93, stT269 (i+1)) + stT269 94 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 93
    simpa using h
  have hprev := st269_p93
  have hstep := st269_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p95 : ((5343495241657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT269 (i+1))
      = (∑ i ∈ Finset.range 94, stT269 (i+1)) + stT269 95 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 94
    simpa using h
  have hprev := st269_p94
  have hstep := st269_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p96 : ((25731082754141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT269 (i+1))
      = (∑ i ∈ Finset.range 95, stT269 (i+1)) + stT269 96 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 95
    simpa using h
  have hprev := st269_p95
  have hstep := st269_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p97 : ((212487838949/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT269 (i+1))
      = (∑ i ∈ Finset.range 96, stT269 (i+1)) + stT269 97 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 96
    simpa using h
  have hprev := st269_p96
  have hstep := st269_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p98 : ((26012169804643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT269 (i+1))
      = (∑ i ∈ Finset.range 97, stT269 (i+1)) + stT269 98 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 97
    simpa using h
  have hprev := st269_p97
  have hstep := st269_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p99 : ((26175908422609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT269 (i+1))
      = (∑ i ∈ Finset.range 98, stT269 (i+1)) + stT269 99 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 98
    simpa using h
  have hprev := st269_p98
  have hstep := st269_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p100 : ((1057871686069/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT269 (i+1))
      = (∑ i ∈ Finset.range 99, stT269 (i+1)) + stT269 100 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 99
    simpa using h
  have hprev := st269_p99
  have hstep := st269_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p101 : ((5155263129313/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT269 (i+1))
      = (∑ i ∈ Finset.range 100, stT269 (i+1)) + stT269 101 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 100
    simpa using h
  have hprev := st269_p100
  have hstep := st269_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p102 : ((13354837372837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT269 (i+1))
      = (∑ i ∈ Finset.range 101, stT269 (i+1)) + stT269 102 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 101
    simpa using h
  have hprev := st269_p101
  have hstep := st269_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p103 : ((1608730950109/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT269 (i+1))
      = (∑ i ∈ Finset.range 102, stT269 (i+1)) + stT269 103 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 102
    simpa using h
  have hprev := st269_p102
  have hstep := st269_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p104 : ((6619282401091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT269 (i+1))
      = (∑ i ∈ Finset.range 103, stT269 (i+1)) + stT269 104 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 103
    simpa using h
  have hprev := st269_p103
  have hstep := st269_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p105 : ((655094883717/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT269 (i+1))
      = (∑ i ∈ Finset.range 104, stT269 (i+1)) + stT269 105 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 104
    simpa using h
  have hprev := st269_p104
  have hstep := st269_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p106 : ((809665791207/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT269 (i+1))
      = (∑ i ∈ Finset.range 105, stT269 (i+1)) + stT269 106 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 105
    simpa using h
  have hprev := st269_p105
  have hstep := st269_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p107 : ((1667535758319/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT269 (i+1))
      = (∑ i ∈ Finset.range 106, stT269 (i+1)) + stT269 107 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 106
    simpa using h
  have hprev := st269_p106
  have hstep := st269_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p108 : ((5143660570067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT269 (i+1))
      = (∑ i ∈ Finset.range 107, stT269 (i+1)) + stT269 108 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 107
    simpa using h
  have hprev := st269_p107
  have hstep := st269_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p109 : ((26478144300483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT269 (i+1))
      = (∑ i ∈ Finset.range 108, stT269 (i+1)) + stT269 109 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 108
    simpa using h
  have hprev := st269_p108
  have hstep := st269_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p110 : ((2625948567723/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT269 (i+1))
      = (∑ i ∈ Finset.range 109, stT269 (i+1)) + stT269 110 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 109
    simpa using h
  have hprev := st269_p109
  have hstep := st269_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p111 : ((6456162692541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT269 (i+1))
      = (∑ i ∈ Finset.range 110, stT269 (i+1)) + stT269 111 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 110
    simpa using h
  have hprev := st269_p110
  have hstep := st269_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p112 : ((26706954802037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT269 (i+1))
      = (∑ i ∈ Finset.range 111, stT269 (i+1)) + stT269 112 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 111
    simpa using h
  have hprev := st269_p111
  have hstep := st269_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p113 : ((2583488103557/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT269 (i+1))
      = (∑ i ∈ Finset.range 112, stT269 (i+1)) + stT269 113 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 112
    simpa using h
  have hprev := st269_p112
  have hstep := st269_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p114 : ((1048488983039/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT269 (i+1))
      = (∑ i ∈ Finset.range 113, stT269 (i+1)) + stT269 114 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 113
    simpa using h
  have hprev := st269_p113
  have hstep := st269_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p115 : ((5311178852531/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT269 (i+1))
      = (∑ i ∈ Finset.range 114, stT269 (i+1)) + stT269 115 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 114
    simpa using h
  have hprev := st269_p114
  have hstep := st269_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p116 : ((25693847935051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT269 (i+1))
      = (∑ i ∈ Finset.range 115, stT269 (i+1)) + stT269 116 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 115
    simpa using h
  have hprev := st269_p115
  have hstep := st269_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p117 : ((26525522588051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT269 (i+1))
      = (∑ i ∈ Finset.range 116, stT269 (i+1)) + stT269 117 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 116
    simpa using h
  have hprev := st269_p116
  have hstep := st269_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p118 : ((26282824036201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT269 (i+1))
      = (∑ i ∈ Finset.range 117, stT269 (i+1)) + stT269 118 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 117
    simpa using h
  have hprev := st269_p117
  have hstep := st269_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p119 : ((25761533982861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT269 (i+1))
      = (∑ i ∈ Finset.range 118, stT269 (i+1)) + stT269 119 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 118
    simpa using h
  have hprev := st269_p118
  have hstep := st269_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p120 : ((26671760311341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT269 (i+1))
      = (∑ i ∈ Finset.range 119, stT269 (i+1)) + stT269 120 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 119
    simpa using h
  have hprev := st269_p119
  have hstep := st269_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p121 : ((26060714795691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT269 (i+1))
      = (∑ i ∈ Finset.range 120, stT269 (i+1)) + stT269 121 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 120
    simpa using h
  have hprev := st269_p120
  have hstep := st269_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p122 : ((25889198344023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT269 (i+1))
      = (∑ i ∈ Finset.range 121, stT269 (i+1)) + stT269 122 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 121
    simpa using h
  have hprev := st269_p121
  have hstep := st269_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p123 : ((13353503809339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT269 (i+1))
      = (∑ i ∈ Finset.range 122, stT269 (i+1)) + stT269 123 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 122
    simpa using h
  have hprev := st269_p122
  have hstep := st269_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p124 : ((12965811185007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT269 (i+1))
      = (∑ i ∈ Finset.range 123, stT269 (i+1)) + stT269 124 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 123
    simpa using h
  have hprev := st269_p123
  have hstep := st269_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p125 : ((12993053642573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT269 (i+1))
      = (∑ i ∈ Finset.range 124, stT269 (i+1)) + stT269 125 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 124
    simpa using h
  have hprev := st269_p124
  have hstep := st269_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p126 : ((6675996814419/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT269 (i+1))
      = (∑ i ∈ Finset.range 125, stT269 (i+1)) + stT269 126 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 125
    simpa using h
  have hprev := st269_p125
  have hstep := st269_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p127 : ((12940184555493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT269 (i+1))
      = (∑ i ∈ Finset.range 126, stT269 (i+1)) + stT269 127 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 126
    simpa using h
  have hprev := st269_p126
  have hstep := st269_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p128 : ((13009505731417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT269 (i+1))
      = (∑ i ∈ Finset.range 127, stT269 (i+1)) + stT269 128 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 127
    simpa using h
  have hprev := st269_p127
  have hstep := st269_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p129 : ((13351742809567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT269 (i+1))
      = (∑ i ∈ Finset.range 128, stT269 (i+1)) + stT269 129 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 128
    simpa using h
  have hprev := st269_p128
  have hstep := st269_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p130 : ((12945161060701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT269 (i+1))
      = (∑ i ∈ Finset.range 129, stT269 (i+1)) + stT269 130 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 129
    simpa using h
  have hprev := st269_p129
  have hstep := st269_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p131 : ((2598299765209/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT269 (i+1))
      = (∑ i ∈ Finset.range 130, stT269 (i+1)) + stT269 131 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 130
    simpa using h
  have hprev := st269_p130
  have hstep := st269_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p132 : ((2671044618279/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT269 (i+1))
      = (∑ i ∈ Finset.range 131, stT269 (i+1)) + stT269 132 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 131
    simpa using h
  have hprev := st269_p131
  have hstep := st269_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p133 : ((51924713137/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT269 (i+1))
      = (∑ i ∈ Finset.range 132, stT269 (i+1)) + stT269 133 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 132
    simpa using h
  have hprev := st269_p132
  have hstep := st269_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p134 : ((809002318779/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT269 (i+1))
      = (∑ i ∈ Finset.range 133, stT269 (i+1)) + stT269 134 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 133
    simpa using h
  have hprev := st269_p133
  have hstep := st269_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p135 : ((1334925656529/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT269 (i+1))
      = (∑ i ∈ Finset.range 134, stT269 (i+1)) + stT269 135 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 134
    simpa using h
  have hprev := st269_p134
  have hstep := st269_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p136 : ((13054605678123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT269 (i+1))
      = (∑ i ∈ Finset.range 135, stT269 (i+1)) + stT269 136 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 135
    simpa using h
  have hprev := st269_p135
  have hstep := st269_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p137 : ((1288303051431/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT269 (i+1))
      = (∑ i ∈ Finset.range 136, stT269 (i+1)) + stT269 137 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 136
    simpa using h
  have hprev := st269_p136
  have hstep := st269_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p138 : ((6654236895879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT269 (i+1))
      = (∑ i ∈ Finset.range 137, stT269 (i+1)) + stT269 138 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 137
    simpa using h
  have hprev := st269_p137
  have hstep := st269_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p139 : ((329137958033/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT269 (i+1))
      = (∑ i ∈ Finset.range 138, stT269 (i+1)) + stT269 139 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 138
    simpa using h
  have hprev := st269_p138
  have hstep := st269_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p140 : ((513705784073/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT269 (i+1))
      = (∑ i ∈ Finset.range 139, stT269 (i+1)) + stT269 140 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 139
    simpa using h
  have hprev := st269_p139
  have hstep := st269_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p141 : ((103178427319/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT269 (i+1))
      = (∑ i ∈ Finset.range 140, stT269 (i+1)) + stT269 141 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 140
    simpa using h
  have hprev := st269_p140
  have hstep := st269_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p142 : ((26576600188909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT269 (i+1))
      = (∑ i ∈ Finset.range 141, stT269 (i+1)) + stT269 142 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 141
    simpa using h
  have hprev := st269_p141
  have hstep := st269_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p143 : ((5149296032031/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT269 (i+1))
      = (∑ i ∈ Finset.range 142, stT269 (i+1)) + stT269 143 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 142
    simpa using h
  have hprev := st269_p142
  have hstep := st269_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p144 : ((26090235022653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT269 (i+1))
      = (∑ i ∈ Finset.range 143, stT269 (i+1)) + stT269 144 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 143
    simpa using h
  have hprev := st269_p143
  have hstep := st269_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p145 : ((26716677201651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT269 (i+1))
      = (∑ i ∈ Finset.range 144, stT269 (i+1)) + stT269 145 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 144
    simpa using h
  have hprev := st269_p144
  have hstep := st269_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p146 : ((26022884332973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT269 (i+1))
      = (∑ i ∈ Finset.range 145, stT269 (i+1)) + stT269 146 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 145
    simpa using h
  have hprev := st269_p145
  have hstep := st269_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p147 : ((25770186091913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT269 (i+1))
      = (∑ i ∈ Finset.range 146, stT269 (i+1)) + stT269 147 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 146
    simpa using h
  have hprev := st269_p146
  have hstep := st269_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p148 : ((26590738314437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT269 (i+1))
      = (∑ i ∈ Finset.range 147, stT269 (i+1)) + stT269 148 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 147
    simpa using h
  have hprev := st269_p147
  have hstep := st269_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p149 : ((5288438050561/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT269 (i+1))
      = (∑ i ∈ Finset.range 148, stT269 (i+1)) + stT269 149 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 148
    simpa using h
  have hprev := st269_p148
  have hstep := st269_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p150 : ((12846792080929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT269 (i+1))
      = (∑ i ∈ Finset.range 149, stT269 (i+1)) + stT269 150 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 149
    simpa using h
  have hprev := st269_p149
  have hstep := st269_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p151 : ((2617127283513/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT269 (i+1))
      = (∑ i ∈ Finset.range 150, stT269 (i+1)) + stT269 151 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 150
    simpa using h
  have hprev := st269_p150
  have hstep := st269_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p152 : ((5343462824613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT269 (i+1))
      = (∑ i ∈ Finset.range 151, stT269 (i+1)) + stT269 152 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 151
    simpa using h
  have hprev := st269_p151
  have hstep := st269_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p153 : ((5205227063049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT269 (i+1))
      = (∑ i ∈ Finset.range 152, stT269 (i+1)) + stT269 153 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 152
    simpa using h
  have hprev := st269_p152
  have hstep := st269_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p154 : ((12869680721737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT269 (i+1))
      = (∑ i ∈ Finset.range 153, stT269 (i+1)) + stT269 154 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 153
    simpa using h
  have hprev := st269_p153
  have hstep := st269_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p155 : ((5305510282553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT269 (i+1))
      = (∑ i ∈ Finset.range 154, stT269 (i+1)) + stT269 155 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 154
    simpa using h
  have hprev := st269_p154
  have hstep := st269_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p156 : ((5311005875513/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT269 (i+1))
      = (∑ i ∈ Finset.range 155, stT269 (i+1)) + stT269 156 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 155
    simpa using h
  have hprev := st269_p155
  have hstep := st269_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p157 : ((4025320957/1562500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT269 (i+1))
      = (∑ i ∈ Finset.range 156, stT269 (i+1)) + stT269 157 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 156
    simpa using h
  have hprev := st269_p156
  have hstep := st269_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p158 : ((25959470798793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT269 (i+1))
      = (∑ i ∈ Finset.range 157, stT269 (i+1)) + stT269 158 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 157
    simpa using h
  have hprev := st269_p157
  have hstep := st269_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p159 : ((26696730660943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT269 (i+1))
      = (∑ i ∈ Finset.range 158, stT269 (i+1)) + stT269 159 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 158
    simpa using h
  have hprev := st269_p158
  have hstep := st269_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p160 : ((26322589455593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT269 (i+1))
      = (∑ i ∈ Finset.range 159, stT269 (i+1)) + stT269 160 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 159
    simpa using h
  have hprev := st269_p159
  have hstep := st269_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p161 : ((1026850583079/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT269 (i+1))
      = (∑ i ∈ Finset.range 160, stT269 (i+1)) + stT269 161 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 160
    simpa using h
  have hprev := st269_p160
  have hstep := st269_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p162 : ((26173142914413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT269 (i+1))
      = (∑ i ∈ Finset.range 161, stT269 (i+1)) + stT269 162 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 161
    simpa using h
  have hprev := st269_p161
  have hstep := st269_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p163 : ((26731260310233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT269 (i+1))
      = (∑ i ∈ Finset.range 162, stT269 (i+1)) + stT269 163 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 162
    simpa using h
  have hprev := st269_p162
  have hstep := st269_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p164 : ((1045740570783/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT269 (i+1))
      = (∑ i ∈ Finset.range 163, stT269 (i+1)) + stT269 164 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 163
    simpa using h
  have hprev := st269_p163
  have hstep := st269_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p165 : ((25669682410223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT269 (i+1))
      = (∑ i ∈ Finset.range 164, stT269 (i+1)) + stT269 165 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 164
    simpa using h
  have hprev := st269_p164
  have hstep := st269_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p166 : ((26310355427723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT269 (i+1))
      = (∑ i ∈ Finset.range 165, stT269 (i+1)) + stT269 166 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 165
    simpa using h
  have hprev := st269_p165
  have hstep := st269_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p167 : ((333974864173/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT269 (i+1))
      = (∑ i ∈ Finset.range 166, stT269 (i+1)) + stT269 167 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 166
    simpa using h
  have hprev := st269_p166
  have hstep := st269_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p168 : ((814009376049/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT269 (i+1))
      = (∑ i ∈ Finset.range 167, stT269 (i+1)) + stT269 168 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 167
    simpa using h
  have hprev := st269_p167
  have hstep := st269_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p169 : ((6420875750263/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT269 (i+1))
      = (∑ i ∈ Finset.range 168, stT269 (i+1)) + stT269 169 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 168
    simpa using h
  have hprev := st269_p168
  have hstep := st269_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p170 : ((3295566181477/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT269 (i+1))
      = (∑ i ∈ Finset.range 169, stT269 (i+1)) + stT269 170 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 169
    simpa using h
  have hprev := st269_p169
  have hstep := st269_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p171 : ((834732393093/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT269 (i+1))
      = (∑ i ∈ Finset.range 170, stT269 (i+1)) + stT269 171 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 170
    simpa using h
  have hprev := st269_p170
  have hstep := st269_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p172 : ((26032687422673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT269 (i+1))
      = (∑ i ∈ Finset.range 171, stT269 (i+1)) + stT269 172 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 171
    simpa using h
  have hprev := st269_p171
  have hstep := st269_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p173 : ((25678492223567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT269 (i+1))
      = (∑ i ∈ Finset.range 172, stT269 (i+1)) + stT269 173 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 172
    simpa using h
  have hprev := st269_p172
  have hstep := st269_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p174 : ((26341950785443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT269 (i+1))
      = (∑ i ∈ Finset.range 173, stT269 (i+1)) + stT269 174 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 173
    simpa using h
  have hprev := st269_p173
  have hstep := st269_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p175 : ((1069070811859/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT269 (i+1))
      = (∑ i ∈ Finset.range 174, stT269 (i+1)) + stT269 175 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 174
    simpa using h
  have hprev := st269_p174
  have hstep := st269_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p176 : ((26093020049319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT269 (i+1))
      = (∑ i ∈ Finset.range 175, stT269 (i+1)) + stT269 176 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 175
    simpa using h
  have hprev := st269_p175
  have hstep := st269_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p177 : ((5131385597913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT269 (i+1))
      = (∑ i ∈ Finset.range 176, stT269 (i+1)) + stT269 177 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 176
    simpa using h
  have hprev := st269_p176
  have hstep := st269_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p178 : ((1049697265021/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT269 (i+1))
      = (∑ i ∈ Finset.range 177, stT269 (i+1)) + stT269 178 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 177
    simpa using h
  have hprev := st269_p177
  have hstep := st269_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p179 : ((2674526029999/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT269 (i+1))
      = (∑ i ∈ Finset.range 178, stT269 (i+1)) + stT269 179 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 178
    simpa using h
  have hprev := st269_p178
  have hstep := st269_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p180 : ((2623139323969/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT269 (i+1))
      = (∑ i ∈ Finset.range 179, stT269 (i+1)) + stT269 180 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 179
    simpa using h
  have hprev := st269_p179
  have hstep := st269_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p181 : ((5130691369691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT269 (i+1))
      = (∑ i ∈ Finset.range 180, stT269 (i+1)) + stT269 181 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 180
    simpa using h
  have hprev := st269_p180
  have hstep := st269_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p182 : ((26066701683457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT269 (i+1))
      = (∑ i ∈ Finset.range 181, stT269 (i+1)) + stT269 182 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 181
    simpa using h
  have hprev := st269_p181
  have hstep := st269_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p183 : ((26717290085557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT269 (i+1))
      = (∑ i ∈ Finset.range 182, stT269 (i+1)) + stT269 183 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 182
    simpa using h
  have hprev := st269_p182
  have hstep := st269_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p184 : ((26437134804147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT269 (i+1))
      = (∑ i ∈ Finset.range 183, stT269 (i+1)) + stT269 184 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 183
    simpa using h
  have hprev := st269_p183
  have hstep := st269_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p185 : ((6432476073173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT269 (i+1))
      = (∑ i ∈ Finset.range 184, stT269 (i+1)) + stT269 185 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 184
    simpa using h
  have hprev := st269_p184
  have hstep := st269_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p186 : ((25844009590157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT269 (i+1))
      = (∑ i ∈ Finset.range 185, stT269 (i+1)) + stT269 186 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 185
    simpa using h
  have hprev := st269_p185
  have hstep := st269_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p187 : ((26574960561749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT269 (i+1))
      = (∑ i ∈ Finset.range 186, stT269 (i+1)) + stT269 187 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 186
    simpa using h
  have hprev := st269_p186
  have hstep := st269_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p188 : ((26653720989833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT269 (i+1))
      = (∑ i ∈ Finset.range 187, stT269 (i+1)) + stT269 188 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 187
    simpa using h
  have hprev := st269_p187
  have hstep := st269_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p189 : ((2594926196373/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT269 (i+1))
      = (∑ i ∈ Finset.range 188, stT269 (i+1)) + stT269 189 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 188
    simpa using h
  have hprev := st269_p188
  have hstep := st269_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p190 : ((25664534731017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT269 (i+1))
      = (∑ i ∈ Finset.range 189, stT269 (i+1)) + stT269 190 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 189
    simpa using h
  have hprev := st269_p189
  have hstep := st269_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p191 : ((26276792659709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT269 (i+1))
      = (∑ i ∈ Finset.range 190, stT269 (i+1)) + stT269 191 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 190
    simpa using h
  have hprev := st269_p190
  have hstep := st269_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p192 : ((2675699092083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT269 (i+1))
      = (∑ i ∈ Finset.range 191, stT269 (i+1)) + stT269 192 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 191
    simpa using h
  have hprev := st269_p191
  have hstep := st269_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p193 : ((13155169307243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT269 (i+1))
      = (∑ i ∈ Finset.range 192, stT269 (i+1)) + stT269 193 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 192
    simpa using h
  have hprev := st269_p192
  have hstep := st269_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p194 : ((25676393022789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT269 (i+1))
      = (∑ i ∈ Finset.range 193, stT269 (i+1)) + stT269 194 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 193
    simpa using h
  have hprev := st269_p193
  have hstep := st269_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p195 : ((25888642767363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT269 (i+1))
      = (∑ i ∈ Finset.range 194, stT269 (i+1)) + stT269 195 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 194
    simpa using h
  have hprev := st269_p194
  have hstep := st269_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p196 : ((26598873485703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT269 (i+1))
      = (∑ i ∈ Finset.range 195, stT269 (i+1)) + stT269 196 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 195
    simpa using h
  have hprev := st269_p195
  have hstep := st269_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p197 : ((26666916508113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT269 (i+1))
      = (∑ i ∈ Finset.range 196, stT269 (i+1)) + stT269 197 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 196
    simpa using h
  have hprev := st269_p196
  have hstep := st269_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p198 : ((25988896819923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT269 (i+1))
      = (∑ i ∈ Finset.range 197, stT269 (i+1)) + stT269 198 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 197
    simpa using h
  have hprev := st269_p197
  have hstep := st269_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p199 : ((25636573250457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT269 (i+1))
      = (∑ i ∈ Finset.range 198, stT269 (i+1)) + stT269 199 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 198
    simpa using h
  have hprev := st269_p198
  have hstep := st269_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p200 : ((26157506018823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT269 (i+1))
      = (∑ i ∈ Finset.range 199, stT269 (i+1)) + stT269 200 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 199
    simpa using h
  have hprev := st269_p199
  have hstep := st269_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p201 : ((26739961580853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT269 (i+1))
      = (∑ i ∈ Finset.range 200, stT269 (i+1)) + stT269 201 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 200
    simpa using h
  have hprev := st269_p200
  have hstep := st269_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p202 : ((26489892297683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT269 (i+1))
      = (∑ i ∈ Finset.range 201, stT269 (i+1)) + stT269 202 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 201
    simpa using h
  have hprev := st269_p201
  have hstep := st269_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p203 : ((3224139813287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT269 (i+1))
      = (∑ i ∈ Finset.range 202, stT269 (i+1)) + stT269 203 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 202
    simpa using h
  have hprev := st269_p202
  have hstep := st269_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p204 : ((1606481031111/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT269 (i+1))
      = (∑ i ∈ Finset.range 203, stT269 (i+1)) + stT269 204 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 203
    simpa using h
  have hprev := st269_p203
  have hstep := st269_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p205 : ((6587845691139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT269 (i+1))
      = (∑ i ∈ Finset.range 204, stT269 (i+1)) + stT269 205 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 204
    simpa using h
  have hprev := st269_p204
  have hstep := st269_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p206 : ((5354066081531/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT269 (i+1))
      = (∑ i ∈ Finset.range 205, stT269 (i+1)) + stT269 206 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 205
    simpa using h
  have hprev := st269_p205
  have hstep := st269_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p207 : ((26345542870717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT269 (i+1))
      = (∑ i ∈ Finset.range 206, stT269 (i+1)) + stT269 207 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 206
    simpa using h
  have hprev := st269_p206
  have hstep := st269_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p208 : ((25702384627517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT269 (i+1))
      = (∑ i ∈ Finset.range 207, stT269 (i+1)) + stT269 208 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 207
    simpa using h
  have hprev := st269_p207
  have hstep := st269_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p209 : ((25773086790599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT269 (i+1))
      = (∑ i ∈ Finset.range 208, stT269 (i+1)) + stT269 209 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 208
    simpa using h
  have hprev := st269_p208
  have hstep := st269_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p210 : ((26451426206119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT269 (i+1))
      = (∑ i ∈ Finset.range 209, stT269 (i+1)) + stT269 210 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 209
    simpa using h
  have hprev := st269_p209
  have hstep := st269_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p211 : ((26767595714683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT269 (i+1))
      = (∑ i ∈ Finset.range 210, stT269 (i+1)) + stT269 211 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 210
    simpa using h
  have hprev := st269_p210
  have hstep := st269_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p212 : ((26277451885703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT269 (i+1))
      = (∑ i ∈ Finset.range 211, stT269 (i+1)) + stT269 212 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 211
    simpa using h
  have hprev := st269_p211
  have hstep := st269_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p213 : ((6418191264031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT269 (i+1))
      = (∑ i ∈ Finset.range 212, stT269 (i+1)) + stT269 213 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 212
    simpa using h
  have hprev := st269_p212
  have hstep := st269_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p214 : ((12897186730227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT269 (i+1))
      = (∑ i ∈ Finset.range 213, stT269 (i+1)) + stT269 214 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 213
    simpa using h
  have hprev := st269_p213
  have hstep := st269_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p215 : ((13234933346823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT269 (i+1))
      = (∑ i ∈ Finset.range 214, stT269 (i+1)) + stT269 215 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 214
    simpa using h
  have hprev := st269_p214
  have hstep := st269_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p216 : ((535442231831/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT269 (i+1))
      = (∑ i ∈ Finset.range 215, stT269 (i+1)) + stT269 216 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 215
    simpa using h
  have hprev := st269_p215
  have hstep := st269_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p217 : ((2629362905099/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT269 (i+1))
      = (∑ i ∈ Finset.range 216, stT269 (i+1)) + stT269 217 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 216
    simpa using h
  have hprev := st269_p216
  have hstep := st269_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p218 : ((12841591525879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT269 (i+1))
      = (∑ i ∈ Finset.range 217, stT269 (i+1)) + stT269 218 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 217
    simpa using h
  have hprev := st269_p217
  have hstep := st269_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p219 : ((25756295767947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT269 (i+1))
      = (∑ i ∈ Finset.range 218, stT269 (i+1)) + stT269 219 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 218
    simpa using h
  have hprev := st269_p218
  have hstep := st269_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p220 : ((2641164214131/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT269 (i+1))
      = (∑ i ∈ Finset.range 219, stT269 (i+1)) + stT269 220 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 219
    simpa using h
  have hprev := st269_p219
  have hstep := st269_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p221 : ((13392272631951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT269 (i+1))
      = (∑ i ∈ Finset.range 220, stT269 (i+1)) + stT269 221 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 220
    simpa using h
  have hprev := st269_p220
  have hstep := st269_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p222 : ((13195427653107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT269 (i+1))
      = (∑ i ∈ Finset.range 221, stT269 (i+1)) + stT269 222 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 221
    simpa using h
  have hprev := st269_p221
  have hstep := st269_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p223 : ((12872271304357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT269 (i+1))
      = (∑ i ∈ Finset.range 222, stT269 (i+1)) + stT269 223 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 222
    simpa using h
  have hprev := st269_p222
  have hstep := st269_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p224 : ((12838158033733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT269 (i+1))
      = (∑ i ∈ Finset.range 223, stT269 (i+1)) + stT269 224 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 223
    simpa using h
  have hprev := st269_p223
  have hstep := st269_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p225 : ((6567301035311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT269 (i+1))
      = (∑ i ∈ Finset.range 224, stT269 (i+1)) + stT269 225 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 224
    simpa using h
  have hprev := st269_p224
  have hstep := st269_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p226 : ((13385050429357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT269 (i+1))
      = (∑ i ∈ Finset.range 225, stT269 (i+1)) + stT269 226 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 225
    simpa using h
  have hprev := st269_p225
  have hstep := st269_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p227 : ((2655189097413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT269 (i+1))
      = (∑ i ∈ Finset.range 226, stT269 (i+1)) + stT269 227 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 226
    simpa using h
  have hprev := st269_p226
  have hstep := st269_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p228 : ((25890535915789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT269 (i+1))
      = (∑ i ∈ Finset.range 227, stT269 (i+1)) + stT269 228 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 227
    simpa using h
  have hprev := st269_p227
  have hstep := st269_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p229 : ((3200608395773/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT269 (i+1))
      = (∑ i ∈ Finset.range 228, stT269 (i+1)) + stT269 229 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 228
    simpa using h
  have hprev := st269_p228
  have hstep := st269_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p230 : ((6510539522871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT269 (i+1))
      = (∑ i ∈ Finset.range 229, stT269 (i+1)) + stT269 230 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 229
    simpa using h
  have hprev := st269_p229
  have hstep := st269_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p231 : ((26666392392489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT269 (i+1))
      = (∑ i ∈ Finset.range 230, stT269 (i+1)) + stT269 231 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 230
    simpa using h
  have hprev := st269_p230
  have hstep := st269_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p232 : ((26723705009961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT269 (i+1))
      = (∑ i ∈ Finset.range 231, stT269 (i+1)) + stT269 232 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 231
    simpa using h
  have hprev := st269_p231
  have hstep := st269_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p233 : ((26149144017423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT269 (i+1))
      = (∑ i ∈ Finset.range 232, stT269 (i+1)) + stT269 233 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 232
    simpa using h
  have hprev := st269_p232
  have hstep := st269_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p234 : ((12814503163863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT269 (i+1))
      = (∑ i ∈ Finset.range 233, stT269 (i+1)) + stT269 234 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 233
    simpa using h
  have hprev := st269_p233
  have hstep := st269_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p235 : ((2577585710243/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT269 (i+1))
      = (∑ i ∈ Finset.range 234, stT269 (i+1)) + stT269 235 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 234
    simpa using h
  have hprev := st269_p234
  have hstep := st269_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p236 : ((13206803884719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT269 (i+1))
      = (∑ i ∈ Finset.range 235, stT269 (i+1)) + stT269 236 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 235
    simpa using h
  have hprev := st269_p235
  have hstep := st269_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p237 : ((6699696324411/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT269 (i+1))
      = (∑ i ∈ Finset.range 236, stT269 (i+1)) + stT269 237 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 236
    simpa using h
  have hprev := st269_p236
  have hstep := st269_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p238 : ((1324461579411/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT269 (i+1))
      = (∑ i ∈ Finset.range 237, stT269 (i+1)) + stT269 238 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 237
    simpa using h
  have hprev := st269_p237
  have hstep := st269_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p239 : ((25843327044299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT269 (i+1))
      = (∑ i ∈ Finset.range 238, stT269 (i+1)) + stT269 239 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 238
    simpa using h
  have hprev := st269_p238
  have hstep := st269_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p240 : ((25596269785277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT269 (i+1))
      = (∑ i ∈ Finset.range 239, stT269 (i+1)) + stT269 240 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 239
    simpa using h
  have hprev := st269_p239
  have hstep := st269_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p241 : ((26023784527669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT269 (i+1))
      = (∑ i ∈ Finset.range 240, stT269 (i+1)) + stT269 241 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 240
    simpa using h
  have hprev := st269_p240
  have hstep := st269_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p242 : ((26643479720149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT269 (i+1))
      = (∑ i ∈ Finset.range 241, stT269 (i+1)) + stT269 242 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 241
    simpa using h
  have hprev := st269_p241
  have hstep := st269_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p243 : ((26766266669149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT269 (i+1))
      = (∑ i ∈ Finset.range 242, stT269 (i+1)) + stT269 243 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 242
    simpa using h
  have hprev := st269_p242
  have hstep := st269_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p244 : ((13129994262707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT269 (i+1))
      = (∑ i ∈ Finset.range 243, stT269 (i+1)) + stT269 244 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 243
    simpa using h
  have hprev := st269_p243
  have hstep := st269_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p245 : ((25682335747201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT269 (i+1))
      = (∑ i ∈ Finset.range 244, stT269 (i+1)) + stT269 245 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 244
    simpa using h
  have hprev := st269_p244
  have hstep := st269_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p246 : ((801903038143/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT269 (i+1))
      = (∑ i ∈ Finset.range 245, stT269 (i+1)) + stT269 246 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 245
    simpa using h
  have hprev := st269_p245
  have hstep := st269_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p247 : ((3276901730391/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT269 (i+1))
      = (∑ i ∈ Finset.range 246, stT269 (i+1)) + stT269 247 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 246
    simpa using h
  have hprev := st269_p246
  have hstep := st269_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p248 : ((835890432129/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT269 (i+1))
      = (∑ i ∈ Finset.range 247, stT269 (i+1)) + stT269 248 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 247
    simpa using h
  have hprev := st269_p247
  have hstep := st269_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p249 : ((13347186222839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT269 (i+1))
      = (∑ i ∈ Finset.range 248, stT269 (i+1)) + stT269 249 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 248
    simpa using h
  have hprev := st269_p248
  have hstep := st269_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_p250 : ((13056794366667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT269 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT269 (i+1))
      = (∑ i ∈ Finset.range 249, stT269 (i+1)) + stT269 250 := by
    have h := Finset.sum_range_succ (fun i => stT269 (i+1)) 249
    simpa using h
  have hprev := st269_p249
  have hstep := st269_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st269_s250 :
    |Real.sin (((269 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))
      - ((99001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 3418039/5000000) (δ := 3399/250000000) (ψ := -18323/62500) 269 236
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 269`** (evaluated boundary). -/
theorem station_269_sign : 0 < hardyG ((((269:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 269 250 (by norm_num) (by norm_num)
    ((-18323/62500 : ℚ) : ℝ)
  have hchain := st269_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT269 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((269 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-18323/62500 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st269_c250
  have hsinb := abs_le.mp st269_s250
  have hbdy_lo : ((-16772642441621/723612500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((269 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18323/62500 : ℚ) : ℝ))) / 2
          - ((((269:ℕ)):ℝ))
            * Real.sin (((269 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18323/62500 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((269:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((269:ℝ) * Real.log (250:ℝ) - ((-18323/62500 : ℚ) : ℝ))) / 2
        - ((269:ℝ)) * Real.sin ((269:ℝ) * Real.log (250:ℝ) - ((-18323/62500 : ℚ) : ℝ))
        ≥ ((-212158853/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((269:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-212158853/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-212158853/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-212158853/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((269:ℕ)):ℝ))+1) * (((((269:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((98964896569/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((13056794366667/5000000000000 : ℚ) : ℝ) + ((-16772642441621/723612500000000 : ℚ) : ℝ)
      - ((98964896569/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-18323/62500 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((269:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-18323/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((269:ℕ)):ℝ)))).re
      - Real.sin ((-18323/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((269:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((269:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((269:ℕ)):ℝ))
      = (((((269:ℕ)):ℝ)) * (Real.log ((((269:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((269:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_269
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
  have hθwin : |(((-18323/62500 : ℚ) : ℝ) + ((59:ℤ)) * (2*Real.pi)) - theta ((((269:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((269:ℕ)):ℝ)))
    (φ := ((-18323/62500 : ℚ) : ℝ) + ((59:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-18323/62500 : ℚ)) : ℝ) 59).1,
    (cos_sin_shift (((-18323/62500 : ℚ)) : ℝ) 59).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_269_sign
end AxiomAudit
