import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 299` (rung-309; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT299 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((299 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((158821/500000 : ℚ) : ℝ))

theorem st299_c1 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((37999/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158821/2000000) (δ := 1/1000000000) (ψ := 158821/500000) 299 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t1 : ((7599/8000 : ℚ) : ℝ) ≤ stT299 1 := by
  have hc : ((7599/8000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7599/8000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((7599/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c2 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((458209/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -514699/5000000) (δ := 7519/500000000) (ψ := 158821/500000) 299 33
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t2 : ((3239672985653/5000000000000 : ℚ) : ℝ) ≤ stT299 2 := by
  have hc : ((458159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3239672985653/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((458159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c3 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((64327/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1802231/5000000) (δ := 599/40000000) (ψ := 158821/500000) 299 52
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t3 : ((185551694027/2500000000000 : ℚ) : ℝ) ≤ stT299 3 := by
  have hc : ((64277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185551694027/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((64277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c4 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((874757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -632327/5000000) (δ := 599/40000000) (ψ := 158821/500000) 299 66
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t4 : ((874657/2000000 : ℚ) : ℝ) ≤ stT299 4 := by
  have hc : ((874657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((874657/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((874657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c5 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-242797/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7252409/10000000) (δ := 7477/500000000) (ψ := 158821/500000) 299 77
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t5 : ((-67870812987/156250000000 : ℚ) : ℝ) ≤ stT299 5 := by
  have hc : ((-121411/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67870812987/156250000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-121411/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c6 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((221267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1684603/5000000) (δ := 14991/1000000000) (ψ := 158821/500000) 299 85
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t6 : ((451455148247/5000000000000 : ℚ) : ℝ) ≤ stT299 6 := by
  have hc : ((221167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((451455148247/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((221167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c7 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-475421/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1766713/2500000) (δ := 7517/500000000) (ψ := 158821/500000) 299 93
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t7 : ((-359422317559/1000000000000 : ℚ) : ℝ) ≤ stT299 7 := by
  have hc : ((-475471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-359422317559/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-475471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c8 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((206339/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149991/1000000) (δ := 14991/1000000000) (ψ := 158821/500000) 299 99
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t8 : ((364714977681/1250000000000 : ℚ) : ℝ) ≤ stT299 8 := by
  have hc : ((103157/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364714977681/1250000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((103157/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c9 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-499111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7704897/10000000) (δ := 2991/200000000) (ψ := 158821/500000) 299 105
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t9 : ((-831935166387/2500000000000 : ℚ) : ℝ) ≤ stT299 9 := by
  have hc : ((-499161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-831935166387/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-499161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c10 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-989289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374387/500000) (δ := 1889/125000000) (ψ := 158821/500000) 299 110
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t10 : ((-1564361534071/5000000000000 : ℚ) : ℝ) ≤ stT299 10 := by
  have hc : ((-989389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1564361534071/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-989389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c11 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((932359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462391/5000000) (δ := 751/50000000) (ψ := 158821/500000) 299 114
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t11 : ((2810866230267/10000000000000 : ℚ) : ℝ) ≤ stT299 11 := by
  have hc : ((932259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2810866230267/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((932259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c12 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((311923/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62679/200000) (δ := 7527/500000000) (ψ := 158821/500000) 299 118
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t12 : ((900155357073/10000000000000 : ℚ) : ℝ) ≤ stT299 12 := by
  have hc : ((311823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((900155357073/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((311823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c13 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((249641/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26803/2000000) (δ := 7563/500000000) (ψ := 158821/500000) 299 122
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t13 : ((86538747/312500000 : ℚ) : ℝ) ≤ stT299 13 := by
  have hc : ((15601/15625 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86538747/312500000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((15601/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c14 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-487867/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1825527/2500000) (δ := 15097/1000000000) (ψ := 158821/500000) 299 126
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t14 : ((-1304013317121/5000000000000 : ℚ) : ℝ) ≤ stT299 14 := by
  have hc : ((-487917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1304013317121/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-487917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c15 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((416211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570761/2000000) (δ := 603/40000000) (ψ := 158821/500000) 299 129
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t15 : ((268598402167/2500000000000 : ℚ) : ℝ) ≤ stT299 15 := by
  have hc : ((416111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268598402167/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((416111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c16 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((768651/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -867583/5000000) (δ := 7527/500000000) (ψ := 158821/500000) 299 132
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t16 : ((768551/4000000 : ℚ) : ℝ) ≤ stT299 16 := by
  have hc : ((768551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((768551/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((768551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c17 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((76661/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3542167/10000000) (δ := 14971/1000000000) (ψ := 158821/500000) 299 135
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t17 : ((46452237129/1250000000000 : ℚ) : ℝ) ≤ stT299 17 := by
  have hc : ((76611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46452237129/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((76611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c18 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-499703/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 776781/1000000) (δ := 7559/500000000) (ψ := 158821/500000) 299 137
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t18 : ((-1177929315319/5000000000000 : ℚ) : ℝ) ≤ stT299 18 := by
  have hc : ((-499753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1177929315319/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-499753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c19 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((91159/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1059153/10000000) (δ := 15107/1000000000) (ψ := 158821/500000) 299 140
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t19 : ((209110116393/1000000000000 : ℚ) : ℝ) ≤ stT299 19 := by
  have hc : ((91149/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209110116393/1000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((91149/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c20 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-249657/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544599/2000000) (δ := 1891/125000000) (ψ := 158821/500000) 299 143
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t20 : ((-69788241297/312500000000 : ℚ) : ℝ) ≤ stT299 20 := by
  have hc : ((-124841/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69788241297/312500000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-124841/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c21 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((120623/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2668247/10000000) (δ := 15143/1000000000) (ψ := 158821/500000) 299 145
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t21 : ((65791575611/625000000000 : ℚ) : ℝ) ≤ stT299 21 := by
  have hc : ((60299/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65791575611/625000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((60299/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c22 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((192441/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344763/5000000) (δ := 14957/1000000000) (ψ := 158821/500000) 299 147
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t22 : ((410242918947/2000000000000 : ℚ) : ℝ) ≤ stT299 22 := by
  have hc : ((192421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((410242918947/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((192421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c23 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((269929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62533/250000) (δ := 14971/1000000000) (ψ := 158821/500000) 299 149
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t23 : ((70342072197/625000000000 : ℚ) : ℝ) ≤ stT299 23 := by
  have hc : ((269879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70342072197/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((269879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c24 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((199909/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1449347/5000000) (δ := 15117/1000000000) (ψ := 158821/500000) 299 151
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t24 : ((407960385019/5000000000000 : ℚ) : ℝ) ≤ stT299 24 := by
  have hc : ((199859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407960385019/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((199859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c25 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((348753/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1997213/10000000) (δ := 3/200000) (ψ := 158821/500000) 299 153
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t25 : ((348703/2500000 : ℚ) : ℝ) ≤ stT299 25 := by
  have hc : ((348703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348703/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((348703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c26 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((49959/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2531/250000) (δ := 7557/500000000) (ψ := 158821/500000) 299 155
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t26 : ((48983918297/250000000000 : ℚ) : ℝ) ≤ stT299 26 := by
  have hc : ((24977/25000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48983918297/250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((24977/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c27 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((30717/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3306293/10000000) (δ := 7537/500000000) (ψ := 158821/500000) 299 157
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t27 : ((236363241/5000000000 : ℚ) : ℝ) ≤ stT299 27 := by
  have hc : ((61409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236363241/5000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((61409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c28 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-991991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7537363/10000000) (δ := 15143/1000000000) (ψ := 158821/500000) 299 159
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t28 : ((-1874876389893/10000000000000 : ℚ) : ℝ) ≤ stT299 28 := by
  have hc : ((-992091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1874876389893/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-992091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c29 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((367787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149271/500000) (δ := 14953/1000000000) (ψ := 158821/500000) 299 160
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t29 : ((682777477711/10000000000000 : ℚ) : ℝ) ≤ stT299 29 := by
  have hc : ((367687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((682777477711/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((367687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c30 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((41113/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -617827/2000000) (δ := 3013/200000000) (ψ := 158821/500000) 299 162
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t30 : ((150077735941/2500000000000 : ℚ) : ℝ) ≤ stT299 30 := by
  have hc : ((82201/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150077735941/2500000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((82201/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c31 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-655273/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 714169/1250000) (δ := 471/31250000) (ψ := 158821/500000) 299 163
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t31 : ((-588542649071/5000000000000 : ℚ) : ℝ) ≤ stT299 31 := by
  have hc : ((-655373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-588542649071/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-655373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c32 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((141029/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -985211/5000000) (δ := 15117/1000000000) (ψ := 158821/500000) 299 165
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t32 : ((124635457947/1000000000000 : ℚ) : ℝ) ≤ stT299 32 := by
  have hc : ((141009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124635457947/1000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((141009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c33 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-132491/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2661693/5000000) (δ := 1501/100000000) (ψ := 158821/500000) 299 166
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t33 : ((-57670201233/625000000000 : ℚ) : ℝ) ≤ stT299 33 := by
  have hc : ((-33129/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57670201233/625000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-33129/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c34 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((59791/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3777423/10000000) (δ := 2999/200000000) (ψ := 158821/500000) 299 168
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t34 : ((20473833927/2000000000000 : ℚ) : ℝ) ≤ stT299 34 := by
  have hc : ((59691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20473833927/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((59691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c35 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((40153/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 218277/1000000) (δ := 3747/250000000) (ψ := 158821/500000) 299 169
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t35 : ((67860372699/625000000000 : ℚ) : ℝ) ≤ stT299 35 := by
  have hc : ((160587/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67860372699/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((160587/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c36 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-495873/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1506511/2000000) (δ := 7561/500000000) (ψ := 158821/500000) 299 170
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t36 : ((-826538498641/5000000000000 : ℚ) : ℝ) ≤ stT299 36 := by
  have hc : ((-495923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-826538498641/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-495923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c37 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((104107/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3402619/10000000) (δ := 473/31250000) (ψ := 158821/500000) 299 172
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t37 : ((171068563373/5000000000000 : ℚ) : ℝ) ≤ stT299 37 := by
  have hc : ((104057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171068563373/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((104057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c38 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((189237/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 823897/10000000) (δ := 3761/250000000) (ψ := 158821/500000) 299 173
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t38 : ((153475233219/1000000000000 : ℚ) : ℝ) ≤ stT299 38 := by
  have hc : ((189217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153475233219/1000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((189217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c39 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-239889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 226631/500000) (δ := 15051/1000000000) (ψ := 158821/500000) 299 174
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t39 : ((-192145032949/5000000000000 : ℚ) : ℝ) ≤ stT299 39 := by
  have hc : ((-239989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192145032949/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-239989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c40 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-99913/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484357/625000) (δ := 7479/500000000) (ψ := 158821/500000) 299 175
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t40 : ((-157992152297/1000000000000 : ℚ) : ℝ) ≤ stT299 40 := by
  have hc : ((-99923/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157992152297/1000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-99923/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c41 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-490447/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325531/625000) (δ := 3743/250000000) (ψ := 158821/500000) 299 177
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t41 : ((-383052945343/5000000000000 : ℚ) : ℝ) ≤ stT299 41 := by
  have hc : ((-490547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383052945343/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-490547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c42 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((79611/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2903503/10000000) (δ := 15079/1000000000) (ψ := 158821/500000) 299 178
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t42 : ((122811539503/2000000000000 : ℚ) : ℝ) ≤ stT299 42 := by
  have hc : ((79591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122811539503/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((79591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c43 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((229383/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -511209/5000000) (δ := 1877/125000000) (ψ := 158821/500000) 299 179
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t43 : ((34976750963/250000000000 : ℚ) : ℝ) ≤ stT299 43 := by
  have hc : ((114679/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34976750963/250000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((114679/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c44 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((61471/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45427/1000000) (δ := 15009/1000000000) (ψ := 158821/500000) 299 180
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t44 : ((92661552651/625000000000 : ℚ) : ℝ) ≤ stT299 44 := by
  have hc : ((245859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92661552651/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((245859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c45 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((815103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61789/400000) (δ := 15001/1000000000) (ψ := 158821/500000) 299 181
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t45 : ((1214933937133/10000000000000 : ℚ) : ℝ) ≤ stT299 45 := by
  have hc : ((815003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1214933937133/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((815003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c46 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((616587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2265989/10000000) (δ := 3019/200000000) (ψ := 158821/500000) 299 182
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t46 : ((908960146053/10000000000000 : ℚ) : ℝ) ≤ stT299 46 := by
  have hc : ((616487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((908960146053/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((616487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c47 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((9889/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 526797/2000000) (δ := 943/62500000) (ψ := 158821/500000) 299 183
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t47 : ((14421662663/200000000000 : ℚ) : ℝ) ≤ stT299 47 := by
  have hc : ((9887/20000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14421662663/200000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((9887/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c48 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((30261/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2663439/10000000) (δ := 15123/1000000000) (ψ := 158821/500000) 299 184
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t48 : ((1397406393/20000000000 : ℚ) : ℝ) ≤ stT299 48 := by
  have hc : ((121019/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1397406393/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((121019/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c49 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((145963/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2368327/10000000) (δ := 15073/1000000000) (ψ := 158821/500000) 299 185
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t49 : ((104241397299/1250000000000 : ℚ) : ℝ) ≤ stT299 49 := by
  have hc : ((72969/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104241397299/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((72969/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c50 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((95219/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1761957/10000000) (δ := 7483/500000000) (ψ := 158821/500000) 299 186
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t50 : ((269284539969/2500000000000 : ℚ) : ℝ) ≤ stT299 50 := by
  have hc : ((190413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269284539969/2500000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((190413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c51 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((941893/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 856437/10000000) (δ := 15059/1000000000) (ψ := 158821/500000) 299 187
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t51 : ((32969347551/250000000000 : ℚ) : ℝ) ≤ stT299 51 := by
  have hc : ((941793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32969347551/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((941793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c52 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((198191/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21031/625000) (δ := 15051/1000000000) (ψ := 158821/500000) 299 188
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t52 : ((1099254537/8000000000 : ℚ) : ℝ) ≤ stT299 52 := by
  have hc : ((198171/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1099254537/8000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((198171/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c53 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((4689/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180593/1000000) (δ := 7479/500000000) (ψ := 158821/500000) 299 189
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t53 : ((10303960547/100000000000 : ℚ) : ℝ) ≤ stT299 53 := by
  have hc : ((37507/50000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10303960547/100000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((37507/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c54 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((153567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3541549/10000000) (δ := 15137/1000000000) (ψ := 158821/500000) 299 190
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t54 : ((208842037209/10000000000000 : ℚ) : ℝ) ≤ stT299 54 := by
  have hc : ((153467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208842037209/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((153467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c55 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-599301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138339/250000) (δ := 1513/100000000) (ψ := 158821/500000) 299 191
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t55 : ((-2020580771/25000000000 : ℚ) : ℝ) ≤ stT299 55 := by
  have hc : ((-599401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2020580771/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-599401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c56 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-999471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3886347/5000000) (δ := 749/50000000) (ψ := 158821/500000) 299 192
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t56 : ((-1335733724297/10000000000000 : ℚ) : ℝ) ≤ stT299 56 := by
  have hc : ((-999571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1335733724297/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-999571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c57 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-143689/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5457757/10000000) (δ := 749/50000000) (ψ := 158821/500000) 299 192
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t57 : ((-95176967781/1250000000000 : ℚ) : ℝ) ≤ stT299 57 := by
  have hc : ((-71857/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95176967781/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-71857/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c58 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((226769/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 687541/2500000) (δ := 1877/125000000) (ψ := 158821/500000) 299 193
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t58 : ((37212069627/625000000000 : ℚ) : ℝ) ≤ stT299 58 := by
  have hc : ((226719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37212069627/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((226719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c59 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((997417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35947/2000000) (δ := 7497/500000000) (ψ := 158821/500000) 299 194
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t59 : ((1298396031813/10000000000000 : ℚ) : ℝ) ≤ stT299 59 := by
  have hc : ((997317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1298396031813/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((997317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c60 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((238713/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3324391/10000000) (δ := 7501/500000000) (ψ := 158821/500000) 299 195
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t60 : ((154023975661/5000000000000 : ℚ) : ℝ) ≤ stT299 60 := by
  have hc : ((238613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154023975661/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((238613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c61 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-178231/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6676703/10000000) (δ := 7547/500000000) (ψ := 158821/500000) 299 196
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t61 : ((-228227054619/2000000000000 : ℚ) : ℝ) ≤ stT299 61 := by
  have hc : ((-178251/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228227054619/2000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-178251/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c62 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-58137/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5478021/10000000) (δ := 7497/500000000) (ψ := 158821/500000) 299 196
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t62 : ((-36923403147/500000000000 : ℚ) : ℝ) ≤ stT299 62 := by
  have hc : ((-58147/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36923403147/500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-58147/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c63 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((19247/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1730357/10000000) (δ := 1877/125000000) (ψ := 158821/500000) 299 197
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t63 : ((48491559809/500000000000 : ℚ) : ℝ) ≤ stT299 63 := by
  have hc : ((38489/50000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48491559809/500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((38489/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c64 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((39711/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275719/1250000) (δ := 15023/1000000000) (ψ := 158821/500000) 299 198
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t64 : ((158819/2000000 : ℚ) : ℝ) ≤ stT299 64 := by
  have hc : ((158819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158819/2000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((158819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c65 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-40929/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3162163/5000000) (δ := 14973/1000000000) (ψ := 158821/500000) 299 199
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t65 : ((-6346550629/62500000000 : ℚ) : ℝ) ≤ stT299 65 := by
  have hc : ((-20467/25000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6346550629/62500000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-20467/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c66 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-6999/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508813/1000000) (δ := 15073/1000000000) (ψ := 158821/500000) 299 199
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t66 : ((-27574711647/500000000000 : ℚ) : ℝ) ≤ stT299 66 := by
  have hc : ((-112009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27574711647/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-112009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c67 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((969307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 620997/10000000) (δ := 7533/500000000) (ψ := 158821/500000) 299 200
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t67 : ((592037188329/5000000000000 : ℚ) : ℝ) ≤ stT299 67 := by
  have hc : ((969207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((592037188329/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((969207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c68 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-34269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4012679/10000000) (δ := 7529/500000000) (ψ := 158821/500000) 299 201
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t68 : ((-41678564551/10000000000000 : ℚ) : ℝ) ≤ stT299 68 := by
  have hc : ((-34369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41678564551/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-34369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c69 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-928061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1724981/2500000) (δ := 7529/500000000) (ψ := 158821/500000) 299 201
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t69 : ((-1117374973299/10000000000000 : ℚ) : ℝ) ≤ stT299 69 := by
  have hc : ((-928161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1117374973299/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-928161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c70 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((711613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 973757/5000000) (δ := 15051/1000000000) (ψ := 158821/500000) 299 202
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t70 : ((212605064991/2500000000000 : ℚ) : ℝ) ≤ stT299 70 := by
  have hc : ((711513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212605064991/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((711513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c71 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((151487/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3157461/10000000) (δ := 1893/125000000) (ψ := 158821/500000) 299 203
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t71 : ((179722554297/5000000000000 : ℚ) : ℝ) ≤ stT299 71 := by
  have hc : ((151437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179722554297/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((151437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c72 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-975311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7297299/10000000) (δ := 15059/1000000000) (ψ := 158821/500000) 299 203
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t72 : ((-71845848027/625000000000 : ℚ) : ℝ) ≤ stT299 72 := by
  have hc : ((-975411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71845848027/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-975411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c73 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((181221/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1899827/10000000) (δ := 15037/1000000000) (ψ := 158821/500000) 299 204
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t73 : ((53018447889/625000000000 : ℚ) : ℝ) ≤ stT299 73 := by
  have hc : ((45299/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53018447889/625000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((45299/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c74 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((115359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72759/200000) (δ := 14973/1000000000) (ψ := 158821/500000) 299 205
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t74 : ((33496455321/2500000000000 : ℚ) : ℝ) ≤ stT299 74 := by
  have hc : ((115259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33496455321/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((115259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c75 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-208667/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6395817/10000000) (δ := 1503/100000000) (ψ := 158821/500000) 299 205
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t75 : ((-60244215273/625000000000 : ℚ) : ℝ) ≤ stT299 75 := by
  have hc : ((-52173/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60244215273/625000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-52173/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c76 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((121551/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 588641/10000000) (δ := 749/50000000) (ψ := 158821/500000) 299 206
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t76 : ((139414139503/1250000000000 : ℚ) : ℝ) ≤ stT299 76 := by
  have hc : ((243077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139414139503/1250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((243077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c77 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-538263/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -668491/1250000) (δ := 3023/200000000) (ψ := 158821/500000) 299 207
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t77 : ((-306760852489/5000000000000 : ℚ) : ℝ) ≤ stT299 77 := by
  have hc : ((-538363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306760852489/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-538363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c78 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-18451/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1074341/2500000) (δ := 3747/250000000) (ψ := 158821/500000) 299 207
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t78 : ((-20905814853/1250000000000 : ℚ) : ℝ) ≤ stT299 78 := by
  have hc : ((-36927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20905814853/1250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-36927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c79 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((9101/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1888197/10000000) (δ := 469/31250000) (ψ := 158821/500000) 299 208
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t79 : ((40952041713/500000000000 : ℚ) : ℝ) ≤ stT299 79 := by
  have hc : ((36399/50000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40952041713/500000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((36399/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c80 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-123849/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 939307/1250000) (δ := 469/31250000) (ψ := 158821/500000) 299 208
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t80 : ((-138481368291/1250000000000 : ℚ) : ℝ) ≤ stT299 80 := by
  have hc : ((-247723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138481368291/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-247723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c81 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((906057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136539/1250000) (δ := 7551/500000000) (ψ := 158821/500000) 299 209
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t81 : ((1006618788227/10000000000000 : ℚ) : ℝ) ≤ stT299 81 := by
  have hc : ((905957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1006618788227/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((905957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c82 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-570163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -680469/1250000) (δ := 7497/500000000) (ψ := 158821/500000) 299 210
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t82 : ((-157437638777/2500000000000 : ℚ) : ℝ) ≤ stT299 82 := by
  have hc : ((-570263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157437638777/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-570263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c83 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((123681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 723399/2000000) (δ := 15109/1000000000) (ψ := 158821/500000) 299 210
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t83 : ((67823848001/5000000000000 : ℚ) : ℝ) ≤ stT299 83 := by
  have hc : ((123581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67823848001/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((123581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c84 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((969/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3138797/10000000) (δ := 30087/1000000000) (ψ := 158821/500000) 299 211
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t84 : ((16910788411/500000000000 : ℚ) : ℝ) ≤ stT299 84 := by
  have hc : ((15499/50000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16910788411/500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((15499/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c85 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-65349/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1141491/2000000) (δ := 1877/125000000) (ψ := 158821/500000) 299 211
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t85 : ((-70891835427/1000000000000 : ℚ) : ℝ) ≤ stT299 85 := by
  have hc : ((-65359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70891835427/1000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-65359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c86 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((876093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314437/2500000) (δ := 3781/250000000) (ψ := 158821/500000) 299 212
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t86 : ((944606903711/10000000000000 : ℚ) : ℝ) ≤ stT299 86 := by
  have hc : ((875993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((944606903711/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((875993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c87 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-982383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 923003/1250000) (δ := 15079/1000000000) (ψ := 158821/500000) 299 212
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t87 : ((-1053332796579/10000000000000 : ℚ) : ℝ) ≤ stT299 87 := by
  have hc : ((-982483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1053332796579/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-982483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c88 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((199233/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109507/5000000) (δ := 471/31250000) (ψ := 158821/500000) 299 213
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t88 : ((212361655639/2000000000000 : ℚ) : ℝ) ≤ stT299 88 := by
  have hc : ((199213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212361655639/2000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((199213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c89 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-94779/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7042573/10000000) (δ := 3013/200000000) (ψ := 158821/500000) 299 214
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t89 : ((-50238075211/500000000000 : ℚ) : ℝ) ≤ stT299 89 := by
  have hc : ((-94789/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50238075211/500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-94789/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c90 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((865931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1309469/10000000) (δ := 2993/200000000) (ψ := 158821/500000) 299 214
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t90 : ((228166382613/2500000000000 : ℚ) : ℝ) ≤ stT299 90 := by
  have hc : ((865831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228166382613/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((865831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c91 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-386861/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6138731/10000000) (δ := 6009/200000000) (ψ := 158821/500000) 299 215
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t91 : ((-81118599527/1000000000000 : ℚ) : ℝ) ≤ stT299 91 := by
  have hc : ((-386911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81118599527/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-386911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c92 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((137567/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1015367/5000000) (δ := 3029/200000000) (ψ := 158821/500000) 299 215
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t92 : ((35850662721/500000000000 : ℚ) : ℝ) ≤ stT299 92 := by
  have hc : ((137547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35850662721/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((137547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c93 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-154783/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2798041/5000000) (δ := 1869/125000000) (ψ := 158821/500000) 299 216
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t93 : ((-2508257269/39062500000 : ℚ) : ℝ) ≤ stT299 93 := by
  have hc : ((-19351/31250 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2508257269/39062500000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-19351/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c94 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((573961/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 479731/2000000) (δ := 3763/250000000) (ψ := 158821/500000) 299 216
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t94 : ((591892286481/10000000000000 : ℚ) : ℝ) ≤ stT299 94 := by
  have hc : ((573861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((591892286481/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((573861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c95 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-555429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5399189/10000000) (δ := 3761/250000000) (ψ := 158821/500000) 299 217
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t95 : ((-569961087891/10000000000000 : ℚ) : ℝ) ≤ stT299 95 := by
  have hc : ((-555529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-569961087891/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-555529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c96 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((282137/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 607027/2500000) (δ := 14959/1000000000) (ψ := 158821/500000) 299 217
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t96 : ((14395181697/250000000000 : ℚ) : ℝ) ≤ stT299 96 := by
  have hc : ((282087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14395181697/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((282087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c97 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-299667/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2766831/5000000) (δ := 15067/1000000000) (ψ := 158821/500000) 299 218
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t97 : ((-304316756799/5000000000000 : ℚ) : ℝ) ≤ stT299 97 := by
  have hc : ((-299717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304316756799/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-299717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c98 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((328777/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2133071/10000000) (δ := 473/31250000) (ψ := 158821/500000) 299 218
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t98 : ((41508029563/625000000000 : ℚ) : ℝ) ≤ stT299 98 := by
  have hc : ((328727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41508029563/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((328727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c99 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-91699/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5985973/10000000) (δ := 15029/1000000000) (ψ := 158821/500000) 299 219
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t99 : ((-92173542537/1250000000000 : ℚ) : ℝ) ≤ stT299 99 := by
  have hc : ((-183423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92173542537/1250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-183423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c100 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((32771/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 763313/5000000) (δ := 15129/1000000000) (ψ := 158821/500000) 299 219
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t100 : ((32766967233/400000000000 : ℚ) : ℝ) ≤ stT299 100 := by
  have hc : ((32767/40000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32766967233/400000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((32767/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c101 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-902943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6743413/10000000) (δ := 7511/500000000) (ψ := 158821/500000) 299 220
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t101 : ((-449281050317/5000000000000 : ℚ) : ℝ) ≤ stT299 101 := by
  have hc : ((-903043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-449281050317/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-903043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c102 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((969289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621181/10000000) (δ := 7561/500000000) (ψ := 158821/500000) 299 220
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t102 : ((959639580783/10000000000000 : ℚ) : ℝ) ≤ stT299 102 := by
  have hc : ((969189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((959639580783/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((969189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c103 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-999713/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7794097/10000000) (δ := 3747/250000000) (ψ := 158821/500000) 299 221
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t103 : ((-98514574329/1000000000000 : ℚ) : ℝ) ≤ stT299 103 := by
  have hc : ((-999813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98514574329/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-999813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c104 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((194791/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571827/10000000) (δ := 3003/200000000) (ψ := 158821/500000) 299 221
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t104 : ((9549427359/100000000000 : ℚ) : ℝ) ≤ stT299 104 := by
  have hc : ((194771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9549427359/100000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((194771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c105 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-873211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3290687/5000000) (δ := 3023/200000000) (ψ := 158821/500000) 299 221
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t105 : ((-852265078211/10000000000000 : ℚ) : ℝ) ≤ stT299 105 := by
  have hc : ((-873311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852265078211/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-873311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c106 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((684773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2041261/10000000) (δ := 3777/250000000) (ψ := 158821/500000) 299 222
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t106 : ((133002522961/2000000000000 : ℚ) : ℝ) ≤ stT299 106 := by
  have hc : ((684673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133002522961/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((684673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c107 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-101997/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 995523/2000000) (δ := 2999/200000000) (ψ := 158821/500000) 299 222
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t107 : ((-49314221107/1250000000000 : ℚ) : ℝ) ≤ stT299 107 := by
  have hc : ((-51011/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49314221107/1250000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-51011/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c108 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((60039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -944201/2500000) (δ := 15103/1000000000) (ψ := 158821/500000) 299 223
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t108 : ((230705211/40000000000 : ℚ) : ℝ) ≤ stT299 108 := by
  have hc : ((59939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230705211/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((59939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c109 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((40003/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778151/2500000) (δ := 3/200000) (ψ := 158821/500000) 299 223
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t109 : ((38303940653/1250000000000 : ℚ) : ℝ) ≤ stT299 109 := by
  have hc : ((79981/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38303940653/1250000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((79981/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c110 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-671869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1153763/2000000) (δ := 1511/100000000) (ψ := 158821/500000) 299 224
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t110 : ((-640697578647/10000000000000 : ℚ) : ℝ) ≤ stT299 110 := by
  have hc : ((-671969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640697578647/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-671969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c111 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((184337/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199197/2000000) (δ := 1501/100000000) (ψ := 158821/500000) 299 224
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t111 : ((174945770769/2000000000000 : ℚ) : ℝ) ≤ stT299 111 := by
  have hc : ((184317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174945770769/2000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((184317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c112 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-124763/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7700013/10000000) (δ := 15093/1000000000) (ψ := 158821/500000) 299 224
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t112 : ((-14737733407/156250000000 : ℚ) : ℝ) ≤ stT299 112 := by
  have hc : ((-249551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14737733407/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-249551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c113 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((106867/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -681711/5000000) (δ := 15117/1000000000) (ψ := 158821/500000) 299 225
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t113 : ((2513004131/31250000000 : ℚ) : ℝ) ≤ stT299 113 := by
  have hc : ((213709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2513004131/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((213709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c114 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-495321/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5222501/10000000) (δ := 7493/500000000) (ψ := 158821/500000) 299 225
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t114 : ((-232002186353/5000000000000 : ℚ) : ℝ) ≤ stT299 114 := by
  have hc : ((-495421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232002186353/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-495421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c115 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-3003/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3957021/10000000) (δ := 3781/250000000) (ψ := 158821/500000) 299 226
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t115 : ((-141181257/125000000000 : ℚ) : ℝ) ≤ stT299 115 := by
  have hc : ((-757/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141181257/125000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-757/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c116 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((5353/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1257417/5000000) (δ := 3781/250000000) (ψ := 158821/500000) 299 226
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t116 : ((155287611/3125000000 : ℚ) : ℝ) ≤ stT299 116 := by
  have hc : ((669/1250 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155287611/3125000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((669/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c117 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-908591/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6776739/10000000) (δ := 15031/1000000000) (ψ := 158821/500000) 299 227
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t117 : ((-840085738191/10000000000000 : ℚ) : ℝ) ≤ stT299 117 := by
  have hc : ((-908691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-840085738191/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-908691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c118 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((493127/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414991/10000000) (δ := 3743/250000000) (ψ := 158821/500000) 299 227
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t118 : ((226956933099/2500000000000 : ℚ) : ℝ) ≤ stT299 118 := by
  have hc : ((493077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226956933099/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((493077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c119 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-707821/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473253/2500000) (δ := 3743/250000000) (ψ := 158821/500000) 299 227
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t119 : ((-648950472779/10000000000000 : ℚ) : ℝ) ≤ stT299 119 := by
  have hc : ((-707921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-648950472779/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-707921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c120 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((146409/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3559647/10000000) (δ := 2993/200000000) (ψ := 158821/500000) 299 228
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t120 : ((13356109683/1000000000000 : ℚ) : ℝ) ≤ stT299 120 := by
  have hc : ((146309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13356109683/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((146309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c121 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((491067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1321853/5000000) (δ := 2993/200000000) (ψ := 158821/500000) 299 228
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t121 : ((44633319003/1000000000000 : ℚ) : ℝ) ≤ stT299 121 := by
  have hc : ((490967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44633319003/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((490967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c122 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-929843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3455979/5000000) (δ := 7573/500000000) (ψ := 158821/500000) 299 229
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t122 : ((-420965667297/5000000000000 : ℚ) : ℝ) ≤ stT299 122 := by
  have hc : ((-929943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-420965667297/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-929943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c123 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((947983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -202473/2500000) (δ := 15057/1000000000) (ψ := 158821/500000) 299 229
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t123 : ((854676716727/10000000000000 : ℚ) : ℝ) ≤ stT299 123 := by
  have hc : ((947883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((854676716727/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((947883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c124 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-251173/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1048553/2000000) (δ := 15057/1000000000) (ψ := 158821/500000) 299 229
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t124 : ((-225605037021/5000000000000 : ℚ) : ℝ) ≤ stT299 124 := by
  have hc : ((-251223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225605037021/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-251223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c125 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-212033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4461129/10000000) (δ := 303/20000000) (ψ := 158821/500000) 299 230
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t125 : ((-47434423731/2500000000000 : ℚ) : ℝ) ≤ stT299 125 := by
  have hc : ((-212133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47434423731/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-212133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c126 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((826441/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1495101/10000000) (δ := 14953/1000000000) (ψ := 158821/500000) 299 230
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t126 : ((73616240667/1000000000000 : ℚ) : ℝ) ≤ stT299 126 := by
  have hc : ((826341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73616240667/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((826341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c127 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-983857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7404163/10000000) (δ := 301/20000000) (ψ := 158821/500000) 299 230
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t127 : ((-873121131649/10000000000000 : ℚ) : ℝ) ≤ stT299 127 := by
  have hc : ((-983957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-873121131649/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-983957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c128 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((280003/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -152563/625000) (δ := 187/12500000) (ψ := 158821/500000) 299 231
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t128 : ((247445697499/5000000000000 : ℚ) : ℝ) ≤ stT299 128 := by
  have hc : ((279953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247445697499/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((279953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c129 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((13659/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1688093/5000000) (δ := 15143/1000000000) (ψ := 158821/500000) 299 231
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t129 : ((961645099/50000000000 : ℚ) : ℝ) ≤ stT299 129 := by
  have hc : ((54611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((961645099/50000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((54611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c130 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-86893/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3279791/5000000) (δ := 3759/250000000) (ψ := 158821/500000) 299 232
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t130 : ((-76219058277/1000000000000 : ℚ) : ℝ) ≤ stT299 130 := by
  have hc : ((-86903/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76219058277/1000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-86903/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c131 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((236297/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207891/2500000) (δ := 14967/1000000000) (ψ := 158821/500000) 299 232
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t131 : ((1612748371/19531250000 : ℚ) : ℝ) ≤ stT299 131 := by
  have hc : ((14767/15625 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1612748371/19531250000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((14767/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c132 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-72389/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2426437/5000000) (δ := 473/31250000) (ψ := 158821/500000) 299 232
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t132 : ((-63023997101/2000000000000 : ℚ) : ℝ) ≤ stT299 132 := by
  have hc : ((-72409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63023997101/2000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-72409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c133 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-49221/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5213557/10000000) (δ := 15029/1000000000) (ψ := 158821/500000) 299 233
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t133 : ((-4268869241/100000000000 : ℚ) : ℝ) ≤ stT299 133 := by
  have hc : ((-49231/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4268869241/100000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-49231/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c134 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((494061/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48213/1250000) (δ := 29929/1000000000) (ψ := 158821/500000) 299 233
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t134 : ((106690073637/1250000000000 : ℚ) : ℝ) ≤ stT299 134 := by
  have hc : ((494011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106690073637/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((494011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c135 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-360947/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5943329/10000000) (δ := 15029/1000000000) (ψ := 158821/500000) 299 233
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t135 : ((-310696761011/5000000000000 : ℚ) : ℝ) ≤ stT299 135 := by
  have hc : ((-360997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310696761011/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-360997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c136 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-25611/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4248009/10000000) (δ := 7541/500000000) (ψ := 158821/500000) 299 234
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t136 : ((-21978403083/2000000000000 : ℚ) : ℝ) ≤ stT299 136 := by
  have hc : ((-25631/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21978403083/2000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-25631/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c137 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((22043/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4913/40000) (δ := 15121/1000000000) (ψ := 158821/500000) 299 234
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t137 : ((37660910917/500000000000 : ℚ) : ℝ) ≤ stT299 137 := by
  have hc : ((44081/50000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37660910917/500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((44081/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c138 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-888947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3332297/5000000) (δ := 7541/500000000) (ψ := 158821/500000) 299 234
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t138 : ((-756807482079/10000000000000 : ℚ) : ℝ) ≤ stT299 138 := by
  have hc : ((-889047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-756807482079/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-889047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c139 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((56041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -729239/2000000) (δ := 15089/1000000000) (ψ := 158821/500000) 299 235
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t139 : ((11872723577/1250000000000 : ℚ) : ℝ) ≤ stT299 139 := by
  have hc : ((55991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11872723577/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((55991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c140 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((9681/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 856129/5000000) (δ := 7557/500000000) (ψ := 158821/500000) 299 235
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t140 : ((16361758863/250000000000 : ℚ) : ℝ) ≤ stT299 140 := by
  have hc : ((38719/50000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16361758863/250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((38719/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c141 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-946499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1406503/2000000) (δ := 14989/1000000000) (ψ := 158821/500000) 299 235
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t141 : ((-99647530131/1250000000000 : ℚ) : ℝ) ≤ stT299 141 := by
  have hc : ((-946599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99647530131/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-946599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c142 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((212087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -848179/2500000) (δ := 1887/125000000) (ψ := 158821/500000) 299 236
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t142 : ((177895462647/10000000000000 : ℚ) : ℝ) ≤ stT299 142 := by
  have hc : ((211987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177895462647/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((211987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c143 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((29507/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92647/500000) (δ := 1887/125000000) (ψ := 158821/500000) 299 236
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t143 : ((12335823863/200000000000 : ℚ) : ℝ) ≤ stT299 143 := by
  have hc : ((29503/40000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12335823863/200000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((29503/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c144 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-190047/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441373/625000) (δ := 15007/1000000000) (ψ := 158821/500000) 299 236
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t144 : ((-79194646689/1000000000000 : ℚ) : ℝ) ≤ stT299 144 := by
  have hc : ((-190067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79194646689/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-190067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c145 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((180631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3472921/10000000) (δ := 15103/1000000000) (ψ := 158821/500000) 299 237
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t145 : ((74961345537/5000000000000 : ℚ) : ℝ) ≤ stT299 145 := by
  have hc : ((180531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74961345537/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((180531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c146 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((157281/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1664571/10000000) (δ := 151/10000000) (ψ := 158821/500000) 299 237
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t146 : ((26029997981/400000000000 : ℚ) : ℝ) ≤ stT299 146 := by
  have hc : ((157261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26029997981/400000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((157261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c147 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-453473/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1691733/2500000) (δ := 15103/1000000000) (ψ := 158821/500000) 299 237
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t147 : ((-374059874601/5000000000000 : ℚ) : ℝ) ≤ stT299 147 := by
  have hc : ((-453523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-374059874601/5000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-453523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c148 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((2689/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1936603/5000000) (δ := 14993/1000000000) (ψ := 158821/500000) 299 238
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t148 : ((2200066941/1250000000000 : ℚ) : ℝ) ≤ stT299 148 := by
  have hc : ((5353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2200066941/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((5353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c149 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((447087/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 580267/5000000) (δ := 1501/100000000) (ψ := 158821/500000) 299 238
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t149 : ((366226568547/5000000000000 : ℚ) : ℝ) ≤ stT299 149 := by
  have hc : ((447037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366226568547/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((447037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c150 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-389603/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6160487/10000000) (δ := 1511/100000000) (ψ := 158821/500000) 299 238
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t150 : ((-318150505541/5000000000000 : ℚ) : ℝ) ≤ stT299 150 := by
  have hc : ((-389653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318150505541/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-389653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c151 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-25849/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2290319/5000000) (δ := 15017/1000000000) (ψ := 158821/500000) 299 239
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t151 : ((-21043769751/1000000000000 : ℚ) : ℝ) ≤ stT299 151 := by
  have hc : ((-25859/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21043769751/1000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-25859/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c152 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((495013/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70677/2000000) (δ := 7493/500000000) (ψ := 158821/500000) 299 239
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t152 : ((401467954041/5000000000000 : ℚ) : ℝ) ≤ stT299 152 := by
  have hc : ((494963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401467954041/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((494963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c153 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-253293/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2627521/5000000) (δ := 15117/1000000000) (ψ := 158821/500000) 299 239
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t153 : ((-204815908379/5000000000000 : ℚ) : ℝ) ≤ stT299 153 := by
  have hc : ((-253343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204815908379/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-253343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c154 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-19221/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5583183/10000000) (δ := 121/8000000) (ψ := 158821/500000) 299 240
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t154 : ((-123929936639/2500000000000 : ℚ) : ℝ) ≤ stT299 154 := by
  have hc : ((-153793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123929936639/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-153793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c155 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((955927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74499/1000000) (δ := 7539/500000000) (ψ := 158821/500000) 299 240
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t155 : ((767738407113/10000000000000 : ℚ) : ℝ) ≤ stT299 155 := by
  have hc : ((955827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((767738407113/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((955827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c156 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-54021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1015527/2500000) (δ := 7489/500000000) (ψ := 158821/500000) 299 240
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t156 : ((-43331491561/10000000000000 : ℚ) : ℝ) ≤ stT299 156 := by
  have hc : ((-54121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43331491561/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-54121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c157 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-923457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171737/250000) (δ := 15071/1000000000) (ψ := 158821/500000) 299 241
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t157 : ((-737078835459/10000000000000 : ℚ) : ℝ) ≤ stT299 157 := by
  have hc : ((-923557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-737078835459/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-923557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c158 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((20639/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2123453/10000000) (δ := 15071/1000000000) (ψ := 158821/500000) 299 241
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t158 : ((131336118459/2500000000000 : ℚ) : ℝ) ≤ stT299 158 := by
  have hc : ((165087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131336118459/2500000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((165087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c159 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((101749/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296337/5000000) (δ := 15071/1000000000) (ψ := 158821/500000) 299 241
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t159 : ((80676285179/2000000000000 : ℚ) : ℝ) ≤ stT299 159 := by
  have hc : ((101729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80676285179/2000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((101729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c160 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-486843/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9099/12500) (δ := 15071/1000000000) (ψ := 158821/500000) 299 241
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t160 : ((-38492299901/500000000000 : ℚ) : ℝ) ≤ stT299 160 := by
  have hc : ((-486893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38492299901/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-486893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c161 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((62171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471433/1250000) (δ := 15039/1000000000) (ψ := 158821/500000) 299 242
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t161 : ((4891877581/1000000000000 : ℚ) : ℝ) ≤ stT299 161 := by
  have hc : ((62071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4891877581/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((62071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c162 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((94181/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26783/312500) (δ := 15039/1000000000) (ψ := 158821/500000) 299 242
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t162 : ((36993853127/500000000000 : ℚ) : ℝ) ≤ stT299 162 := by
  have hc : ((94171/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36993853127/500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((94171/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c163 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-28727/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 682137/1250000) (δ := 3741/250000000) (ψ := 158821/500000) 299 242
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t163 : ((-5626163763/125000000000 : ℚ) : ℝ) ≤ stT299 163 := by
  have hc : ((-7183/12500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5626163763/125000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-7183/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c164 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-128967/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177469/312500) (δ := 15057/1000000000) (ψ := 158821/500000) 299 243
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t164 : ((-100721949703/2000000000000 : ℚ) : ℝ) ≤ stT299 164 := by
  have hc : ((-128987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100721949703/2000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-128987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c165 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((224677/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226991/2000000) (δ := 7523/500000000) (ψ := 158821/500000) 299 243
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t165 : ((21861391587/312500000000 : ℚ) : ℝ) ≤ stT299 165 := by
  have hc : ((56163/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21861391587/312500000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((56163/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c166 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((43281/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 105677/312500) (δ := 14957/1000000000) (ψ := 158821/500000) 299 243
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t166 : ((671540503/40000000000 : ℚ) : ℝ) ≤ stT299 166 := by
  have hc : ((43261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671540503/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((43261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c167 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-124997/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -391837/500000) (δ := 303/20000000) (ψ := 158821/500000) 299 244
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t167 : ((-3022979729/39062500000 : ℚ) : ℝ) ≤ stT299 167 := by
  have hc : ((-250019/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3022979729/39062500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-250019/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c168 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((109681/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337409/1000000) (δ := 301/20000000) (ψ := 158821/500000) 299 244
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t168 : ((21145517649/1250000000000 : ℚ) : ℝ) ≤ stT299 168 := by
  have hc : ((109631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21145517649/1250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((109631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c169 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((911093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1062173/10000000) (δ := 301/20000000) (ψ := 158821/500000) 299 244
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t169 : ((70076314539/1000000000000 : ℚ) : ℝ) ≤ stT299 169 := by
  have hc : ((910993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70076314539/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((910993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c170 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-289737/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5472199/10000000) (δ := 14953/1000000000) (ψ := 158821/500000) 299 244
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t170 : ((-44451297291/1000000000000 : ℚ) : ℝ) ≤ stT299 170 := by
  have hc : ((-289787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44451297291/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-289787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c171 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-87003/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2925801/5000000) (δ := 187/12500000) (ψ := 158821/500000) 299 245
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t171 : ((-1663562329/31250000000 : ℚ) : ℝ) ≤ stT299 171 := by
  have hc : ((-174031/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1663562329/31250000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-174031/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c172 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((25841/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373251/2500000) (δ := 753/50000000) (ψ := 158821/500000) 299 245
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t172 : ((39402345969/625000000000 : ℚ) : ℝ) ≤ stT299 172 := by
  have hc : ((206703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39402345969/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((206703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c173 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((421107/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 355041/1250000) (δ := 187/12500000) (ψ := 158821/500000) 299 245
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t173 : ((64017061399/2000000000000 : ℚ) : ℝ) ≤ stT299 173 := by
  have hc : ((421007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64017061399/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((421007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c174 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-960469/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3574347/5000000) (δ := 753/50000000) (ψ := 158821/500000) 299 245
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t174 : ((-728206398331/10000000000000 : ℚ) : ℝ) ≤ stT299 174 := by
  have hc : ((-960569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-728206398331/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-960569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c175 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-138981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4275571/10000000) (δ := 3767/250000000) (ψ := 158821/500000) 299 246
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t175 : ((-105135361249/10000000000000 : ℚ) : ℝ) ≤ stT299 175 := by
  have hc : ((-139081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105135361249/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-139081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c176 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((999979/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4079/2500000) (δ := 3767/250000000) (ψ := 158821/500000) 299 246
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t176 : ((376843396431/5000000000000 : ℚ) : ℝ) ≤ stT299 176 := by
  have hc : ((999879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376843396431/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((999879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c177 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-58243/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4218869/10000000) (δ := 3007/200000000) (ψ := 158821/500000) 299 246
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t177 : ((-43815758571/5000000000000 : ℚ) : ℝ) ≤ stT299 177 := by
  have hc : ((-58293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43815758571/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-58293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c178 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-973561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7277829/10000000) (δ := 1891/125000000) (ψ := 158821/500000) 299 247
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t178 : ((-182447519163/2500000000000 : ℚ) : ℝ) ≤ stT299 178 := by
  have hc : ((-973661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182447519163/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-973661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c179 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((41067/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3090109/10000000) (δ := 603/40000000) (ψ := 158821/500000) 299 247
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t179 : ((12274228083/500000000000 : ℚ) : ℝ) ≤ stT299 179 := by
  have hc : ((82109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12274228083/500000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((82109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c180 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((909097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1074213/10000000) (δ := 3757/250000000) (ψ := 158821/500000) 299 247
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t180 : ((135505091787/2000000000000 : ℚ) : ℝ) ≤ stT299 180 := by
  have hc : ((908997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135505091787/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((908997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c181 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-492891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5215513/10000000) (δ := 603/40000000) (ψ := 158821/500000) 299 247
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t181 : ((-73287549069/2000000000000 : ℚ) : ℝ) ≤ stT299 181 := by
  have hc : ((-492991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73287549069/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-492991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c182 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-207459/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254961/400000) (δ := 15121/1000000000) (ψ := 158821/500000) 299 248
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t182 : ((-30759503/500000000 : ℚ) : ℝ) ≤ stT299 182 := by
  have hc : ((-51871/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30759503/500000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-51871/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c183 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((612767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139049/5000000) (δ := 7541/500000000) (ψ := 158821/500000) 299 248
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t183 : ((452896312407/10000000000000 : ℚ) : ℝ) ≤ stT299 183 := by
  have hc : ((612667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452896312407/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((612667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c184 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((752997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897739/5000000) (δ := 7541/500000000) (ψ := 158821/500000) 299 248
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t184 : ((555042444473/10000000000000 : ℚ) : ℝ) ≤ stT299 184 := by
  have hc : ((752897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((555042444473/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((752897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c185 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-694701/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2923501/5000000) (δ := 15121/1000000000) (ψ := 158821/500000) 299 248
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t185 : ((-102165623443/2000000000000 : ℚ) : ℝ) ≤ stT299 185 := by
  have hc : ((-694801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102165623443/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-694801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c186 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-690181/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2915669/5000000) (δ := 7507/500000000) (ψ := 158821/500000) 299 249
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t186 : ((-126534719829/2500000000000 : ℚ) : ℝ) ≤ stT299 186 := by
  have hc : ((-690281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126534719829/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-690281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c187 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((745643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1823243/10000000) (δ := 7507/500000000) (ψ := 158821/500000) 299 249
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t187 : ((68149340087/1250000000000 : ℚ) : ℝ) ≤ stT299 187 := by
  have hc : ((745543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68149340087/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((745543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c188 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((324183/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2163399/10000000) (δ := 14989/1000000000) (ψ := 158821/500000) 299 249
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t188 : ((59099494023/1250000000000 : ℚ) : ℝ) ≤ stT299 188 := by
  have hc : ((324133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59099494023/1250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((324133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c189 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-771241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6128961/10000000) (δ := 7507/500000000) (ψ := 158821/500000) 299 249
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t189 : ((-561068044013/10000000000000 : ℚ) : ℝ) ≤ stT299 189 := by
  have hc : ((-771341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-561068044013/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-771341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c190 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-631109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1126889/2000000) (δ := 15107/1000000000) (ψ := 158821/500000) 299 250
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t190 : ((-457927611693/10000000000000 : ℚ) : ℝ) ≤ stT299 190 := by
  have hc : ((-631209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-457927611693/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-631209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c191 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((19373/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -855259/5000000) (δ := 3749/250000000) (ψ := 158821/500000) 299 250
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t191 : ((14015990167/250000000000 : ℚ) : ℝ) ≤ stT299 191 := by
  have hc : ((38741/50000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14015990167/250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((38741/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c192 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((79919/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548213/2500000) (δ := 15007/1000000000) (ψ := 158821/500000) 299 250
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t192 : ((115334964531/2500000000000 : ℚ) : ℝ) ≤ stT299 192 := by
  have hc : ((159813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115334964531/2500000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((159813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c193 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-30303/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1215193/2000000) (δ := 15007/1000000000) (ψ := 158821/500000) 299 250
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t193 : ((-2726932939/50000000000 : ℚ) : ℝ) ≤ stT299 193 := by
  have hc : ((-30307/40000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2726932939/50000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-30307/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c194 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-6719/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2884459/5000000) (δ := 3751/250000000) (ψ := 158821/500000) 299 251
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t194 : ((-15077139/312500000 : ℚ) : ℝ) ≤ stT299 194 := by
  have hc : ((-84/125 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15077139/312500000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-84/125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c195 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((71771/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962861/5000000) (δ := 15099/1000000000) (ψ := 158821/500000) 299 251
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t195 : ((25694528377/500000000000 : ℚ) : ℝ) ≤ stT299 195 := by
  have hc : ((71761/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25694528377/500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((71761/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c196 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((362719/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237227/1250000) (δ := 59/3906250) (ψ := 158821/500000) 299 251
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t196 : ((51809805333/1000000000000 : ℚ) : ℝ) ≤ stT299 196 := by
  have hc : ((362669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51809805333/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((362669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c197 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-162953/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2850959/5000000) (δ := 3751/250000000) (ψ := 158821/500000) 299 251
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t197 : ((-58058549319/1250000000000 : ℚ) : ℝ) ≤ stT299 197 := by
  have hc : ((-81489/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58058549319/1250000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-81489/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c198 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-794203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6221229/10000000) (δ := 3773/250000000) (ψ := 158821/500000) 299 252
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t198 : ((-56448731301/1000000000000 : ℚ) : ℝ) ≤ stT299 198 := by
  have hc : ((-794303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56448731301/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-794303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c199 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((555203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2455473/10000000) (δ := 15011/1000000000) (ψ := 158821/500000) 299 252
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t199 : ((393501969743/10000000000000 : ℚ) : ℝ) ≤ stT299 199 := by
  have hc : ((555103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((393501969743/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((555103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c200 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((869529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1291371/10000000) (δ := 15111/1000000000) (ψ := 158821/500000) 299 252
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t200 : ((307389231237/5000000000000 : ℚ) : ℝ) ≤ stT299 200 := by
  have hc : ((869429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307389231237/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((869429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c201 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-13227/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2509801/5000000) (δ := 15111/1000000000) (ψ := 158821/500000) 299 252
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t201 : ((-37327262993/1250000000000 : ℚ) : ℝ) ≤ stT299 201 := by
  have hc : ((-105841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37327262993/1250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-105841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c202 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-46967/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6978743/10000000) (δ := 7559/500000000) (ψ := 158821/500000) 299 253
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t202 : ((-4131175657/62500000000 : ℚ) : ℝ) ≤ stT299 202 := by
  have hc : ((-11743/12500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4131175657/62500000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-11743/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c203 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((253069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -821841/2500000) (δ := 7509/500000000) (ψ := 158821/500000) 299 253
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t203 : ((88774664139/5000000000000 : ℚ) : ℝ) ≤ stT299 203 := by
  have hc : ((252969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88774664139/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((252969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c204 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((988113/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385851/10000000) (δ := 7509/500000000) (ψ := 158821/500000) 299 253
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t204 : ((34587371091/500000000000 : ℚ) : ℝ) ≤ stT299 204 := by
  have hc : ((988013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34587371091/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((988013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c205 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-22819/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2020563/5000000) (δ := 7509/500000000) (ψ := 158821/500000) 299 253
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t205 : ((-15972418539/5000000000000 : ℚ) : ℝ) ≤ stT299 205 := by
  have hc : ((-22869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15972418539/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-22869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c206 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-997541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 767861/1000000) (δ := 3017/200000000) (ψ := 158821/500000) 299 253
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t206 : ((-347545202247/5000000000000 : ℚ) : ℝ) ≤ stT299 206 := by
  have hc : ((-997641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347545202247/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-997641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c207 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-191811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4409509/10000000) (δ := 121/8000000) (ψ := 158821/500000) 299 254
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t207 : ((-133387548639/10000000000000 : ℚ) : ℝ) ≤ stT299 207 := by
  have hc : ((-191911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133387548639/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-191911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c208 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((47417/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -807083/10000000) (δ := 7539/500000000) (ψ := 158821/500000) 299 254
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t208 : ((65748591/1000000000 : ℚ) : ℝ) ≤ stT299 208 := by
  have hc : ((11853/12500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65748591/1000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((11853/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c209 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((443559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2778077/10000000) (δ := 601/40000000) (ψ := 158821/500000) 299 254
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t209 : ((153373399363/5000000000000 : ℚ) : ℝ) ≤ stT299 209 := by
  have hc : ((443459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153373399363/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((443459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c210 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-205889/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6346119/10000000) (δ := 121/8000000) (ψ := 158821/500000) 299 254
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t210 : ((-35523562581/625000000000 : ℚ) : ℝ) ≤ stT299 210 := by
  have hc : ((-102957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35523562581/625000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-102957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c211 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-171051/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5810771/10000000) (δ := 1879/125000000) (ψ := 158821/500000) 299 255
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t211 : ((-29443419901/625000000000 : ℚ) : ℝ) ≤ stT299 211 := by
  have hc : ((-42769/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29443419901/625000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-42769/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c212 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((613267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569129/2500000) (δ := 3783/250000000) (ψ := 158821/500000) 299 255
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t212 : ((210562160967/5000000000000 : ℚ) : ℝ) ≤ stT299 212 := by
  have hc : ((613167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210562160967/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((613167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c213 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((35171/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155143/1250000) (δ := 1879/125000000) (ψ := 158821/500000) 299 255
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t213 : ((6024001599/100000000000 : ℚ) : ℝ) ≤ stT299 213 := by
  have hc : ((35167/40000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6024001599/100000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((35167/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c214 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-80099/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4742359/10000000) (δ := 14971/1000000000) (ψ := 158821/500000) 299 255
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t214 : ((-6846455583/312500000000 : ℚ) : ℝ) ≤ stT299 214 := by
  have hc : ((-20031/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6846455583/312500000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-20031/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c215 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-988877/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7480759/10000000) (δ := 15039/1000000000) (ψ := 158821/500000) 299 256
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t215 : ((-134895473823/2000000000000 : ℚ) : ℝ) ≤ stT299 215 := by
  have hc : ((-988977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134895473823/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-988977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c216 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-34021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200603/500000) (δ := 15039/1000000000) (ψ := 158821/500000) 299 256
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t216 : ((-11608203047/5000000000000 : ℚ) : ℝ) ≤ stT299 216 := by
  have hc : ((-34121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11608203047/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-34121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c217 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((975067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69929/1250000) (δ := 15139/1000000000) (ψ := 158821/500000) 299 256
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t217 : ((165462624537/2500000000000 : ℚ) : ℝ) ≤ stT299 217 := by
  have hc : ((974967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165462624537/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((974967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c218 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((40763/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 719337/2500000) (δ := 1883/125000000) (ψ := 158821/500000) 299 256
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t218 : ((5520279121/200000000000 : ℚ) : ℝ) ≤ stT299 218 := by
  have hc : ((40753/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5520279121/200000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((40753/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c219 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-812587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98413/156250) (δ := 15139/1000000000) (ψ := 158821/500000) 299 256
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t219 : ((-274581744003/5000000000000 : ℚ) : ℝ) ≤ stT299 219 := by
  have hc : ((-812687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274581744003/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-812687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c220 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-738493/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6004071/10000000) (δ := 15047/1000000000) (ψ := 158821/500000) 299 257
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t220 : ((-2489797003/50000000000 : ℚ) : ℝ) ≤ stT299 220 := by
  have hc : ((-738593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2489797003/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-738593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c221 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((25069/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2614009/10000000) (δ := 15047/1000000000) (ψ := 158821/500000) 299 257
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t221 : ((65858793/1953125000 : ℚ) : ℝ) ≤ stT299 221 := by
  have hc : ((3133/6250 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65858793/1953125000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((3133/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c222 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((238517/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 380327/5000000) (δ := 941/62500000) (ψ := 158821/500000) 299 257
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t222 : ((10004083547/156250000000 : ℚ) : ℝ) ≤ stT299 222 := by
  have hc : ((59623/62500 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10004083547/156250000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((59623/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c223 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-38607/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2060109/5000000) (δ := 941/62500000) (ψ := 158821/500000) 299 257
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t223 : ((-517733201/100000000000 : ℚ) : ℝ) ≤ stT299 223 := by
  have hc : ((-38657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-517733201/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-38657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c224 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-197581/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3732379/5000000) (δ := 15147/1000000000) (ψ := 158821/500000) 299 257
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t224 : ((-66013949277/1000000000000 : ℚ) : ℝ) ≤ stT299 224 := by
  have hc : ((-197601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66013949277/1000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-197601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c225 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-192229/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2456771/5000000) (δ := 15049/1000000000) (ψ := 158821/500000) 299 258
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t225 : ((-128186064093/5000000000000 : ℚ) : ℝ) ≤ stT299 225 := by
  have hc : ((-192279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128186064093/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-192279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c226 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((401201/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -399679/2500000) (δ := 30049/1000000000) (ψ := 158821/500000) 299 258
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t226 : ((26684163369/500000000000 : ℚ) : ℝ) ≤ stT299 226 := by
  have hc : ((401151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26684163369/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((401151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c227 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((777187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 850767/5000000) (δ := 15049/1000000000) (ψ := 158821/500000) 299 258
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t227 : ((515770514901/10000000000000 : ℚ) : ℝ) ≤ stT299 227 := by
  have hc : ((777087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((515770514901/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((777087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c228 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-205751/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 997449/2000000) (δ := 15049/1000000000) (ψ := 158821/500000) 299 258
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t228 : ((-136295210867/5000000000000 : ℚ) : ℝ) ≤ stT299 228 := by
  have hc : ((-205801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136295210867/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-205801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c229 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-986931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7449359/10000000) (δ := 14961/1000000000) (ψ := 158821/500000) 299 259
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t229 : ((-652248838389/10000000000000 : ℚ) : ℝ) ≤ stT299 229 := by
  have hc : ((-987031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-652248838389/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-987031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c230 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-21183/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4192277/10000000) (δ := 15061/1000000000) (ψ := 158821/500000) 299 259
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t230 : ((-13980855343/2000000000000 : ℚ) : ℝ) ≤ stT299 230 := by
  have hc : ((-21203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13980855343/2000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-21203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c231 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((185753/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -949323/10000000) (δ := 15061/1000000000) (ψ := 158821/500000) 299 259
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t231 : ((122203213083/2000000000000 : ℚ) : ℝ) ≤ stT299 231 := by
  have hc : ((185733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122203213083/2000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((185733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c232 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((612299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1139789/5000000) (δ := 15061/1000000000) (ψ := 158821/500000) 299 259
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t232 : ((100482058467/2500000000000 : ℚ) : ℝ) ≤ stT299 232 := by
  have hc : ((612199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100482058467/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((612199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c233 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-58677/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109893/200000) (δ := 14961/1000000000) (ψ := 158821/500000) 299 259
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t233 : ((-19223572407/500000000000 : ℚ) : ℝ) ≤ stT299 233 := by
  have hc : ((-58687/100000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19223572407/500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-58687/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c234 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-943819/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1402399/2000000) (δ := 1871/125000000) (ψ := 158821/500000) 299 260
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t234 : ((-617059672599/10000000000000 : ℚ) : ℝ) ≤ stT299 234 := by
  have hc : ((-943919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-617059672599/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-943919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c235 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((20521/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -956089/2500000) (δ := 1871/125000000) (ψ := 158821/500000) 299 260
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t235 : ((1669225811/625000000000 : ℚ) : ℝ) ≤ stT299 235 := by
  have hc : ((20471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1669225811/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((20471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c236 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((193273/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -650247/10000000) (δ := 3007/200000000) (ψ := 158821/500000) 299 260
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t236 : ((1965576263/31250000000 : ℚ) : ℝ) ≤ stT299 236 := by
  have hc : ((193253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1965576263/31250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((193253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c237 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((107359/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2510407/10000000) (δ := 3027/200000000) (ψ := 158821/500000) 299 260
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t237 : ((69724086891/2000000000000 : ℚ) : ℝ) ≤ stT299 237 := by
  have hc : ((107339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69724086891/2000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((107339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c238 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-319157/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1414439/2500000) (δ := 3007/200000000) (ψ := 158821/500000) 299 260
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t238 : ((-51727813557/1250000000000 : ℚ) : ℝ) ≤ stT299 238 := by
  have hc : ((-319207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51727813557/1250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-319207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c239 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-930439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3458007/5000000) (δ := 603/40000000) (ψ := 158821/500000) 299 261
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t239 : ((-601916360533/10000000000000 : ℚ) : ℝ) ≤ stT299 239 := by
  have hc : ((-930539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-601916360533/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-930539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c240 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((52811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3794903/10000000) (δ := 3757/250000000) (ψ := 158821/500000) 299 261
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t240 : ((34024792367/10000000000000 : ℚ) : ℝ) ≤ stT299 240 := by
  have hc : ((52711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34024792367/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((52711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c241 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((962501/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343399/5000000) (δ := 3757/250000000) (ψ := 158821/500000) 299 261
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t241 : ((154984094639/2500000000000 : ℚ) : ℝ) ≤ stT299 241 := by
  have hc : ((962401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154984094639/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((962401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c242 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((142687/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48169/200000) (δ := 3757/250000000) (ψ := 158821/500000) 299 261
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t242 : ((5731659843/156250000000 : ℚ) : ℝ) ≤ stT299 242 := by
  have hc : ((71331/125000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5731659843/156250000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((71331/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c243 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-585559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1372729/2500000) (δ := 599/40000000) (ψ := 158821/500000) 299 261
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t243 : ((-375700834159/10000000000000 : ℚ) : ℝ) ≤ stT299 243 := by
  have hc : ((-585659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375700834159/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-585659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c244 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-60019/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3573607/5000000) (δ := 15083/1000000000) (ψ := 158821/500000) 299 262
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t244 : ((-30741811737/500000000000 : ℚ) : ℝ) ≤ stT299 244 := by
  have hc : ((-240101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30741811737/500000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-240101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c245 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-16287/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4089977/10000000) (δ := 1501/50000000) (ψ := 158821/500000) 299 262
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t245 : ((-1302670203/312500000000 : ℚ) : ℝ) ≤ stT299 245 := by
  have hc : ((-2039/31250 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1302670203/312500000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-2039/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c246 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((913879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -261287/2500000) (δ := 189/12500000) (ψ := 158821/500000) 299 262
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t246 : ((72825444963/1250000000000 : ℚ) : ℝ) ≤ stT299 246 := by
  have hc : ((913779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72825444963/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((913779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c247 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((700339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 198731/1000000) (δ := 189/12500000) (ψ := 158821/500000) 299 262
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t247 : ((111387717969/2500000000000 : ℚ) : ℝ) ≤ stT299 247 := by
  have hc : ((700239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111387717969/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((700239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c248 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-104719/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5007509/10000000) (δ := 189/12500000) (ψ := 158821/500000) 299 262
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t248 : ((-8314068093/312500000000 : ℚ) : ℝ) ≤ stT299 248 := by
  have hc : ((-13093/31250 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8314068093/312500000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-13093/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c249 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-997913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7692439/10000000) (δ := 1499/100000000) (ψ := 158821/500000) 299 263
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t249 : ((-25298631537/400000000000 : ℚ) : ℝ) ≤ stT299 249 := by
  have hc : ((-998013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25298631537/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-998013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_c250 :
    |Real.cos (((299 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-151461/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73381/156250) (δ := 1509/100000000) (ψ := 158821/500000) 299 263
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st299_t250 : ((-11978005127/625000000000 : ℚ) : ℝ) ≤ stT299 250 := by
  have hc : ((-151511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((299 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((158821/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st299_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11978005127/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-151511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st299_p1 : ((7599/8000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT299 (i+1) := by
  rw [Finset.sum_range_one]
  exact st299_t1

theorem st299_p2 : ((7989047985653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT299 (i+1))
      = (∑ i ∈ Finset.range 1, stT299 (i+1)) + stT299 2 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 1
    simpa using h
  have hprev := st299_p1
  have hstep := st299_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p3 : ((8360151373707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT299 (i+1))
      = (∑ i ∈ Finset.range 2, stT299 (i+1)) + stT299 3 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 2
    simpa using h
  have hprev := st299_p2
  have hstep := st299_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p4 : ((10546793873707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT299 (i+1))
      = (∑ i ∈ Finset.range 3, stT299 (i+1)) + stT299 4 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 3
    simpa using h
  have hprev := st299_p3
  have hstep := st299_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p5 : ((8374927858123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT299 (i+1))
      = (∑ i ∈ Finset.range 4, stT299 (i+1)) + stT299 5 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 4
    simpa using h
  have hprev := st299_p4
  have hstep := st299_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p6 : ((882638300637/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT299 (i+1))
      = (∑ i ∈ Finset.range 5, stT299 (i+1)) + stT299 6 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 5
    simpa using h
  have hprev := st299_p5
  have hstep := st299_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p7 : ((281170856743/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT299 (i+1))
      = (∑ i ∈ Finset.range 6, stT299 (i+1)) + stT299 7 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 6
    simpa using h
  have hprev := st299_p6
  have hstep := st299_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p8 : ((8488131329299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT299 (i+1))
      = (∑ i ∈ Finset.range 7, stT299 (i+1)) + stT299 8 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 7
    simpa using h
  have hprev := st299_p7
  have hstep := st299_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p9 : ((272970439861/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT299 (i+1))
      = (∑ i ∈ Finset.range 8, stT299 (i+1)) + stT299 9 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 8
    simpa using h
  have hprev := st299_p8
  have hstep := st299_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p10 : ((2629949731227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT299 (i+1))
      = (∑ i ∈ Finset.range 9, stT299 (i+1)) + stT299 10 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 9
    simpa using h
  have hprev := st299_p9
  have hstep := st299_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p11 : ((533226606207/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT299 (i+1))
      = (∑ i ∈ Finset.range 10, stT299 (i+1)) + stT299 11 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 10
    simpa using h
  have hprev := st299_p10
  have hstep := st299_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p12 : ((1778852564031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT299 (i+1))
      = (∑ i ∈ Finset.range 11, stT299 (i+1)) + stT299 12 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 11
    simpa using h
  have hprev := st299_p11
  have hstep := st299_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p13 : ((2125007552031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT299 (i+1))
      = (∑ i ∈ Finset.range 12, stT299 (i+1)) + stT299 13 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 12
    simpa using h
  have hprev := st299_p12
  have hstep := st299_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p14 : ((7196016891003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT299 (i+1))
      = (∑ i ∈ Finset.range 13, stT299 (i+1)) + stT299 14 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 13
    simpa using h
  have hprev := st299_p13
  have hstep := st299_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p15 : ((7733213695337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT299 (i+1))
      = (∑ i ∈ Finset.range 14, stT299 (i+1)) + stT299 15 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 14
    simpa using h
  have hprev := st299_p14
  have hstep := st299_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p16 : ((8693902445337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT299 (i+1))
      = (∑ i ∈ Finset.range 15, stT299 (i+1)) + stT299 16 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 15
    simpa using h
  have hprev := st299_p15
  have hstep := st299_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p17 : ((8879711393853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT299 (i+1))
      = (∑ i ∈ Finset.range 16, stT299 (i+1)) + stT299 17 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 16
    simpa using h
  have hprev := st299_p16
  have hstep := st299_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p18 : ((3850891039267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT299 (i+1))
      = (∑ i ∈ Finset.range 17, stT299 (i+1)) + stT299 18 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 17
    simpa using h
  have hprev := st299_p17
  have hstep := st299_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p19 : ((8747332660499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT299 (i+1))
      = (∑ i ∈ Finset.range 18, stT299 (i+1)) + stT299 19 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 18
    simpa using h
  have hprev := st299_p18
  have hstep := st299_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p20 : ((7630720799747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT299 (i+1))
      = (∑ i ∈ Finset.range 19, stT299 (i+1)) + stT299 20 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 19
    simpa using h
  have hprev := st299_p19
  have hstep := st299_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p21 : ((1631410680927/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT299 (i+1))
      = (∑ i ∈ Finset.range 20, stT299 (i+1)) + stT299 21 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 20
    simpa using h
  have hprev := st299_p20
  have hstep := st299_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p22 : ((3673064280801/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT299 (i+1))
      = (∑ i ∈ Finset.range 21, stT299 (i+1)) + stT299 22 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 21
    simpa using h
  have hprev := st299_p21
  have hstep := st299_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p23 : ((19490794559157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT299 (i+1))
      = (∑ i ∈ Finset.range 22, stT299 (i+1)) + stT299 23 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 22
    simpa using h
  have hprev := st299_p22
  have hstep := st299_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p24 : ((4061343065839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT299 (i+1))
      = (∑ i ∈ Finset.range 23, stT299 (i+1)) + stT299 24 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 23
    simpa using h
  have hprev := st299_p23
  have hstep := st299_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p25 : ((4340305465839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT299 (i+1))
      = (∑ i ∈ Finset.range 24, stT299 (i+1)) + stT299 25 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 24
    simpa using h
  have hprev := st299_p24
  have hstep := st299_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p26 : ((946435362443/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT299 (i+1))
      = (∑ i ∈ Finset.range 25, stT299 (i+1)) + stT299 26 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 25
    simpa using h
  have hprev := st299_p25
  have hstep := st299_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p27 : ((965344421723/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT299 (i+1))
      = (∑ i ∈ Finset.range 26, stT299 (i+1)) + stT299 27 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 26
    simpa using h
  have hprev := st299_p26
  have hstep := st299_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p28 : ((11129367076591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT299 (i+1))
      = (∑ i ∈ Finset.range 27, stT299 (i+1)) + stT299 28 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 27
    simpa using h
  have hprev := st299_p27
  have hstep := st299_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p29 : ((22941511630893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT299 (i+1))
      = (∑ i ∈ Finset.range 28, stT299 (i+1)) + stT299 29 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 28
    simpa using h
  have hprev := st299_p28
  have hstep := st299_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p30 : ((23541822574657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT299 (i+1))
      = (∑ i ∈ Finset.range 29, stT299 (i+1)) + stT299 30 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 29
    simpa using h
  have hprev := st299_p29
  have hstep := st299_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p31 : ((4472947455303/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT299 (i+1))
      = (∑ i ∈ Finset.range 30, stT299 (i+1)) + stT299 31 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 30
    simpa using h
  have hprev := st299_p30
  have hstep := st299_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p32 : ((4722218371197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT299 (i+1))
      = (∑ i ∈ Finset.range 31, stT299 (i+1)) + stT299 32 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 31
    simpa using h
  have hprev := st299_p31
  have hstep := st299_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p33 : ((22688368636257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT299 (i+1))
      = (∑ i ∈ Finset.range 32, stT299 (i+1)) + stT299 33 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 32
    simpa using h
  have hprev := st299_p32
  have hstep := st299_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p34 : ((5697684451473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT299 (i+1))
      = (∑ i ∈ Finset.range 33, stT299 (i+1)) + stT299 34 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 33
    simpa using h
  have hprev := st299_p33
  have hstep := st299_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p35 : ((5969125942269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT299 (i+1))
      = (∑ i ∈ Finset.range 34, stT299 (i+1)) + stT299 35 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 34
    simpa using h
  have hprev := st299_p34
  have hstep := st299_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p36 : ((11111713385897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT299 (i+1))
      = (∑ i ∈ Finset.range 35, stT299 (i+1)) + stT299 36 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 35
    simpa using h
  have hprev := st299_p35
  have hstep := st299_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p37 : ((1128278194927/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT299 (i+1))
      = (∑ i ∈ Finset.range 36, stT299 (i+1)) + stT299 37 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 36
    simpa using h
  have hprev := st299_p36
  have hstep := st299_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p38 : ((2410031623073/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT299 (i+1))
      = (∑ i ∈ Finset.range 37, stT299 (i+1)) + stT299 38 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 37
    simpa using h
  have hprev := st299_p37
  have hstep := st299_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p39 : ((741125817651/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT299 (i+1))
      = (∑ i ∈ Finset.range 38, stT299 (i+1)) + stT299 39 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 38
    simpa using h
  have hprev := st299_p38
  have hstep := st299_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p40 : ((11068052320931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT299 (i+1))
      = (∑ i ∈ Finset.range 39, stT299 (i+1)) + stT299 40 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 39
    simpa using h
  have hprev := st299_p39
  have hstep := st299_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p41 : ((2671249843897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT299 (i+1))
      = (∑ i ∈ Finset.range 40, stT299 (i+1)) + stT299 41 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 40
    simpa using h
  have hprev := st299_p40
  have hstep := st299_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p42 : ((21984056448691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT299 (i+1))
      = (∑ i ∈ Finset.range 41, stT299 (i+1)) + stT299 42 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 41
    simpa using h
  have hprev := st299_p41
  have hstep := st299_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p43 : ((23383126487211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT299 (i+1))
      = (∑ i ∈ Finset.range 42, stT299 (i+1)) + stT299 43 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 42
    simpa using h
  have hprev := st299_p42
  have hstep := st299_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p44 : ((24865711329627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT299 (i+1))
      = (∑ i ∈ Finset.range 43, stT299 (i+1)) + stT299 44 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 43
    simpa using h
  have hprev := st299_p43
  have hstep := st299_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p45 : ((652016131669/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT299 (i+1))
      = (∑ i ∈ Finset.range 44, stT299 (i+1)) + stT299 45 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 44
    simpa using h
  have hprev := st299_p44
  have hstep := st299_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p46 : ((26989605412813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT299 (i+1))
      = (∑ i ∈ Finset.range 45, stT299 (i+1)) + stT299 46 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 45
    simpa using h
  have hprev := st299_p45
  have hstep := st299_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p47 : ((27710688545963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT299 (i+1))
      = (∑ i ∈ Finset.range 46, stT299 (i+1)) + stT299 47 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 46
    simpa using h
  have hprev := st299_p46
  have hstep := st299_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p48 : ((28409391742463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT299 (i+1))
      = (∑ i ∈ Finset.range 47, stT299 (i+1)) + stT299 48 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 47
    simpa using h
  have hprev := st299_p47
  have hstep := st299_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p49 : ((5848664584171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT299 (i+1))
      = (∑ i ∈ Finset.range 48, stT299 (i+1)) + stT299 49 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 48
    simpa using h
  have hprev := st299_p48
  have hstep := st299_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p50 : ((30320461080731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT299 (i+1))
      = (∑ i ∈ Finset.range 49, stT299 (i+1)) + stT299 50 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 49
    simpa using h
  have hprev := st299_p49
  have hstep := st299_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p51 : ((31639234982771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT299 (i+1))
      = (∑ i ∈ Finset.range 50, stT299 (i+1)) + stT299 51 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 50
    simpa using h
  have hprev := st299_p50
  have hstep := st299_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p52 : ((33013303154021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT299 (i+1))
      = (∑ i ∈ Finset.range 51, stT299 (i+1)) + stT299 52 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 51
    simpa using h
  have hprev := st299_p51
  have hstep := st299_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p53 : ((34043699208721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT299 (i+1))
      = (∑ i ∈ Finset.range 52, stT299 (i+1)) + stT299 53 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 52
    simpa using h
  have hprev := st299_p52
  have hstep := st299_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p54 : ((3425254124593/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT299 (i+1))
      = (∑ i ∈ Finset.range 53, stT299 (i+1)) + stT299 54 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 53
    simpa using h
  have hprev := st299_p53
  have hstep := st299_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p55 : ((3344430893753/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT299 (i+1))
      = (∑ i ∈ Finset.range 54, stT299 (i+1)) + stT299 55 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 54
    simpa using h
  have hprev := st299_p54
  have hstep := st299_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p56 : ((32108575213233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT299 (i+1))
      = (∑ i ∈ Finset.range 55, stT299 (i+1)) + stT299 56 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 55
    simpa using h
  have hprev := st299_p55
  have hstep := st299_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p57 : ((6269431894197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT299 (i+1))
      = (∑ i ∈ Finset.range 56, stT299 (i+1)) + stT299 57 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 56
    simpa using h
  have hprev := st299_p56
  have hstep := st299_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p58 : ((31942552585017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT299 (i+1))
      = (∑ i ∈ Finset.range 57, stT299 (i+1)) + stT299 58 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 57
    simpa using h
  have hprev := st299_p57
  have hstep := st299_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p59 : ((3324094861683/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT299 (i+1))
      = (∑ i ∈ Finset.range 58, stT299 (i+1)) + stT299 59 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 58
    simpa using h
  have hprev := st299_p58
  have hstep := st299_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p60 : ((4193624571019/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT299 (i+1))
      = (∑ i ∈ Finset.range 59, stT299 (i+1)) + stT299 60 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 59
    simpa using h
  have hprev := st299_p59
  have hstep := st299_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p61 : ((32407861295057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT299 (i+1))
      = (∑ i ∈ Finset.range 60, stT299 (i+1)) + stT299 61 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 60
    simpa using h
  have hprev := st299_p60
  have hstep := st299_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p62 : ((31669393232117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT299 (i+1))
      = (∑ i ∈ Finset.range 61, stT299 (i+1)) + stT299 62 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 61
    simpa using h
  have hprev := st299_p61
  have hstep := st299_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p63 : ((32639224428297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT299 (i+1))
      = (∑ i ∈ Finset.range 62, stT299 (i+1)) + stT299 63 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 62
    simpa using h
  have hprev := st299_p62
  have hstep := st299_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p64 : ((33433319428297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT299 (i+1))
      = (∑ i ∈ Finset.range 63, stT299 (i+1)) + stT299 64 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 63
    simpa using h
  have hprev := st299_p63
  have hstep := st299_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p65 : ((32417871327657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT299 (i+1))
      = (∑ i ∈ Finset.range 64, stT299 (i+1)) + stT299 65 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 64
    simpa using h
  have hprev := st299_p64
  have hstep := st299_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p66 : ((31866377094717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT299 (i+1))
      = (∑ i ∈ Finset.range 65, stT299 (i+1)) + stT299 66 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 65
    simpa using h
  have hprev := st299_p65
  have hstep := st299_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p67 : ((264403611771/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT299 (i+1))
      = (∑ i ∈ Finset.range 66, stT299 (i+1)) + stT299 67 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 66
    simpa using h
  have hprev := st299_p66
  have hstep := st299_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p68 : ((4126096613353/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT299 (i+1))
      = (∑ i ∈ Finset.range 67, stT299 (i+1)) + stT299 68 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 67
    simpa using h
  have hprev := st299_p67
  have hstep := st299_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p69 : ((1275655917341/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT299 (i+1))
      = (∑ i ∈ Finset.range 68, stT299 (i+1)) + stT299 69 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 68
    simpa using h
  have hprev := st299_p68
  have hstep := st299_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p70 : ((32741818193489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT299 (i+1))
      = (∑ i ∈ Finset.range 69, stT299 (i+1)) + stT299 70 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 69
    simpa using h
  have hprev := st299_p69
  have hstep := st299_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p71 : ((33101263302083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT299 (i+1))
      = (∑ i ∈ Finset.range 70, stT299 (i+1)) + stT299 71 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 70
    simpa using h
  have hprev := st299_p70
  have hstep := st299_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p72 : ((31951729733651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT299 (i+1))
      = (∑ i ∈ Finset.range 71, stT299 (i+1)) + stT299 72 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 71
    simpa using h
  have hprev := st299_p71
  have hstep := st299_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p73 : ((262400199199/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT299 (i+1))
      = (∑ i ∈ Finset.range 72, stT299 (i+1)) + stT299 73 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 72
    simpa using h
  have hprev := st299_p72
  have hstep := st299_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p74 : ((32934010721159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT299 (i+1))
      = (∑ i ∈ Finset.range 73, stT299 (i+1)) + stT299 74 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 73
    simpa using h
  have hprev := st299_p73
  have hstep := st299_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p75 : ((31970103276791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT299 (i+1))
      = (∑ i ∈ Finset.range 74, stT299 (i+1)) + stT299 75 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 74
    simpa using h
  have hprev := st299_p74
  have hstep := st299_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p76 : ((6617083278563/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT299 (i+1))
      = (∑ i ∈ Finset.range 75, stT299 (i+1)) + stT299 76 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 75
    simpa using h
  have hprev := st299_p75
  have hstep := st299_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p77 : ((32471894687837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT299 (i+1))
      = (∑ i ∈ Finset.range 76, stT299 (i+1)) + stT299 77 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 76
    simpa using h
  have hprev := st299_p76
  have hstep := st299_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p78 : ((32304648169013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT299 (i+1))
      = (∑ i ∈ Finset.range 77, stT299 (i+1)) + stT299 78 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 77
    simpa using h
  have hprev := st299_p77
  have hstep := st299_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p79 : ((33123689003273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT299 (i+1))
      = (∑ i ∈ Finset.range 78, stT299 (i+1)) + stT299 79 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 78
    simpa using h
  have hprev := st299_p78
  have hstep := st299_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p80 : ((6403167611389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT299 (i+1))
      = (∑ i ∈ Finset.range 79, stT299 (i+1)) + stT299 80 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 79
    simpa using h
  have hprev := st299_p79
  have hstep := st299_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p81 : ((8255614211293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT299 (i+1))
      = (∑ i ∈ Finset.range 80, stT299 (i+1)) + stT299 81 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 80
    simpa using h
  have hprev := st299_p80
  have hstep := st299_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p82 : ((2024544143129/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT299 (i+1))
      = (∑ i ∈ Finset.range 81, stT299 (i+1)) + stT299 82 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 81
    simpa using h
  have hprev := st299_p81
  have hstep := st299_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p83 : ((16264176993033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT299 (i+1))
      = (∑ i ∈ Finset.range 82, stT299 (i+1)) + stT299 83 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 82
    simpa using h
  have hprev := st299_p82
  have hstep := st299_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p84 : ((16433284877143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT299 (i+1))
      = (∑ i ∈ Finset.range 83, stT299 (i+1)) + stT299 84 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 83
    simpa using h
  have hprev := st299_p83
  have hstep := st299_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p85 : ((2009853212501/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT299 (i+1))
      = (∑ i ∈ Finset.range 84, stT299 (i+1)) + stT299 85 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 84
    simpa using h
  have hprev := st299_p84
  have hstep := st299_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p86 : ((33102258303727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT299 (i+1))
      = (∑ i ∈ Finset.range 85, stT299 (i+1)) + stT299 86 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 85
    simpa using h
  have hprev := st299_p85
  have hstep := st299_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p87 : ((8012231376787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT299 (i+1))
      = (∑ i ∈ Finset.range 86, stT299 (i+1)) + stT299 87 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 86
    simpa using h
  have hprev := st299_p86
  have hstep := st299_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p88 : ((33110733785343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT299 (i+1))
      = (∑ i ∈ Finset.range 87, stT299 (i+1)) + stT299 88 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 87
    simpa using h
  have hprev := st299_p87
  have hstep := st299_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p89 : ((32105972281123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT299 (i+1))
      = (∑ i ∈ Finset.range 88, stT299 (i+1)) + stT299 89 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 88
    simpa using h
  have hprev := st299_p88
  have hstep := st299_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p90 : ((1320745512463/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT299 (i+1))
      = (∑ i ∈ Finset.range 89, stT299 (i+1)) + stT299 90 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 89
    simpa using h
  have hprev := st299_p89
  have hstep := st299_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p91 : ((6441490363261/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT299 (i+1))
      = (∑ i ∈ Finset.range 90, stT299 (i+1)) + stT299 91 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 90
    simpa using h
  have hprev := st299_p90
  have hstep := st299_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p92 : ((1316978602829/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT299 (i+1))
      = (∑ i ∈ Finset.range 91, stT299 (i+1)) + stT299 92 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 91
    simpa using h
  have hprev := st299_p91
  have hstep := st299_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p93 : ((32282351209861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT299 (i+1))
      = (∑ i ∈ Finset.range 92, stT299 (i+1)) + stT299 93 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 92
    simpa using h
  have hprev := st299_p92
  have hstep := st299_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p94 : ((16437121748171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT299 (i+1))
      = (∑ i ∈ Finset.range 93, stT299 (i+1)) + stT299 94 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 93
    simpa using h
  have hprev := st299_p93
  have hstep := st299_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p95 : ((32304282408451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT299 (i+1))
      = (∑ i ∈ Finset.range 94, stT299 (i+1)) + stT299 95 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 94
    simpa using h
  have hprev := st299_p94
  have hstep := st299_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p96 : ((32880089676331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT299 (i+1))
      = (∑ i ∈ Finset.range 95, stT299 (i+1)) + stT299 96 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 95
    simpa using h
  have hprev := st299_p95
  have hstep := st299_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p97 : ((32271456162733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT299 (i+1))
      = (∑ i ∈ Finset.range 96, stT299 (i+1)) + stT299 97 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 96
    simpa using h
  have hprev := st299_p96
  have hstep := st299_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p98 : ((32935584635741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT299 (i+1))
      = (∑ i ∈ Finset.range 97, stT299 (i+1)) + stT299 98 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 97
    simpa using h
  have hprev := st299_p97
  have hstep := st299_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p99 : ((6439639259089/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT299 (i+1))
      = (∑ i ∈ Finset.range 98, stT299 (i+1)) + stT299 99 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 98
    simpa using h
  have hprev := st299_p98
  have hstep := st299_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p100 : ((3301737047627/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT299 (i+1))
      = (∑ i ∈ Finset.range 99, stT299 (i+1)) + stT299 100 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 99
    simpa using h
  have hprev := st299_p99
  have hstep := st299_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p101 : ((8029702093909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT299 (i+1))
      = (∑ i ∈ Finset.range 100, stT299 (i+1)) + stT299 101 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 100
    simpa using h
  have hprev := st299_p100
  have hstep := st299_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p102 : ((33078447956419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT299 (i+1))
      = (∑ i ∈ Finset.range 101, stT299 (i+1)) + stT299 102 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 101
    simpa using h
  have hprev := st299_p101
  have hstep := st299_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p103 : ((32093302213129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT299 (i+1))
      = (∑ i ∈ Finset.range 102, stT299 (i+1)) + stT299 103 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 102
    simpa using h
  have hprev := st299_p102
  have hstep := st299_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p104 : ((33048244949029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT299 (i+1))
      = (∑ i ∈ Finset.range 103, stT299 (i+1)) + stT299 104 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 103
    simpa using h
  have hprev := st299_p103
  have hstep := st299_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p105 : ((16097989935409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT299 (i+1))
      = (∑ i ∈ Finset.range 104, stT299 (i+1)) + stT299 105 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 104
    simpa using h
  have hprev := st299_p104
  have hstep := st299_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p106 : ((32860992485623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT299 (i+1))
      = (∑ i ∈ Finset.range 105, stT299 (i+1)) + stT299 106 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 105
    simpa using h
  have hprev := st299_p105
  have hstep := st299_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p107 : ((32466478716767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT299 (i+1))
      = (∑ i ∈ Finset.range 106, stT299 (i+1)) + stT299 107 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 106
    simpa using h
  have hprev := st299_p106
  have hstep := st299_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p108 : ((32524155019517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT299 (i+1))
      = (∑ i ∈ Finset.range 107, stT299 (i+1)) + stT299 108 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 107
    simpa using h
  have hprev := st299_p107
  have hstep := st299_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p109 : ((32830586544741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT299 (i+1))
      = (∑ i ∈ Finset.range 108, stT299 (i+1)) + stT299 109 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 108
    simpa using h
  have hprev := st299_p108
  have hstep := st299_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p110 : ((16094944483047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT299 (i+1))
      = (∑ i ∈ Finset.range 109, stT299 (i+1)) + stT299 110 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 109
    simpa using h
  have hprev := st299_p109
  have hstep := st299_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p111 : ((33064617819939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT299 (i+1))
      = (∑ i ∈ Finset.range 110, stT299 (i+1)) + stT299 111 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 110
    simpa using h
  have hprev := st299_p110
  have hstep := st299_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p112 : ((32121402881891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT299 (i+1))
      = (∑ i ∈ Finset.range 111, stT299 (i+1)) + stT299 112 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 111
    simpa using h
  have hprev := st299_p111
  have hstep := st299_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p113 : ((32925564203811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT299 (i+1))
      = (∑ i ∈ Finset.range 112, stT299 (i+1)) + stT299 113 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 112
    simpa using h
  have hprev := st299_p112
  have hstep := st299_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p114 : ((6492311966221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT299 (i+1))
      = (∑ i ∈ Finset.range 113, stT299 (i+1)) + stT299 114 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 113
    simpa using h
  have hprev := st299_p113
  have hstep := st299_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p115 : ((6490053066109/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT299 (i+1))
      = (∑ i ∈ Finset.range 114, stT299 (i+1)) + stT299 115 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 114
    simpa using h
  have hprev := st299_p114
  have hstep := st299_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p116 : ((6589437137149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT299 (i+1))
      = (∑ i ∈ Finset.range 115, stT299 (i+1)) + stT299 116 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 115
    simpa using h
  have hprev := st299_p115
  have hstep := st299_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p117 : ((16053549973777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT299 (i+1))
      = (∑ i ∈ Finset.range 116, stT299 (i+1)) + stT299 117 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 116
    simpa using h
  have hprev := st299_p116
  have hstep := st299_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p118 : ((660298553599/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT299 (i+1))
      = (∑ i ∈ Finset.range 117, stT299 (i+1)) + stT299 118 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 117
    simpa using h
  have hprev := st299_p117
  have hstep := st299_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p119 : ((32365977207171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT299 (i+1))
      = (∑ i ∈ Finset.range 118, stT299 (i+1)) + stT299 119 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 118
    simpa using h
  have hprev := st299_p118
  have hstep := st299_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p120 : ((32499538304001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT299 (i+1))
      = (∑ i ∈ Finset.range 119, stT299 (i+1)) + stT299 120 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 119
    simpa using h
  have hprev := st299_p119
  have hstep := st299_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p121 : ((32945871494031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT299 (i+1))
      = (∑ i ∈ Finset.range 120, stT299 (i+1)) + stT299 121 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 120
    simpa using h
  have hprev := st299_p120
  have hstep := st299_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p122 : ((32103940159437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT299 (i+1))
      = (∑ i ∈ Finset.range 121, stT299 (i+1)) + stT299 122 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 121
    simpa using h
  have hprev := st299_p121
  have hstep := st299_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p123 : ((8239654219041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT299 (i+1))
      = (∑ i ∈ Finset.range 122, stT299 (i+1)) + stT299 123 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 122
    simpa using h
  have hprev := st299_p122
  have hstep := st299_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p124 : ((16253703401061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT299 (i+1))
      = (∑ i ∈ Finset.range 123, stT299 (i+1)) + stT299 124 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 123
    simpa using h
  have hprev := st299_p123
  have hstep := st299_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p125 : ((16158834553599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT299 (i+1))
      = (∑ i ∈ Finset.range 124, stT299 (i+1)) + stT299 125 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 124
    simpa using h
  have hprev := st299_p124
  have hstep := st299_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p126 : ((8263457878467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT299 (i+1))
      = (∑ i ∈ Finset.range 125, stT299 (i+1)) + stT299 126 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 125
    simpa using h
  have hprev := st299_p125
  have hstep := st299_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p127 : ((32180710382219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT299 (i+1))
      = (∑ i ∈ Finset.range 126, stT299 (i+1)) + stT299 127 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 126
    simpa using h
  have hprev := st299_p126
  have hstep := st299_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p128 : ((32675601777217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT299 (i+1))
      = (∑ i ∈ Finset.range 127, stT299 (i+1)) + stT299 128 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 127
    simpa using h
  have hprev := st299_p127
  have hstep := st299_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p129 : ((32867930797017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT299 (i+1))
      = (∑ i ∈ Finset.range 128, stT299 (i+1)) + stT299 129 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 128
    simpa using h
  have hprev := st299_p128
  have hstep := st299_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p130 : ((32105740214247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT299 (i+1))
      = (∑ i ∈ Finset.range 129, stT299 (i+1)) + stT299 130 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 129
    simpa using h
  have hprev := st299_p129
  have hstep := st299_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p131 : ((32931467380199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT299 (i+1))
      = (∑ i ∈ Finset.range 130, stT299 (i+1)) + stT299 131 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 130
    simpa using h
  have hprev := st299_p130
  have hstep := st299_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p132 : ((16308173697347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT299 (i+1))
      = (∑ i ∈ Finset.range 131, stT299 (i+1)) + stT299 132 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 131
    simpa using h
  have hprev := st299_p131
  have hstep := st299_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p133 : ((16094730235297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT299 (i+1))
      = (∑ i ∈ Finset.range 132, stT299 (i+1)) + stT299 133 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 132
    simpa using h
  have hprev := st299_p132
  have hstep := st299_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p134 : ((3304298105969/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT299 (i+1))
      = (∑ i ∈ Finset.range 133, stT299 (i+1)) + stT299 134 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 133
    simpa using h
  have hprev := st299_p133
  have hstep := st299_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p135 : ((8105396884417/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT299 (i+1))
      = (∑ i ∈ Finset.range 134, stT299 (i+1)) + stT299 135 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 134
    simpa using h
  have hprev := st299_p134
  have hstep := st299_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p136 : ((32311695522253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT299 (i+1))
      = (∑ i ∈ Finset.range 135, stT299 (i+1)) + stT299 136 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 135
    simpa using h
  have hprev := st299_p135
  have hstep := st299_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p137 : ((33064913740593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT299 (i+1))
      = (∑ i ∈ Finset.range 136, stT299 (i+1)) + stT299 137 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 136
    simpa using h
  have hprev := st299_p136
  have hstep := st299_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p138 : ((16154053129257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT299 (i+1))
      = (∑ i ∈ Finset.range 137, stT299 (i+1)) + stT299 138 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 137
    simpa using h
  have hprev := st299_p137
  have hstep := st299_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p139 : ((3240308804713/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT299 (i+1))
      = (∑ i ∈ Finset.range 138, stT299 (i+1)) + stT299 139 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 138
    simpa using h
  have hprev := st299_p138
  have hstep := st299_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p140 : ((661151168033/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT299 (i+1))
      = (∑ i ∈ Finset.range 139, stT299 (i+1)) + stT299 140 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 139
    simpa using h
  have hprev := st299_p139
  have hstep := st299_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p141 : ((16130189080301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT299 (i+1))
      = (∑ i ∈ Finset.range 140, stT299 (i+1)) + stT299 141 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 140
    simpa using h
  have hprev := st299_p140
  have hstep := st299_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p142 : ((32438273623249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT299 (i+1))
      = (∑ i ∈ Finset.range 141, stT299 (i+1)) + stT299 142 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 141
    simpa using h
  have hprev := st299_p141
  have hstep := st299_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p143 : ((33055064816399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT299 (i+1))
      = (∑ i ∈ Finset.range 142, stT299 (i+1)) + stT299 143 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 142
    simpa using h
  have hprev := st299_p142
  have hstep := st299_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p144 : ((32263118349509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT299 (i+1))
      = (∑ i ∈ Finset.range 143, stT299 (i+1)) + stT299 144 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 143
    simpa using h
  have hprev := st299_p143
  have hstep := st299_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p145 : ((32413041040583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT299 (i+1))
      = (∑ i ∈ Finset.range 144, stT299 (i+1)) + stT299 145 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 144
    simpa using h
  have hprev := st299_p144
  have hstep := st299_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p146 : ((8265947747527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT299 (i+1))
      = (∑ i ∈ Finset.range 145, stT299 (i+1)) + stT299 146 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 145
    simpa using h
  have hprev := st299_p145
  have hstep := st299_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p147 : ((16157835620453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT299 (i+1))
      = (∑ i ∈ Finset.range 146, stT299 (i+1)) + stT299 147 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 146
    simpa using h
  have hprev := st299_p146
  have hstep := st299_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p148 : ((16166635888217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT299 (i+1))
      = (∑ i ∈ Finset.range 147, stT299 (i+1)) + stT299 148 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 147
    simpa using h
  have hprev := st299_p147
  have hstep := st299_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p149 : ((4133215614191/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT299 (i+1))
      = (∑ i ∈ Finset.range 148, stT299 (i+1)) + stT299 149 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 148
    simpa using h
  have hprev := st299_p148
  have hstep := st299_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p150 : ((16214711951223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT299 (i+1))
      = (∑ i ∈ Finset.range 149, stT299 (i+1)) + stT299 150 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 149
    simpa using h
  have hprev := st299_p149
  have hstep := st299_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p151 : ((4027373275617/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT299 (i+1))
      = (∑ i ∈ Finset.range 150, stT299 (i+1)) + stT299 151 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 150
    simpa using h
  have hprev := st299_p150
  have hstep := st299_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p152 : ((16510961056509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT299 (i+1))
      = (∑ i ∈ Finset.range 151, stT299 (i+1)) + stT299 152 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 151
    simpa using h
  have hprev := st299_p151
  have hstep := st299_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p153 : ((1630614514813/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT299 (i+1))
      = (∑ i ∈ Finset.range 152, stT299 (i+1)) + stT299 153 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 152
    simpa using h
  have hprev := st299_p152
  have hstep := st299_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p154 : ((4014571318713/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT299 (i+1))
      = (∑ i ∈ Finset.range 153, stT299 (i+1)) + stT299 154 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 153
    simpa using h
  have hprev := st299_p153
  have hstep := st299_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p155 : ((32884308956817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT299 (i+1))
      = (∑ i ∈ Finset.range 154, stT299 (i+1)) + stT299 155 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 154
    simpa using h
  have hprev := st299_p154
  have hstep := st299_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p156 : ((4105122183157/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT299 (i+1))
      = (∑ i ∈ Finset.range 155, stT299 (i+1)) + stT299 156 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 155
    simpa using h
  have hprev := st299_p155
  have hstep := st299_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p157 : ((32103898629797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT299 (i+1))
      = (∑ i ∈ Finset.range 156, stT299 (i+1)) + stT299 157 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 156
    simpa using h
  have hprev := st299_p156
  have hstep := st299_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p158 : ((32629243103633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT299 (i+1))
      = (∑ i ∈ Finset.range 157, stT299 (i+1)) + stT299 158 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 157
    simpa using h
  have hprev := st299_p157
  have hstep := st299_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p159 : ((4129078066191/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT299 (i+1))
      = (∑ i ∈ Finset.range 158, stT299 (i+1)) + stT299 159 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 158
    simpa using h
  have hprev := st299_p158
  have hstep := st299_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p160 : ((8065694632877/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT299 (i+1))
      = (∑ i ∈ Finset.range 159, stT299 (i+1)) + stT299 160 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 159
    simpa using h
  have hprev := st299_p159
  have hstep := st299_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p161 : ((16155848653659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT299 (i+1))
      = (∑ i ∈ Finset.range 160, stT299 (i+1)) + stT299 161 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 160
    simpa using h
  have hprev := st299_p160
  have hstep := st299_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p162 : ((16525787184929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT299 (i+1))
      = (∑ i ∈ Finset.range 161, stT299 (i+1)) + stT299 162 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 161
    simpa using h
  have hprev := st299_p161
  have hstep := st299_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p163 : ((16300740634409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT299 (i+1))
      = (∑ i ∈ Finset.range 162, stT299 (i+1)) + stT299 163 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 162
    simpa using h
  have hprev := st299_p162
  have hstep := st299_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p164 : ((32097871520303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT299 (i+1))
      = (∑ i ∈ Finset.range 163, stT299 (i+1)) + stT299 164 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 163
    simpa using h
  have hprev := st299_p163
  have hstep := st299_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p165 : ((32797436051087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT299 (i+1))
      = (∑ i ∈ Finset.range 164, stT299 (i+1)) + stT299 165 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 164
    simpa using h
  have hprev := st299_p164
  have hstep := st299_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p166 : ((32965321176837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT299 (i+1))
      = (∑ i ∈ Finset.range 165, stT299 (i+1)) + stT299 166 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 165
    simpa using h
  have hprev := st299_p165
  have hstep := st299_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p167 : ((32191438366213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT299 (i+1))
      = (∑ i ∈ Finset.range 166, stT299 (i+1)) + stT299 167 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 166
    simpa using h
  have hprev := st299_p166
  have hstep := st299_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p168 : ((6472120501481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT299 (i+1))
      = (∑ i ∈ Finset.range 167, stT299 (i+1)) + stT299 168 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 167
    simpa using h
  have hprev := st299_p167
  have hstep := st299_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p169 : ((6612273130559/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT299 (i+1))
      = (∑ i ∈ Finset.range 168, stT299 (i+1)) + stT299 169 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 168
    simpa using h
  have hprev := st299_p168
  have hstep := st299_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p170 : ((6523370535977/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT299 (i+1))
      = (∑ i ∈ Finset.range 169, stT299 (i+1)) + stT299 170 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 169
    simpa using h
  have hprev := st299_p169
  have hstep := st299_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p171 : ((6416902546921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT299 (i+1))
      = (∑ i ∈ Finset.range 170, stT299 (i+1)) + stT299 171 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 170
    simpa using h
  have hprev := st299_p170
  have hstep := st299_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p172 : ((32714950270109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT299 (i+1))
      = (∑ i ∈ Finset.range 171, stT299 (i+1)) + stT299 172 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 171
    simpa using h
  have hprev := st299_p171
  have hstep := st299_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p173 : ((2064689723569/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT299 (i+1))
      = (∑ i ∈ Finset.range 172, stT299 (i+1)) + stT299 173 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 172
    simpa using h
  have hprev := st299_p172
  have hstep := st299_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p174 : ((32306829178773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT299 (i+1))
      = (∑ i ∈ Finset.range 173, stT299 (i+1)) + stT299 174 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 173
    simpa using h
  have hprev := st299_p173
  have hstep := st299_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p175 : ((8050423454381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT299 (i+1))
      = (∑ i ∈ Finset.range 174, stT299 (i+1)) + stT299 175 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 174
    simpa using h
  have hprev := st299_p174
  have hstep := st299_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p176 : ((16477690305193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT299 (i+1))
      = (∑ i ∈ Finset.range 175, stT299 (i+1)) + stT299 176 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 175
    simpa using h
  have hprev := st299_p175
  have hstep := st299_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p177 : ((8216937273311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT299 (i+1))
      = (∑ i ∈ Finset.range 176, stT299 (i+1)) + stT299 177 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 176
    simpa using h
  have hprev := st299_p176
  have hstep := st299_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p178 : ((2008622438537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT299 (i+1))
      = (∑ i ∈ Finset.range 177, stT299 (i+1)) + stT299 178 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 177
    simpa using h
  have hprev := st299_p177
  have hstep := st299_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p179 : ((8095860894563/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT299 (i+1))
      = (∑ i ∈ Finset.range 178, stT299 (i+1)) + stT299 179 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 178
    simpa using h
  have hprev := st299_p178
  have hstep := st299_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p180 : ((33060969037187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT299 (i+1))
      = (∑ i ∈ Finset.range 179, stT299 (i+1)) + stT299 180 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 179
    simpa using h
  have hprev := st299_p179
  have hstep := st299_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p181 : ((16347265645921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT299 (i+1))
      = (∑ i ∈ Finset.range 180, stT299 (i+1)) + stT299 181 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 180
    simpa using h
  have hprev := st299_p180
  have hstep := st299_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p182 : ((16039670615921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT299 (i+1))
      = (∑ i ∈ Finset.range 181, stT299 (i+1)) + stT299 182 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 181
    simpa using h
  have hprev := st299_p181
  have hstep := st299_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p183 : ((32532237544249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT299 (i+1))
      = (∑ i ∈ Finset.range 182, stT299 (i+1)) + stT299 183 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 182
    simpa using h
  have hprev := st299_p182
  have hstep := st299_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p184 : ((16543639994361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT299 (i+1))
      = (∑ i ∈ Finset.range 183, stT299 (i+1)) + stT299 184 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 183
    simpa using h
  have hprev := st299_p183
  have hstep := st299_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p185 : ((32576451871507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT299 (i+1))
      = (∑ i ∈ Finset.range 184, stT299 (i+1)) + stT299 185 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 184
    simpa using h
  have hprev := st299_p184
  have hstep := st299_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p186 : ((32070312992191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT299 (i+1))
      = (∑ i ∈ Finset.range 185, stT299 (i+1)) + stT299 186 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 185
    simpa using h
  have hprev := st299_p185
  have hstep := st299_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p187 : ((32615507712887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT299 (i+1))
      = (∑ i ∈ Finset.range 186, stT299 (i+1)) + stT299 187 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 186
    simpa using h
  have hprev := st299_p186
  have hstep := st299_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p188 : ((33088303665071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT299 (i+1))
      = (∑ i ∈ Finset.range 187, stT299 (i+1)) + stT299 188 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 187
    simpa using h
  have hprev := st299_p187
  have hstep := st299_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p189 : ((16263617810529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT299 (i+1))
      = (∑ i ∈ Finset.range 188, stT299 (i+1)) + stT299 189 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 188
    simpa using h
  have hprev := st299_p188
  have hstep := st299_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p190 : ((6413861601873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT299 (i+1))
      = (∑ i ∈ Finset.range 189, stT299 (i+1)) + stT299 190 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 189
    simpa using h
  have hprev := st299_p189
  have hstep := st299_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p191 : ((6525989523209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT299 (i+1))
      = (∑ i ∈ Finset.range 190, stT299 (i+1)) + stT299 191 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 190
    simpa using h
  have hprev := st299_p190
  have hstep := st299_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p192 : ((33091287474169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT299 (i+1))
      = (∑ i ∈ Finset.range 191, stT299 (i+1)) + stT299 192 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 191
    simpa using h
  have hprev := st299_p191
  have hstep := st299_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p193 : ((32545900886369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT299 (i+1))
      = (∑ i ∈ Finset.range 192, stT299 (i+1)) + stT299 193 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 192
    simpa using h
  have hprev := st299_p192
  have hstep := st299_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p194 : ((32063432438369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT299 (i+1))
      = (∑ i ∈ Finset.range 193, stT299 (i+1)) + stT299 194 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 193
    simpa using h
  have hprev := st299_p193
  have hstep := st299_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p195 : ((32577323005909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT299 (i+1))
      = (∑ i ∈ Finset.range 194, stT299 (i+1)) + stT299 195 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 194
    simpa using h
  have hprev := st299_p194
  have hstep := st299_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p196 : ((33095421059239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT299 (i+1))
      = (∑ i ∈ Finset.range 195, stT299 (i+1)) + stT299 196 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 195
    simpa using h
  have hprev := st299_p195
  have hstep := st299_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p197 : ((32630952664687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT299 (i+1))
      = (∑ i ∈ Finset.range 196, stT299 (i+1)) + stT299 197 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 196
    simpa using h
  have hprev := st299_p196
  have hstep := st299_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p198 : ((32066465351677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT299 (i+1))
      = (∑ i ∈ Finset.range 197, stT299 (i+1)) + stT299 198 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 197
    simpa using h
  have hprev := st299_p197
  have hstep := st299_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p199 : ((1622998366071/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT299 (i+1))
      = (∑ i ∈ Finset.range 198, stT299 (i+1)) + stT299 199 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 198
    simpa using h
  have hprev := st299_p198
  have hstep := st299_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p200 : ((16537372891947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT299 (i+1))
      = (∑ i ∈ Finset.range 199, stT299 (i+1)) + stT299 200 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 199
    simpa using h
  have hprev := st299_p199
  have hstep := st299_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p201 : ((655522553599/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT299 (i+1))
      = (∑ i ∈ Finset.range 200, stT299 (i+1)) + stT299 201 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 200
    simpa using h
  have hprev := st299_p200
  have hstep := st299_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p202 : ((3211513957483/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT299 (i+1))
      = (∑ i ∈ Finset.range 201, stT299 (i+1)) + stT299 202 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 201
    simpa using h
  have hprev := st299_p201
  have hstep := st299_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p203 : ((8073172225777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT299 (i+1))
      = (∑ i ∈ Finset.range 202, stT299 (i+1)) + stT299 203 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 202
    simpa using h
  have hprev := st299_p202
  have hstep := st299_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p204 : ((515381817577/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT299 (i+1))
      = (∑ i ∈ Finset.range 203, stT299 (i+1)) + stT299 204 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 203
    simpa using h
  have hprev := st299_p203
  have hstep := st299_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p205 : ((659049829757/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT299 (i+1))
      = (∑ i ∈ Finset.range 204, stT299 (i+1)) + stT299 205 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 204
    simpa using h
  have hprev := st299_p204
  have hstep := st299_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p206 : ((8064350270839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT299 (i+1))
      = (∑ i ∈ Finset.range 205, stT299 (i+1)) + stT299 206 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 205
    simpa using h
  have hprev := st299_p205
  have hstep := st299_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p207 : ((32124013534717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT299 (i+1))
      = (∑ i ∈ Finset.range 206, stT299 (i+1)) + stT299 207 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 206
    simpa using h
  have hprev := st299_p206
  have hstep := st299_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p208 : ((32781499444717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT299 (i+1))
      = (∑ i ∈ Finset.range 207, stT299 (i+1)) + stT299 208 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 207
    simpa using h
  have hprev := st299_p207
  have hstep := st299_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p209 : ((33088246243443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT299 (i+1))
      = (∑ i ∈ Finset.range 208, stT299 (i+1)) + stT299 209 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 208
    simpa using h
  have hprev := st299_p208
  have hstep := st299_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p210 : ((32519869242147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT299 (i+1))
      = (∑ i ∈ Finset.range 209, stT299 (i+1)) + stT299 210 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 209
    simpa using h
  have hprev := st299_p209
  have hstep := st299_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p211 : ((32048774523731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT299 (i+1))
      = (∑ i ∈ Finset.range 210, stT299 (i+1)) + stT299 211 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 210
    simpa using h
  have hprev := st299_p210
  have hstep := st299_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p212 : ((6493979769133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT299 (i+1))
      = (∑ i ∈ Finset.range 211, stT299 (i+1)) + stT299 212 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 211
    simpa using h
  have hprev := st299_p211
  have hstep := st299_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p213 : ((6614459801113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT299 (i+1))
      = (∑ i ∈ Finset.range 212, stT299 (i+1)) + stT299 213 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 212
    simpa using h
  have hprev := st299_p212
  have hstep := st299_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p214 : ((32853212426909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT299 (i+1))
      = (∑ i ∈ Finset.range 213, stT299 (i+1)) + stT299 214 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 213
    simpa using h
  have hprev := st299_p213
  have hstep := st299_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p215 : ((16089367528897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT299 (i+1))
      = (∑ i ∈ Finset.range 214, stT299 (i+1)) + stT299 215 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 214
    simpa using h
  have hprev := st299_p214
  have hstep := st299_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p216 : ((321555186517/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT299 (i+1))
      = (∑ i ∈ Finset.range 215, stT299 (i+1)) + stT299 216 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 215
    simpa using h
  have hprev := st299_p215
  have hstep := st299_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p217 : ((4102171143731/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT299 (i+1))
      = (∑ i ∈ Finset.range 216, stT299 (i+1)) + stT299 217 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 216
    simpa using h
  have hprev := st299_p216
  have hstep := st299_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p218 : ((16546691552949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT299 (i+1))
      = (∑ i ∈ Finset.range 217, stT299 (i+1)) + stT299 218 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 217
    simpa using h
  have hprev := st299_p217
  have hstep := st299_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p219 : ((8136054904473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT299 (i+1))
      = (∑ i ∈ Finset.range 218, stT299 (i+1)) + stT299 219 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 218
    simpa using h
  have hprev := st299_p218
  have hstep := st299_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p220 : ((8011565054323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT299 (i+1))
      = (∑ i ∈ Finset.range 219, stT299 (i+1)) + stT299 220 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 219
    simpa using h
  have hprev := st299_p219
  have hstep := st299_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p221 : ((8095864309363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT299 (i+1))
      = (∑ i ∈ Finset.range 220, stT299 (i+1)) + stT299 221 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 220
    simpa using h
  have hprev := st299_p220
  have hstep := st299_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p222 : ((1651185929223/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT299 (i+1))
      = (∑ i ∈ Finset.range 221, stT299 (i+1)) + stT299 222 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 221
    simpa using h
  have hprev := st299_p221
  have hstep := st299_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p223 : ((824298631609/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT299 (i+1))
      = (∑ i ∈ Finset.range 222, stT299 (i+1)) + stT299 223 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 222
    simpa using h
  have hprev := st299_p222
  have hstep := st299_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p224 : ((3231180577159/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT299 (i+1))
      = (∑ i ∈ Finset.range 223, stT299 (i+1)) + stT299 224 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 223
    simpa using h
  have hprev := st299_p223
  have hstep := st299_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p225 : ((8013858410851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT299 (i+1))
      = (∑ i ∈ Finset.range 224, stT299 (i+1)) + stT299 225 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 224
    simpa using h
  have hprev := st299_p224
  have hstep := st299_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p226 : ((509204951731/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT299 (i+1))
      = (∑ i ∈ Finset.range 225, stT299 (i+1)) + stT299 226 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 225
    simpa using h
  have hprev := st299_p225
  have hstep := st299_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p227 : ((6620977485137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT299 (i+1))
      = (∑ i ∈ Finset.range 226, stT299 (i+1)) + stT299 227 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 226
    simpa using h
  have hprev := st299_p226
  have hstep := st299_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p228 : ((32832297003951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT299 (i+1))
      = (∑ i ∈ Finset.range 227, stT299 (i+1)) + stT299 228 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 227
    simpa using h
  have hprev := st299_p227
  have hstep := st299_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p229 : ((16090024082781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT299 (i+1))
      = (∑ i ∈ Finset.range 228, stT299 (i+1)) + stT299 229 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 228
    simpa using h
  have hprev := st299_p228
  have hstep := st299_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p230 : ((32110143888847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT299 (i+1))
      = (∑ i ∈ Finset.range 229, stT299 (i+1)) + stT299 230 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 229
    simpa using h
  have hprev := st299_p229
  have hstep := st299_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p231 : ((16360579977131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT299 (i+1))
      = (∑ i ∈ Finset.range 230, stT299 (i+1)) + stT299 231 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 230
    simpa using h
  have hprev := st299_p230
  have hstep := st299_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p232 : ((3312308818813/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT299 (i+1))
      = (∑ i ∈ Finset.range 231, stT299 (i+1)) + stT299 232 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 231
    simpa using h
  have hprev := st299_p231
  have hstep := st299_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p233 : ((3273861673999/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT299 (i+1))
      = (∑ i ∈ Finset.range 232, stT299 (i+1)) + stT299 233 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 232
    simpa using h
  have hprev := st299_p232
  have hstep := st299_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p234 : ((32121557067391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT299 (i+1))
      = (∑ i ∈ Finset.range 233, stT299 (i+1)) + stT299 234 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 233
    simpa using h
  have hprev := st299_p233
  have hstep := st299_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p235 : ((32148264680367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT299 (i+1))
      = (∑ i ∈ Finset.range 234, stT299 (i+1)) + stT299 235 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 234
    simpa using h
  have hprev := st299_p234
  have hstep := st299_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p236 : ((32777249084527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT299 (i+1))
      = (∑ i ∈ Finset.range 235, stT299 (i+1)) + stT299 236 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 235
    simpa using h
  have hprev := st299_p235
  have hstep := st299_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p237 : ((16562934759491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT299 (i+1))
      = (∑ i ∈ Finset.range 236, stT299 (i+1)) + stT299 237 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 236
    simpa using h
  have hprev := st299_p236
  have hstep := st299_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p238 : ((16356023505263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT299 (i+1))
      = (∑ i ∈ Finset.range 237, stT299 (i+1)) + stT299 238 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 237
    simpa using h
  have hprev := st299_p237
  have hstep := st299_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p239 : ((32110130649993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT299 (i+1))
      = (∑ i ∈ Finset.range 238, stT299 (i+1)) + stT299 239 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 238
    simpa using h
  have hprev := st299_p238
  have hstep := st299_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p240 : ((803603886059/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT299 (i+1))
      = (∑ i ∈ Finset.range 239, stT299 (i+1)) + stT299 240 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 239
    simpa using h
  have hprev := st299_p239
  have hstep := st299_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p241 : ((8191022955229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT299 (i+1))
      = (∑ i ∈ Finset.range 240, stT299 (i+1)) + stT299 241 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 240
    simpa using h
  have hprev := st299_p240
  have hstep := st299_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p242 : ((8282729512717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT299 (i+1))
      = (∑ i ∈ Finset.range 241, stT299 (i+1)) + stT299 242 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 241
    simpa using h
  have hprev := st299_p241
  have hstep := st299_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p243 : ((32755217216709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT299 (i+1))
      = (∑ i ∈ Finset.range 242, stT299 (i+1)) + stT299 243 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 242
    simpa using h
  have hprev := st299_p242
  have hstep := st299_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p244 : ((32140380981969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT299 (i+1))
      = (∑ i ∈ Finset.range 243, stT299 (i+1)) + stT299 244 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 243
    simpa using h
  have hprev := st299_p243
  have hstep := st299_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p245 : ((32098695535473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT299 (i+1))
      = (∑ i ∈ Finset.range 244, stT299 (i+1)) + stT299 245 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 244
    simpa using h
  have hprev := st299_p244
  have hstep := st299_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p246 : ((32681299095177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT299 (i+1))
      = (∑ i ∈ Finset.range 245, stT299 (i+1)) + stT299 246 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 245
    simpa using h
  have hprev := st299_p245
  have hstep := st299_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p247 : ((33126849967053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT299 (i+1))
      = (∑ i ∈ Finset.range 246, stT299 (i+1)) + stT299 247 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 246
    simpa using h
  have hprev := st299_p246
  have hstep := st299_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p248 : ((32860799788077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT299 (i+1))
      = (∑ i ∈ Finset.range 247, stT299 (i+1)) + stT299 248 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 247
    simpa using h
  have hprev := st299_p247
  have hstep := st299_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p249 : ((8057083499913/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT299 (i+1))
      = (∑ i ∈ Finset.range 248, stT299 (i+1)) + stT299 249 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 248
    simpa using h
  have hprev := st299_p248
  have hstep := st299_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_p250 : ((1601834295881/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT299 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT299 (i+1))
      = (∑ i ∈ Finset.range 249, stT299 (i+1)) + stT299 250 := by
    have h := Finset.sum_range_succ (fun i => stT299 (i+1)) 249
    simpa using h
  have hprev := st299_p249
  have hstep := st299_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st299_s250 :
    |Real.sin (((299 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((158821/500000 : ℚ) : ℝ))
      - ((-190603/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -73381/156250) (δ := 1509/100000000) (ψ := 158821/500000) 299 263
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 299`** (evaluated boundary). -/
theorem station_299_sign : 0 < hardyG ((((299:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 299 250 (by norm_num) (by norm_num)
    ((158821/500000 : ℚ) : ℝ)
  have hchain := st299_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT299 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((299 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((158821/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st299_c250
  have hsinb := abs_le.mp st299_s250
  have hbdy_lo : ((9014792084259/178802500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((299 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((158821/500000 : ℚ) : ℝ))) / 2
          - ((((299:ℕ)):ℝ))
            * Real.sin (((299 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((158821/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((299:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((299:ℝ) * Real.log (250:ℝ) - ((158821/500000 : ℚ) : ℝ))) / 2
        - ((299:ℝ)) * Real.sin ((299:ℝ) * Real.log (250:ℝ) - ((158821/500000 : ℚ) : ℝ))
        ≥ ((71268249/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((299:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((71268249/250000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((71268249/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((71268249/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((299:ℕ)):ℝ))+1) * (((((299:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((12167109471/6250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1601834295881/500000000000 : ℚ) : ℝ) + ((9014792084259/178802500000000 : ℚ) : ℝ)
      - ((12167109471/6250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((158821/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((299:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((158821/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((299:ℕ)):ℝ)))).re
      - Real.sin ((158821/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((299:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((299:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((299:ℕ)):ℝ))
      = (((((299:ℕ)):ℝ)) * (Real.log ((((299:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((299:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_299
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
  have hθwin : |(((158821/500000 : ℚ) : ℝ) + ((68:ℤ)) * (2*Real.pi)) - theta ((((299:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((299:ℕ)):ℝ)))
    (φ := ((158821/500000 : ℚ) : ℝ) + ((68:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((158821/500000 : ℚ)) : ℝ) 68).1,
    (cos_sin_shift (((158821/500000 : ℚ)) : ℝ) 68).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_299_sign
end AxiomAudit
