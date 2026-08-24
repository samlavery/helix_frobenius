import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 302` (rung-309; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT302 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((302 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))

theorem st302_c1 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((986551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205241/5000000) (δ := 201/1000000000) (ψ := -164193/1000000) 302 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t1 : ((986451/1000000 : ℚ) : ℝ) ≤ stT302 1 := by
  have hc : ((986451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((986451/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((986451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c2 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-273477/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5373793/10000000) (δ := 7569/500000000) (ψ := -164193/1000000) 302 33
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t2 : ((-483532004209/1250000000000 : ℚ) : ℝ) ≤ stT302 2 := by
  have hc : ((-273527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483532004209/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-273527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c3 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((30351/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1329661/5000000) (δ := 15121/1000000000) (ψ := -164193/1000000) 302 53
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t3 : ((350390949629/1250000000000 : ℚ) : ℝ) ≤ stT302 3 := by
  have hc : ((121379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((350390949629/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((121379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c4 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-272979/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2685411/5000000) (δ := 15183/1000000000) (ψ := -164193/1000000) 302 67
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t4 : ((-1365145273029/5000000000000 : ℚ) : ℝ) ≤ stT302 4 := by
  have hc : ((-273029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1365145273029/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-273029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c5 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-743567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6022963/10000000) (δ := 15149/1000000000) (ψ := -164193/1000000) 302 77
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t5 : ((-415722495339/1250000000000 : ℚ) : ℝ) ≤ stT302 5 := by
  have hc : ((-743667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415722495339/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-743667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c6 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((302269/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1152013/5000000) (δ := 949/62500000) (ψ := -164193/1000000) 302 86
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t6 : ((616901813779/2500000000000 : ℚ) : ℝ) ≤ stT302 6 := by
  have hc : ((302219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((616901813779/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((302219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c7 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-938949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6975901/10000000) (δ := 3819/250000000) (ψ := -164193/1000000) 302 94
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t7 : ((-709854371521/2000000000000 : ℚ) : ℝ) ≤ stT302 7 := by
  have hc : ((-939049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-709854371521/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-939049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c8 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((986747/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203737/5000000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 100
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t8 : ((3488323027851/10000000000000 : ℚ) : ℝ) ≤ stT302 8 := by
  have hc : ((986647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3488323027851/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((986647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c9 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-132003/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5729089/10000000) (δ := 381/25000000) (ψ := -164193/1000000) 302 106
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t9 : ((-220038377341/1000000000000 : ℚ) : ℝ) ≤ stT302 9 := by
  have hc : ((-132023/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220038377341/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-132023/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c10 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-312567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4721727/10000000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 111
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t10 : ((-494369987713/5000000000000 : ℚ) : ℝ) ≤ stT302 10 := by
  have hc : ((-312667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-494369987713/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-312667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c11 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-47571/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220281/500000) (δ := 3819/250000000) (ψ := -164193/1000000) 302 115
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t11 : ((-17938420743/312500000000 : ℚ) : ℝ) ≤ stT302 11 := by
  have hc : ((-11899/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17938420743/312500000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-11899/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c12 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-972597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3633687/5000000) (δ := 15247/1000000000) (ψ := -164193/1000000) 302 119
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t12 : ((-87747969067/312500000000 : ℚ) : ℝ) ≤ stT302 12 := by
  have hc : ((-972697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87747969067/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-972697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c13 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-367489/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60847/125000) (δ := 3037/200000000) (ψ := -164193/1000000) 302 123
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t13 : ((-1019508459089/10000000000000 : ℚ) : ℝ) ≤ stT302 13 := by
  have hc : ((-367589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1019508459089/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-367589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c14 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((86637/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2012553/10000000) (δ := 15213/1000000000) (ψ := -164193/1000000) 302 127
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t14 : ((115756839097/625000000000 : ℚ) : ℝ) ≤ stT302 14 := by
  have hc : ((173249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115756839097/625000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((173249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c15 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((189871/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 738299/2500000) (δ := 3817/250000000) (ψ := -164193/1000000) 302 130
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t15 : ((122528886037/1250000000000 : ℚ) : ℝ) ≤ stT302 15 := by
  have hc : ((189821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122528886037/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((189821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c16 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-248909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2277937/5000000) (δ := 15147/1000000000) (ψ := -164193/1000000) 302 133
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t16 : ((-622522749009/10000000000000 : ℚ) : ℝ) ≤ stT302 16 := by
  have hc : ((-249009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-622522749009/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-249009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c17 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((35669/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3203557/10000000) (δ := 609/40000000) (ψ := -164193/1000000) 302 136
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t17 : ((43239853107/625000000000 : ℚ) : ℝ) ≤ stT302 17 := by
  have hc : ((71313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43239853107/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((71313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c18 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((953457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38287/500000) (δ := 15299/1000000000) (ψ := -164193/1000000) 302 139
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t18 : ((1123541711427/5000000000000 : ℚ) : ℝ) ≤ stT302 18 := by
  have hc : ((953357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1123541711427/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((953357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c19 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-190219/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3534447/5000000) (δ := 15221/1000000000) (ψ := -164193/1000000) 302 142
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t19 : ((-218219161881/1000000000000 : ℚ) : ℝ) ≤ stT302 19 := by
  have hc : ((-190239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218219161881/1000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-190239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c20 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((995333/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 241621/10000000) (δ := 3047/200000000) (ψ := -164193/1000000) 302 144
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t20 : ((2225407668611/10000000000000 : ℚ) : ℝ) ≤ stT302 20 := by
  have hc : ((995233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2225407668611/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((995233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c21 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-639711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1132459/2000000) (δ := 15153/1000000000) (ψ := -164193/1000000) 302 146
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t21 : ((-1396182128169/10000000000000 : ℚ) : ℝ) ≤ stT302 21 := by
  have hc : ((-639811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1396182128169/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-639811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c22 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-51371/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1267799/2000000) (δ := 119/7812500) (ψ := -164193/1000000) 302 149
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t22 : ((-54768354009/312500000000 : ℚ) : ℝ) ≤ stT302 22 := by
  have hc : ((-205509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54768354009/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-205509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c23 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-53263/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1048453/2500000) (δ := 7593/500000000) (ψ := -164193/1000000) 302 151
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t23 : ((-22233067077/1000000000000 : ℚ) : ℝ) ≤ stT302 23 := by
  have hc : ((-53313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22233067077/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-53313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c24 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((178931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3477241/10000000) (δ := 15203/1000000000) (ψ := -164193/1000000) 302 153
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t24 : ((365037169271/10000000000000 : ℚ) : ℝ) ≤ stT302 24 := by
  have hc : ((178831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365037169271/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((178831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c25 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-29097/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4072557/10000000) (δ := 7607/500000000) (ψ := -164193/1000000) 302 155
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t25 : ((-58294029147/5000000000000 : ℚ) : ℝ) ≤ stT302 25 := by
  have hc : ((-29147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58294029147/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-29147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c26 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-703241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1175371/2000000) (δ := 15229/1000000000) (ψ := -164193/1000000) 302 157
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t26 : ((-689682821121/5000000000000 : ℚ) : ℝ) ≤ stT302 26 := by
  have hc : ((-703341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-689682821121/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-703341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c27 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-929423/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1727277/2500000) (δ := 473/31250000) (ψ := -164193/1000000) 302 158
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t27 : ((-1788867943023/10000000000000 : ℚ) : ℝ) ≤ stT302 27 := by
  have hc : ((-929523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1788867943023/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-929523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c28 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((380631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 590159/2000000) (δ := 303/20000000) (ψ := -164193/1000000) 302 160
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t28 : ((359567927741/5000000000000 : ℚ) : ℝ) ≤ stT302 28 := by
  have hc : ((380531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((359567927741/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((380531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c29 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((176231/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -616/3125) (δ := 3033/200000000) (ψ := -164193/1000000) 302 162
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t29 : ((163603130159/1250000000000 : ℚ) : ℝ) ≤ stT302 29 := by
  have hc : ((88103/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163603130159/1250000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((88103/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c30 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-124961/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3895747/5000000) (δ := 15179/1000000000) (ψ := -164193/1000000) 302 164
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t30 : ((-228169367837/1250000000000 : ℚ) : ℝ) ≤ stT302 30 := by
  have hc : ((-249947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228169367837/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-249947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c31 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((876253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1256917/10000000) (δ := 15117/1000000000) (ψ := -164193/1000000) 302 165
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t31 : ((1573617224109/10000000000000 : ℚ) : ℝ) ≤ stT302 31 := by
  have hc : ((876153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1573617224109/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((876153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c32 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-2457/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6188741/10000000) (δ := 15103/1000000000) (ψ := -164193/1000000) 302 167
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t32 : ((-69503295139/500000000000 : ℚ) : ℝ) ≤ stT302 32 := by
  have hc : ((-39317/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69503295139/500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-39317/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c33 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((215151/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 667927/5000000) (δ := 1901/125000000) (ψ := -164193/1000000) 302 168
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t33 : ((23405386111/156250000000 : ℚ) : ℝ) ≤ stT302 33 := by
  have hc : ((107563/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23405386111/156250000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((107563/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c34 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-992177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3770529/5000000) (δ := 15181/1000000000) (ψ := -164193/1000000) 302 170
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t34 : ((-850870581561/5000000000000 : ℚ) : ℝ) ≤ stT302 34 := by
  have hc : ((-992277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-850870581561/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-992277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c35 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((53433/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1363459/10000000) (δ := 7637/500000000) (ψ := -164193/1000000) 302 171
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t35 : ((90307662939/625000000000 : ℚ) : ℝ) ≤ stT302 35 := by
  have hc : ((213707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90307662939/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((213707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c36 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-27009/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 524701/1250000) (δ := 3809/250000000) (ψ := -164193/1000000) 302 172
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t36 : ((-22528337839/1250000000000 : ℚ) : ℝ) ≤ stT302 36 := by
  have hc : ((-13517/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22528337839/1250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-13517/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c37 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-107929/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3266037/5000000) (δ := 947/62500000) (ψ := -164193/1000000) 302 174
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t37 : ((-35490949317/250000000000 : ℚ) : ℝ) ≤ stT302 37 := by
  have hc : ((-215883/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35490949317/250000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-215883/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c38 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((665809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1052773/5000000) (δ := 7579/500000000) (ψ := -164193/1000000) 302 175
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t38 : ((539961229863/5000000000000 : ℚ) : ℝ) ≤ stT302 38 := by
  have hc : ((665709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539961229863/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((665709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c39 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((150467/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1797993/10000000) (δ := 7569/500000000) (ψ := -164193/1000000) 302 176
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t39 : ((240907922607/2000000000000 : ℚ) : ℝ) ≤ stT302 39 := by
  have hc : ((150447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240907922607/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((150447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c40 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-489217/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5204969/10000000) (δ := 3793/250000000) (ψ := -164193/1000000) 302 177
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t40 : ((-773678192063/10000000000000 : ℚ) : ℝ) ≤ stT302 40 := by
  have hc : ((-489317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-773678192063/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-489317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c41 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-496733/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1513609/2000000) (δ := 951/62500000) (ψ := -164193/1000000) 302 179
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t41 : ((-387922444427/2500000000000 : ℚ) : ℝ) ≤ stT302 41 := by
  have hc : ((-496783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387922444427/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-496783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c42 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-445857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63529/125000) (δ := 15109/1000000000) (ψ := -164193/1000000) 302 180
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t42 : ((-344063406769/5000000000000 : ℚ) : ℝ) ≤ stT302 42 := by
  have hc : ((-445957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344063406769/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-445957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c43 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((353111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -756189/2500000) (δ := 7601/500000000) (ψ := -164193/1000000) 302 181
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t43 : ((107667295967/2000000000000 : ℚ) : ℝ) ≤ stT302 43 := by
  have hc : ((353011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107667295967/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((353011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c44 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((852389/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1375647/10000000) (δ := 3059/200000000) (ψ := -164193/1000000) 302 182
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t44 : ((321218348921/2500000000000 : ℚ) : ℝ) ≤ stT302 44 := by
  have hc : ((852289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321218348921/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((852289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c45 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((15608/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58323/5000000) (δ := 3797/250000000) (ψ := -164193/1000000) 302 183
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t45 : ((372235008833/2500000000000 : ℚ) : ℝ) ≤ stT302 45 := by
  have hc : ((249703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372235008833/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((249703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c46 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((953007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38473/500000) (δ := 191/12500000) (ψ := -164193/1000000) 302 184
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t46 : ((1404984186033/10000000000000 : ℚ) : ℝ) ≤ stT302 46 := by
  have hc : ((952907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1404984186033/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((952907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c47 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((868067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 649377/5000000) (δ := 1523/100000000) (ψ := -164193/1000000) 302 185
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t47 : ((1266059196583/10000000000000 : ℚ) : ℝ) ≤ stT302 47 := by
  have hc : ((867967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1266059196583/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((867967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c48 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((828461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1486107/10000000) (δ := 7633/500000000) (ψ := -164193/1000000) 302 186
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t48 : ((9565084467/80000000000 : ℚ) : ℝ) ≤ stT302 48 := by
  have hc : ((828361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9565084467/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((828361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c49 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((214651/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33641/250000) (δ := 15159/1000000000) (ψ := -164193/1000000) 302 187
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t49 : ((153304239723/1250000000000 : ℚ) : ℝ) ≤ stT302 49 := by
  have hc : ((107313/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153304239723/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((107313/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c50 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((234297/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 890791/10000000) (δ := 15151/1000000000) (ψ := -164193/1000000) 302 188
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t50 : ((10353453373/78125000000 : ℚ) : ℝ) ≤ stT302 50 := by
  have hc : ((14642/15625 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10353453373/78125000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((14642/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c51 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((124821/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 133791/10000000) (δ := 7629/500000000) (ψ := -164193/1000000) 302 189
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t51 : ((8738342319/62500000000 : ℚ) : ℝ) ≤ stT302 51 := by
  have hc : ((249617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8738342319/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((249617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c52 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((46699/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -913507/10000000) (δ := 7583/500000000) (ψ := -164193/1000000) 302 190
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t52 : ((129505809/1000000000 : ℚ) : ℝ) ≤ stT302 52 := by
  have hc : ((23347/25000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129505809/1000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((23347/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c53 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((312357/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2240079/10000000) (δ := 15273/1000000000) (ψ := -164193/1000000) 302 191
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t53 : ((85797291347/1000000000000 : ℚ) : ℝ) ≤ stT302 53 := by
  have hc : ((312307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85797291347/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((312307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c54 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((7317/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3835507/10000000) (δ := 759/50000000) (ψ := -164193/1000000) 302 192
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t54 : ((9929954619/2000000000000 : ℚ) : ℝ) ≤ stT302 54 := by
  have hc : ((7297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9929954619/2000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((7297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c55 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-324079/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56899/100000) (δ := 3779/250000000) (ψ := -164193/1000000) 302 193
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t55 : ((-1092638859/12500000000 : ℚ) : ℝ) ≤ stT302 55 := by
  have hc : ((-324129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1092638859/12500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-324129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c56 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-999711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -974237/1250000) (δ := 15209/1000000000) (ψ := -164193/1000000) 302 194
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t56 : ((-1336054437977/10000000000000 : ℚ) : ℝ) ≤ stT302 56 := by
  have hc : ((-999811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1336054437977/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-999811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c57 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-152671/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2784651/5000000) (δ := 15209/1000000000) (ψ := -164193/1000000) 302 194
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t57 : ((-25281361371/312500000000 : ℚ) : ℝ) ≤ stT302 57 := by
  have hc : ((-19087/31250 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25281361371/312500000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-19087/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c58 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((365283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 748037/2500000) (δ := 7551/500000000) (ψ := -164193/1000000) 302 195
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t58 : ((59938581339/1250000000000 : ℚ) : ℝ) ≤ stT302 58 := by
  have hc : ((365183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59938581339/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((365183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c59 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((997099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 190457/10000000) (δ := 15209/1000000000) (ψ := -164193/1000000) 302 196
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t59 : ((1297982031111/10000000000000 : ℚ) : ℝ) ≤ stT302 59 := by
  have hc : ((996999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1297982031111/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((996999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c60 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((425521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414073/5000000) (δ := 3779/250000000) (ψ := -164193/1000000) 302 197
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t60 : ((274607979237/5000000000000 : ℚ) : ℝ) ≤ stT302 60 := by
  have hc : ((425421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274607979237/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((425421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c61 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-376233/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -757061/1250000) (δ := 759/50000000) (ψ := -164193/1000000) 302 198
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t61 : ((-481781088427/5000000000000 : ℚ) : ℝ) ≤ stT302 61 := by
  have hc : ((-376283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-481781088427/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-376283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c62 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-793951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622019/1000000) (δ := 15223/1000000000) (ψ := -164193/1000000) 302 198
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t62 : ((-504223179051/5000000000000 : ℚ) : ℝ) ≤ stT302 62 := by
  have hc : ((-794051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504223179051/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-794051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c63 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((127199/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162033/625000) (δ := 15273/1000000000) (ψ := -164193/1000000) 302 199
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t63 : ((80112053147/1250000000000 : ℚ) : ℝ) ≤ stT302 63 := by
  have hc : ((63587/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80112053147/1250000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((63587/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c64 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((176449/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -306367/2500000) (δ := 15237/1000000000) (ψ := -164193/1000000) 302 200
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t64 : ((176429/1600000 : ℚ) : ℝ) ≤ stT302 64 := by
  have hc : ((176429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176429/1600000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((176429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c65 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-497147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5227761/10000000) (δ := 7629/500000000) (ψ := -164193/1000000) 302 201
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t65 : ((-154189830489/2500000000000 : ℚ) : ℝ) ≤ stT302 65 := by
  have hc : ((-497247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154189830489/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-497247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c66 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-406383/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3149601/5000000) (δ := 3029/200000000) (ψ := -164193/1000000) 302 201
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t66 : ((-100056895239/1000000000000 : ℚ) : ℝ) ≤ stT302 66 := by
  have hc : ((-406433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100056895239/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-406433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c67 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((17809/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1944853/10000000) (δ := 15151/1000000000) (ψ := -164193/1000000) 302 202
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t67 : ((21754094211/250000000000 : ℚ) : ℝ) ≤ stT302 67 := by
  have hc : ((35613/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21754094211/250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((35613/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c68 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((513889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -257771/1000000) (δ := 3811/250000000) (ψ := -164193/1000000) 302 203
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t68 : ((311530308471/5000000000000 : ℚ) : ℝ) ≤ stT302 68 := by
  have hc : ((513789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311530308471/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((513789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c69 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-972243/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7263579/10000000) (δ := 15137/1000000000) (ψ := -164193/1000000) 302 204
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t69 : ((-1170563871637/10000000000000 : ℚ) : ℝ) ≤ stT302 69 := by
  have hc : ((-972343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1170563871637/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-972343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c70 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((130467/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 359989/1000000) (δ := 7633/500000000) (ψ := -164193/1000000) 302 204
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t70 : ((38954572169/2500000000000 : ℚ) : ℝ) ≤ stT302 70 := by
  have hc : ((130367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38954572169/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((130367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c71 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((847531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1398701/10000000) (δ := 1523/100000000) (ψ := -164193/1000000) 302 205
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t71 : ((1005715009611/10000000000000 : ℚ) : ℝ) ≤ stT302 71 := by
  have hc : ((847431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1005715009611/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((847431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c72 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-86643/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6547007/10000000) (δ := 191/12500000) (ψ := -164193/1000000) 302 206
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t72 : ((-6382600021/62500000000 : ℚ) : ℝ) ≤ stT302 72 := by
  have hc : ((-86653/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6382600021/62500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-86653/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c73 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((1201/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1933467/5000000) (δ := 15123/1000000000) (ψ := -164193/1000000) 302 206
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t73 : ((349952889/125000000000 : ℚ) : ℝ) ≤ stT302 73 := by
  have hc : ((299/12500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349952889/125000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((299/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c74 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((404743/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1568801/10000000) (δ := 3797/250000000) (ψ := -164193/1000000) 302 207
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t74 : ((117611474967/1250000000000 : ℚ) : ℝ) ≤ stT302 74 := by
  have hc : ((404693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117611474967/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((404693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c75 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-239939/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1785581/2500000) (δ := 3777/250000000) (ψ := -164193/1000000) 302 208
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t75 : ((-69271667691/625000000000 : ℚ) : ℝ) ≤ stT302 75 := by
  have hc : ((-59991/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69271667691/625000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-59991/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c76 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((414757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1428901/5000000) (δ := 3777/250000000) (ψ := -164193/1000000) 302 208
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t76 : ((237821961123/5000000000000 : ℚ) : ℝ) ≤ stT302 76 := by
  have hc : ((414657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237821961123/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((414657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c77 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((369533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1490363/5000000) (δ := 15201/1000000000) (ψ := -164193/1000000) 302 209
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t77 : ((84201538793/2000000000000 : ℚ) : ℝ) ≤ stT302 77 := by
  have hc : ((369433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84201538793/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((369433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c78 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-453001/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6761341/10000000) (δ := 15201/1000000000) (ψ := -164193/1000000) 302 209
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t78 : ((-256489840089/2500000000000 : ℚ) : ℝ) ≤ stT302 78 := by
  have hc : ((-453051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256489840089/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-453051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c79 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((482081/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 671323/10000000) (δ := 15109/1000000000) (ψ := -164193/1000000) 302 210
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t79 : ((542326811697/5000000000000 : ℚ) : ℝ) ≤ stT302 79 := by
  have hc : ((482031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((542326811697/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((482031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c80 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-18789/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2769823/5000000) (δ := 951/62500000) (ψ := -164193/1000000) 302 211
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t80 : ((-84040938729/1250000000000 : ℚ) : ℝ) ≤ stT302 80 := by
  have hc : ((-150337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84040938729/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-150337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c81 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((35053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3839341/10000000) (δ := 15187/1000000000) (ψ := -164193/1000000) 302 211
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t81 : ((38836662783/10000000000000 : ℚ) : ℝ) ≤ stT302 81 := by
  have hc : ((34953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38836662783/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((34953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c82 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((504599/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2604697/10000000) (δ := 15279/1000000000) (ψ := -164193/1000000) 302 212
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t82 : ((111425162637/2000000000000 : ℚ) : ℝ) ≤ stT302 82 := by
  have hc : ((504499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111425162637/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((504499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c83 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-43321/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81837/125000) (δ := 15279/1000000000) (ψ := -164193/1000000) 302 212
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t83 : ((-23778240309/250000000000 : ℚ) : ℝ) ≤ stT302 83 := by
  have hc : ((-21663/25000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23778240309/250000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-21663/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c84 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((998867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11901/1000000) (δ := 7593/250000000) (ψ := -164193/1000000) 302 213
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t84 : ((1089743687263/10000000000000 : ℚ) : ℝ) ≤ stT302 84 := by
  have hc : ((998767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1089743687263/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((998767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c85 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-926871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6891963/10000000) (δ := 7569/500000000) (ψ := -164193/1000000) 302 214
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t85 : ((-1005441876063/10000000000000 : ℚ) : ℝ) ≤ stT302 85 := by
  have hc : ((-926971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1005441876063/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-926971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c86 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((89267/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1938517/10000000) (δ := 7569/500000000) (ψ := -164193/1000000) 302 214
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t86 : ((192491074443/2500000000000 : ℚ) : ℝ) ≤ stT302 86 := by
  have hc : ((178509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192491074443/2500000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((178509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c87 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-430991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5040967/10000000) (δ := 7579/500000000) (ψ := -164193/1000000) 302 215
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t87 : ((-462178265283/10000000000000 : ℚ) : ℝ) ≤ stT302 87 := by
  have hc : ((-431091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-462178265283/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-431091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c88 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((135299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1793851/5000000) (δ := 3049/200000000) (ψ := -164193/1000000) 302 215
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t88 : ((144122539597/10000000000000 : ℚ) : ℝ) ≤ stT302 88 := by
  have hc : ((135199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144122539597/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((135199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c89 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((13473/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3589139/10000000) (δ := 947/62500000) (ψ := -164193/1000000) 302 216
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t89 : ((14270739611/1000000000000 : ℚ) : ℝ) ≤ stT302 89 := by
  have hc : ((13463/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14270739611/1000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((13463/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c90 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-179821/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2423351/5000000) (δ := 15251/1000000000) (ψ := -164193/1000000) 302 216
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t90 : ((-189600762003/5000000000000 : ℚ) : ℝ) ≤ stT302 90 := by
  have hc : ((-179871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189600762003/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-179871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c91 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((534019/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78707/312500) (δ := 30259/1000000000) (ψ := -164193/1000000) 302 217
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t91 : ((139924686249/2500000000000 : ℚ) : ℝ) ≤ stT302 91 := by
  have hc : ((533919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139924686249/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((533919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c92 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-661133/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5732809/10000000) (δ := 15259/1000000000) (ψ := -164193/1000000) 302 217
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t92 : ((-689383672509/10000000000000 : ℚ) : ℝ) ≤ stT302 92 := by
  have hc : ((-661233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-689383672509/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-661233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c93 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((748387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72517/400000) (δ := 15167/1000000000) (ψ := -164193/1000000) 302 218
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t93 : ((775936952937/10000000000000 : ℚ) : ℝ) ≤ stT302 93 := by
  have hc : ((748287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((775936952937/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((748287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c94 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-804013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3131013/5000000) (δ := 3809/250000000) (ψ := -164193/1000000) 302 218
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t94 : ((-414689919343/5000000000000 : ℚ) : ℝ) ≤ stT302 94 := by
  have hc : ((-804113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-414689919343/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-804113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c95 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((417523/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1456451/10000000) (δ := 7637/500000000) (ψ := -164193/1000000) 302 219
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t95 : ((214159056797/2500000000000 : ℚ) : ℝ) ≤ stT302 95 := by
  have hc : ((417473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214159056797/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((417473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c96 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-211569/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 322469/500000) (δ := 15129/1000000000) (ψ := -164193/1000000) 302 219
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t96 : ((-107978639937/1250000000000 : ℚ) : ℝ) ≤ stT302 96 := by
  have hc : ((-105797/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107978639937/1250000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-105797/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c97 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((13122/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1434669/10000000) (δ := 15181/1000000000) (ψ := -164193/1000000) 302 220
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t97 : ((106574269871/1250000000000 : ℚ) : ℝ) ≤ stT302 97 := by
  have hc : ((209927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106574269871/1250000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((209927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c98 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-2547/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1577247/2500000) (δ := 7611/500000000) (ψ := -164193/1000000) 302 220
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t98 : ((-41170805821/500000000000 : ℚ) : ℝ) ≤ stT302 98 := by
  have hc : ((-40757/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41170805821/500000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-40757/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c99 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((192243/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1733913/10000000) (δ := 3023/200000000) (ψ := -164193/1000000) 302 221
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t99 : ((96593101033/1250000000000 : ℚ) : ℝ) ≤ stT302 99 := by
  have hc : ((96109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96593101033/1250000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((96109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c100 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-69673/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365879/625000) (δ := 1911/125000000) (ψ := -164193/1000000) 302 221
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t100 : ((-69683/1000000 : ℚ) : ℝ) ≤ stT302 100 := by
  have hc : ((-69683/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69683/1000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-69683/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c101 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((592579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -585337/2500000) (δ := 1901/125000000) (ψ := -164193/1000000) 302 222
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t101 : ((589538526723/10000000000000 : ℚ) : ℝ) ≤ stT302 101 := by
  have hc : ((592479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((589538526723/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((592479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c102 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-90231/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5097139/10000000) (δ := 3039/200000000) (ψ := -164193/1000000) 302 222
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t102 : ((-22340461787/500000000000 : ℚ) : ℝ) ≤ stT302 102 := by
  have hc : ((-90251/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22340461787/500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-90251/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c103 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((269437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3244969/10000000) (δ := 15103/1000000000) (ψ := -164193/1000000) 302 223
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t103 : ((265385556873/10000000000000 : ℚ) : ℝ) ≤ stT302 103 := by
  have hc : ((269337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265385556873/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((269337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c104 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-4909/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 809953/2000000) (δ := 153/10000000) (ψ := -164193/1000000) 302 223
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t104 : ((-4823477939/1000000000000 : ℚ) : ℝ) ≤ stT302 104 := by
  have hc : ((-4919/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4823477939/1000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-4919/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c105 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-201113/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177329/400000) (δ := 1521/100000000) (ψ := -164193/1000000) 302 224
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t105 : ((-196363967913/10000000000000 : ℚ) : ℝ) ≤ stT302 105 := by
  have hc : ((-201213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196363967913/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-201213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c106 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((231563/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2723193/10000000) (δ := 15193/1000000000) (ψ := -164193/1000000) 302 224
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t106 : ((44973020841/1000000000000 : ℚ) : ℝ) ≤ stT302 106 := by
  have hc : ((231513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44973020841/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((231513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c107 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-141703/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5895471/10000000) (δ := 15117/1000000000) (ψ := -164193/1000000) 302 225
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t107 : ((-137008867851/2000000000000 : ℚ) : ℝ) ≤ stT302 107 := by
  have hc : ((-141723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137008867851/2000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-141723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c108 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((56247/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1127841/10000000) (δ := 15117/1000000000) (ψ := -164193/1000000) 302 225
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t108 : ((865882587/10000000000 : ℚ) : ℝ) ≤ stT302 108 := by
  have hc : ((224963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((865882587/10000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((224963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c109 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-995683/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7621589/10000000) (δ := 1903/125000000) (ψ := -164193/1000000) 302 226
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t109 : ((-953787843541/10000000000000 : ℚ) : ℝ) ≤ stT302 109 := by
  have hc : ((-995783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-953787843541/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-995783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c110 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((479033/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90819/1250000) (δ := 15179/1000000000) (ψ := -164193/1000000) 302 226
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t110 : ((228346044573/2500000000000 : ℚ) : ℝ) ≤ stT302 110 := by
  have hc : ((478983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228346044573/2500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((478983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c111 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-382697/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6106123/10000000) (δ := 1903/125000000) (ψ := -164193/1000000) 302 226
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t111 : ((-181643688513/2500000000000 : ℚ) : ℝ) ≤ stT302 111 := by
  have hc : ((-382747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181643688513/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-382747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c112 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((106163/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -707637/2500000) (δ := 1909/125000000) (ψ := -164193/1000000) 302 227
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t112 : ((50145481859/1250000000000 : ℚ) : ℝ) ≤ stT302 112 := by
  have hc : ((53069/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50145481859/1250000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((53069/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c113 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((2317/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3880647/10000000) (δ := 1909/125000000) (ψ := -164193/1000000) 302 227
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t113 : ((54197231/31250000000 : ℚ) : ℝ) ≤ stT302 113 := by
  have hc : ((4609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54197231/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((4609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c114 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-119709/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5175313/10000000) (δ := 3033/200000000) (ψ := -164193/1000000) 302 228
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t114 : ((-28035297031/625000000000 : ℚ) : ℝ) ≤ stT302 114 := by
  have hc : ((-59867/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28035297031/625000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-59867/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c115 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((843273/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1418631/10000000) (δ := 7619/500000000) (ψ := -164193/1000000) 302 228
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t115 : ((98282774399/1250000000000 : ℚ) : ℝ) ≤ stT302 115 := by
  have hc : ((843173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98282774399/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((843173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c116 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-999177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7752543/10000000) (δ := 15257/1000000000) (ψ := -164193/1000000) 302 229
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t116 : ((-927805711129/10000000000000 : ℚ) : ℝ) ≤ stT302 116 := by
  have hc : ((-999277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-927805711129/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-999277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c117 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((436687/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -635887/5000000) (δ := 15257/1000000000) (ψ := -164193/1000000) 302 229
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t117 : ((807341813/10000000000 : ℚ) : ℝ) ≤ stT302 117 := by
  have hc : ((436637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((807341813/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((436637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c118 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-235633/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1030761/2000000) (δ := 7573/500000000) (ψ := -164193/1000000) 302 229
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t118 : ((-8678555109/200000000000 : ℚ) : ℝ) ≤ stT302 118 := by
  have hc : ((-235683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8678555109/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-235683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c119 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-102171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -261429/625000) (δ := 15253/1000000000) (ψ := -164193/1000000) 302 230
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t119 : ((-93751723429/10000000000000 : ℚ) : ℝ) ≤ stT302 119 := by
  have hc : ((-102271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93751723429/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-102271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c120 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((41057/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1067601/5000000) (δ := 303/20000000) (ψ := -164193/1000000) 302 230
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t120 : ((14989599261/250000000000 : ℚ) : ℝ) ≤ stT302 120 := by
  have hc : ((164203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14989599261/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((164203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c121 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-39047/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7307167/10000000) (δ := 379/25000000) (ψ := -164193/1000000) 302 231
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t121 : ((-35500912641/400000000000 : ℚ) : ℝ) ≤ stT302 121 := by
  have hc : ((-39051/40000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35500912641/400000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-39051/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c122 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((905917/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54657/500000) (δ := 15243/1000000000) (ψ := -164193/1000000) 302 231
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t122 : ((820087761669/10000000000000 : ℚ) : ℝ) ≤ stT302 122 := by
  have hc : ((905817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((820087761669/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((905817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c123 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-88299/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 633769/1250000) (δ := 379/25000000) (ψ := -164193/1000000) 302 231
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t123 : ((-7963459273/200000000000 : ℚ) : ℝ) ≤ stT302 123 := by
  have hc : ((-88319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7963459273/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-88319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c124 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-118353/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180977/400000) (δ := 15267/1000000000) (ψ := -164193/1000000) 302 232
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t124 : ((-106329090881/5000000000000 : ℚ) : ℝ) ≤ stT302 124 := by
  have hc : ((-118403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106329090881/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-118403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c125 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((408111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769943/5000000) (δ := 15267/1000000000) (ψ := -164193/1000000) 302 232
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t125 : ((364980776047/5000000000000 : ℚ) : ℝ) ≤ stT302 125 := by
  have hc : ((408061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364980776047/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((408061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c126 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-992899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7555877/10000000) (δ := 15267/1000000000) (ψ := -164193/1000000) 302 232
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t126 : ((-884634012129/10000000000000 : ℚ) : ℝ) ≤ stT302 126 := by
  have hc : ((-992999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-884634012129/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-992999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c127 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((80269/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272967/1250000) (δ := 7587/500000000) (ψ := -164193/1000000) 302 233
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t127 : ((35608043407/625000000000 : ℚ) : ℝ) ≤ stT302 127 := by
  have hc : ((160513/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35608043407/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((160513/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c128 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((18893/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93447/250000) (δ := 7587/500000000) (ψ := -164193/1000000) 302 233
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t128 : ((4169276111/625000000000 : ℚ) : ℝ) ≤ stT302 128 := by
  have hc : ((4717/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4169276111/625000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((4717/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c129 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-762399/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3047261/5000000) (δ := 7641/500000000) (ψ := -164193/1000000) 302 234
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t129 : ((-671343007049/10000000000000 : ℚ) : ℝ) ≤ stT302 129 := by
  have hc : ((-762499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-671343007049/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-762499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c130 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((248603/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66103/2500000) (δ := 7641/500000000) (ψ := -164193/1000000) 302 234
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t130 : ((54504330881/625000000000 : ℚ) : ℝ) ≤ stT302 130 := by
  have hc : ((124289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54504330881/625000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((124289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c131 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-18603/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5521077/10000000) (δ := 15121/1000000000) (ψ := -164193/1000000) 302 234
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t131 : ((-26010023109/500000000000 : ℚ) : ℝ) ≤ stT302 131 := by
  have hc : ((-148849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26010023109/500000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-148849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c132 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-102943/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4445413/10000000) (δ := 15189/1000000000) (ψ := -164193/1000000) 302 235
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t132 : ((-89643974277/5000000000000 : ℚ) : ℝ) ≤ stT302 132 := by
  have hc : ((-102993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89643974277/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-102993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c133 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((43853/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1252723/10000000) (δ := 15189/1000000000) (ψ := -164193/1000000) 302 235
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t133 : ((4752624429/62500000000 : ℚ) : ℝ) ≤ stT302 133 := by
  have hc : ((5481/6250 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4752624429/62500000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((5481/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c134 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-232321/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1727041/2500000) (δ := 30389/1000000000) (ψ := -164193/1000000) 302 235
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t134 : ((-100358253337/1250000000000 : ℚ) : ℝ) ≤ stT302 134 := by
  have hc : ((-116173/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100358253337/1250000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-116173/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c135 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((145959/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -796603/2500000) (δ := 239/15625000) (ψ := -164193/1000000) 302 236
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t135 : ((62789165879/2500000000000 : ℚ) : ℝ) ≤ stT302 135 := by
  have hc : ((145909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62789165879/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((145909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c136 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((578241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2385563/10000000) (δ := 15107/1000000000) (ψ := -164193/1000000) 302 236
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t136 : ((123937820593/2500000000000 : ℚ) : ℝ) ≤ stT302 136 := by
  have hc : ((578141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123937820593/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((578141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c137 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-199937/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1558239/2000000) (δ := 19/1250000) (ψ := -164193/1000000) 302 237
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t137 : ((-85417431303/1000000000000 : ℚ) : ℝ) ≤ stT302 137 := by
  have hc : ((-199957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85417431303/1000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-199957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c138 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((605723/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1150153/5000000) (δ := 15203/1000000000) (ψ := -164193/1000000) 302 237
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t138 : ((64442526561/1250000000000 : ℚ) : ℝ) ≤ stT302 138 := by
  have hc : ((605623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64442526561/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((605623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c139 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((76357/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157551/500000) (δ := 19/1250000) (ψ := -164193/1000000) 302 237
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t139 : ((4046492901/156250000000 : ℚ) : ℝ) ≤ stT302 139 := by
  have hc : ((19083/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4046492901/156250000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((19083/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c140 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-480013/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3572363/5000000) (δ := 15293/1000000000) (ψ := -164193/1000000) 302 238
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t140 : ((-81145528953/1000000000000 : ℚ) : ℝ) ≤ stT302 140 := by
  have hc : ((-480063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81145528953/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-480063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c141 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((759381/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1771089/10000000) (δ := 15293/1000000000) (ψ := -164193/1000000) 302 238
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t141 : ((639429253431/10000000000000 : ℚ) : ℝ) ≤ stT302 141 := by
  have hc : ((759281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((639429253431/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((759281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c142 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((144431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3564647/10000000) (δ := 15293/1000000000) (ψ := -164193/1000000) 302 238
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t142 : ((121119832911/10000000000000 : ℚ) : ℝ) ≤ stT302 142 := by
  have hc : ((144331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121119832911/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((144331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c143 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-45983/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1711257/2500000) (δ := 7593/500000000) (ψ := -164193/1000000) 302 239
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t143 : ((-9614285771/125000000000 : ℚ) : ℝ) ≤ stT302 143 := by
  have hc : ((-11497/12500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9614285771/125000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-11497/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c144 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((201491/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316747/2000000) (δ := 7593/500000000) (ψ := -164193/1000000) 302 239
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t144 : ((83944133089/1250000000000 : ℚ) : ℝ) ≤ stT302 144 := by
  have hc : ((100733/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83944133089/1250000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((100733/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c145 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((2281/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3641243/10000000) (δ := 15217/1000000000) (ψ := -164193/1000000) 302 239
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t145 : ((946302333/100000000000 : ℚ) : ℝ) ≤ stT302 145 := by
  have hc : ((2279/20000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((946302333/100000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((2279/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c146 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-924711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6877681/10000000) (δ := 121/8000000) (ψ := -164193/1000000) 302 240
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t146 : ((-382689566233/5000000000000 : ℚ) : ℝ) ≤ stT302 146 := by
  have hc : ((-924811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382689566233/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-924811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c147 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((192867/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1724127/10000000) (δ := 7639/500000000) (ψ := -164193/1000000) 302 240
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t147 : ((39763345453/625000000000 : ℚ) : ℝ) ≤ stT302 147 := by
  have hc : ((96421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39763345453/625000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((96421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c148 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((211371/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3394547/10000000) (δ := 121/8000000) (ψ := -164193/1000000) 302 240
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t148 : ((86831747187/5000000000000 : ℚ) : ℝ) ≤ stT302 148 := by
  have hc : ((211271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86831747187/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((211271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c149 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-968931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7229171/10000000) (δ := 15171/1000000000) (ψ := -164193/1000000) 302 241
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t149 : ((-24808162631/312500000000 : ℚ) : ℝ) ≤ stT302 149 := by
  have hc : ((-969031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24808162631/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-969031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c150 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((643587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2179051/10000000) (δ := 119/7812500) (ψ := -164193/1000000) 302 241
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t150 : ((32837785097/625000000000 : ℚ) : ℝ) ≤ stT302 150 := by
  have hc : ((643487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32837785097/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((643487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c151 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((52761/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1418811/5000000) (δ := 119/7812500) (ψ := -164193/1000000) 302 241
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t151 : ((21463048159/625000000000 : ℚ) : ℝ) ≤ stT302 151 := by
  have hc : ((105497/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21463048159/625000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((105497/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c152 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-499957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156423/200000) (δ := 15171/1000000000) (ψ := -164193/1000000) 302 241
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t152 : ((-101389919439/1250000000000 : ℚ) : ℝ) ≤ stT302 152 := by
  have hc : ((-500007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101389919439/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-500007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c153 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((77221/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -366997/1250000) (δ := 15139/1000000000) (ψ := -164193/1000000) 302 242
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t153 : ((15603325713/500000000000 : ℚ) : ℝ) ≤ stT302 153 := by
  have hc : ((77201/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15603325713/500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((77201/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c154 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((175419/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 991311/5000000) (δ := 477/31250000) (ψ := -164193/1000000) 302 242
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t154 : ((35334085967/625000000000 : ℚ) : ℝ) ≤ stT302 154 := by
  have hc : ((87697/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35334085967/625000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((87697/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c155 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-923439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85867/125000) (δ := 15139/1000000000) (ψ := -164193/1000000) 302 242
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t155 : ((-37090249779/500000000000 : ℚ) : ℝ) ≤ stT302 155 := by
  have hc : ((-923539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37090249779/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-923539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c156 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-22511/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1991637/5000000) (δ := 15157/1000000000) (ψ := -164193/1000000) 302 243
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t156 : ((-18103293651/10000000000000 : ℚ) : ℝ) ≤ stT302 156 := by
  have hc : ((-22611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18103293651/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-22611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c157 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((471973/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33641/400000) (δ := 15157/1000000000) (ψ := -164193/1000000) 302 243
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t157 : ((188317569689/2500000000000 : ℚ) : ℝ) ≤ stT302 157 := by
  have hc : ((471923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188317569689/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((471923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c158 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-631179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5634671/10000000) (δ := 15157/1000000000) (ψ := -164193/1000000) 302 243
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t158 : ((-251109529341/5000000000000 : ℚ) : ℝ) ≤ stT302 158 := by
  have hc : ((-631279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251109529341/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-631279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c159 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-525363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2654923/5000000) (δ := 15153/1000000000) (ψ := -164193/1000000) 302 244
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t159 : ((-104179870769/2500000000000 : ℚ) : ℝ) ≤ stT302 159 := by
  have hc : ((-525463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104179870769/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-525463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c160 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((243387/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288149/5000000) (δ := 15153/1000000000) (ψ := -164193/1000000) 302 244
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t160 : ((96197226489/1250000000000 : ℚ) : ℝ) ≤ stT302 160 := by
  have hc : ((121681/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96197226489/1250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((121681/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c161 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-80209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4127729/10000000) (δ := 61/4000000) (ψ := -164193/1000000) 302 244
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t161 : ((-63292406299/10000000000000 : ℚ) : ℝ) ≤ stT302 161 := by
  have hc : ((-80309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63292406299/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-80309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c162 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-116107/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3452637/5000000) (δ := 15143/1000000000) (ψ := -164193/1000000) 302 245
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t162 : ((-7298575053/100000000000 : ℚ) : ℝ) ≤ stT302 162 := by
  have hc : ((-232239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7298575053/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-232239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c163 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((618761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2259079/10000000) (δ := 763/50000000) (ψ := -164193/1000000) 302 245
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t163 : ((24228620743/500000000000 : ℚ) : ℝ) ≤ stT302 163 := by
  have hc : ((618661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24228620743/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((618661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c164 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((58699/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589663/2500000) (δ := 763/50000000) (ψ := -164193/1000000) 302 245
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t164 : ((11457090513/250000000000 : ℚ) : ℝ) ≤ stT302 164 := by
  have hc : ((58689/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11457090513/250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((58689/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c165 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-935093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6948297/10000000) (δ := 763/50000000) (ψ := -164193/1000000) 302 245
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t165 : ((-728046815307/10000000000000 : ℚ) : ℝ) ≤ stT302 165 := by
  have hc : ((-935193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-728046815307/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-935193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c166 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-27021/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -419773/1000000) (δ := 237/15625000) (ψ := -164193/1000000) 302 246
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t166 : ((-10495889973/1250000000000 : ℚ) : ℝ) ≤ stT302 166 := by
  have hc : ((-13523/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10495889973/1250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-13523/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c167 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((198187/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 539/16000) (δ := 3047/200000000) (ψ := -164193/1000000) 302 246
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t167 : ((153346182441/2000000000000 : ℚ) : ℝ) ≤ stT302 167 := by
  have hc : ((198167/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153346182441/2000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((198167/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c168 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-179373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4844301/10000000) (δ := 237/15625000) (ψ := -164193/1000000) 302 246
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t168 : ((-138427894691/5000000000000 : ℚ) : ℝ) ≤ stT302 168 := by
  have hc : ((-179423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138427894691/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-179423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c169 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-831809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -797861/1250000) (δ := 611/40000000) (ψ := -164193/1000000) 302 247
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t169 : ((-639930191979/10000000000000 : ℚ) : ℝ) ≤ stT302 169 := by
  have hc : ((-831909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-639930191979/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-831909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c170 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((716903/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -385723/2000000) (δ := 1891/125000000) (ψ := -164193/1000000) 302 247
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t170 : ((137440524023/2500000000000 : ℚ) : ℝ) ≤ stT302 170 := by
  have hc : ((716803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137440524023/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((716803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c171 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((270229/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156221/625000) (δ := 611/40000000) (ψ := -164193/1000000) 302 247
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t171 : ((206611014701/5000000000000 : ℚ) : ℝ) ≤ stT302 171 := by
  have hc : ((270179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206611014701/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((270179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c172 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-18567/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1380373/2000000) (δ := 1891/125000000) (ψ := -164193/1000000) 302 247
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t172 : ((-14158732517/200000000000 : ℚ) : ℝ) ≤ stT302 172 := by
  have hc : ((-18569/20000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14158732517/200000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-18569/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c173 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-19957/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553661/1250000) (δ := 15221/1000000000) (ψ := -164193/1000000) 302 248
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t173 : ((-7590315281/500000000000 : ℚ) : ℝ) ≤ stT302 173 := by
  have hc : ((-19967/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7590315281/500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-19967/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c174 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((999517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38847/5000000) (δ := 7591/500000000) (ψ := -164193/1000000) 302 248
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t174 : ((378828014433/5000000000000 : ℚ) : ℝ) ≤ stT302 174 := by
  have hc : ((999417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378828014433/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((999417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c175 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-128441/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 531123/1250000) (δ := 15221/1000000000) (ψ := -164193/1000000) 302 248
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t175 : ((-97167869589/10000000000000 : ℚ) : ℝ) ≤ stT302 175 := by
  have hc : ((-128541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97167869589/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-128541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c176 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-961387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7156989/10000000) (δ := 7557/500000000) (ψ := -164193/1000000) 302 249
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t176 : ((-724748709373/10000000000000 : ℚ) : ℝ) ≤ stT302 176 := by
  have hc : ((-961487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-724748709373/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-961487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c177 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((406913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287931/1000000) (δ := 7557/500000000) (ψ := -164193/1000000) 302 249
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t177 : ((152889682099/5000000000000 : ℚ) : ℝ) ≤ stT302 177 := by
  have hc : ((406813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152889682099/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((406813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c178 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((85269/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374209/10000000) (δ := 7557/500000000) (ψ := -164193/1000000) 302 249
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t178 : ((63904263529/1000000000000 : ℚ) : ℝ) ≤ stT302 178 := by
  have hc : ((85259/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63904263529/1000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((85259/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c179 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-621599/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2801973/5000000) (δ := 15289/1000000000) (ψ := -164193/1000000) 302 249
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t179 : ((-116170053441/2500000000000 : ℚ) : ℝ) ≤ stT302 179 := by
  have hc : ((-621699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116170053441/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-621699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c180 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-177301/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5897913/10000000) (δ := 15207/1000000000) (ψ := -164193/1000000) 302 250
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t180 : ((-16521374757/312500000000 : ℚ) : ℝ) ≤ stT302 180 := by
  have hc : ((-88663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16521374757/312500000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-88663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c181 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((77377/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857531/5000000) (δ := 15207/1000000000) (ψ := -164193/1000000) 302 250
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t181 : ((28753213449/500000000000 : ℚ) : ℝ) ≤ stT302 181 := by
  have hc : ((77367/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28753213449/500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((77367/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c182 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((558787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1222343/5000000) (δ := 15207/1000000000) (ψ := -164193/1000000) 302 250
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t182 : ((414126180063/10000000000000 : ℚ) : ℝ) ≤ stT302 182 := by
  have hc : ((558687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414126180063/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((558687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c183 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-873277/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6581709/10000000) (δ := 3799/250000000) (ψ := -164193/1000000) 302 250
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t183 : ((-322809746347/5000000000000 : ℚ) : ℝ) ≤ stT302 183 := by
  have hc : ((-873377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322809746347/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-873377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c184 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-420437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5011807/10000000) (δ := 15299/1000000000) (ψ := -164193/1000000) 302 251
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t184 : ((-31002408177/1000000000000 : ℚ) : ℝ) ≤ stT302 184 := by
  have hc : ((-420537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31002408177/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-420537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c185 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((466551/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -919631/10000000) (δ := 59/3906250) (ψ := -164193/1000000) 302 251
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t185 : ((171489033107/2500000000000 : ℚ) : ℝ) ≤ stT302 185 := by
  have hc : ((466501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171489033107/2500000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((466501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c186 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((38207/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3150423/10000000) (δ := 59/3906250) (ψ := -164193/1000000) 302 251
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t186 : ((11202217683/500000000000 : ℚ) : ℝ) ≤ stT302 186 := by
  have hc : ((76389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11202217683/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((76389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c187 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-120731/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7198733/10000000) (δ := 59/3906250) (ψ := -164193/1000000) 302 251
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t187 : ((-176592922951/2500000000000 : ℚ) : ℝ) ≤ stT302 187 := by
  have hc : ((-241487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176592922951/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-241487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c188 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-110207/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4482589/10000000) (δ := 1899/125000000) (ψ := -164193/1000000) 302 252
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t188 : ((-3216527461/200000000000 : ℚ) : ℝ) ≤ stT302 188 := by
  have hc : ((-110257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3216527461/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-110257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c189 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((196367/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238619/5000000) (δ := 15211/1000000000) (ψ := -164193/1000000) 302 252
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t189 : ((4463163657/62500000000 : ℚ) : ℝ) ≤ stT302 189 := by
  have hc : ((196347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4463163657/62500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((196347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c190 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((10453/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3506897/10000000) (δ := 15211/1000000000) (ψ := -164193/1000000) 302 252
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t190 : ((7578866403/625000000000 : ℚ) : ℝ) ≤ stT302 190 := by
  have hc : ((41787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7578866403/625000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((41787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c191 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-12353/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3735097/5000000) (δ := 15211/1000000000) (ψ := -164193/1000000) 302 252
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t191 : ((-1430276231/20000000000 : ℚ) : ℝ) ≤ stT302 191 := by
  have hc : ((-49417/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1430276231/20000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-49417/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c192 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-73383/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -859047/2000000) (δ := 7559/500000000) (ψ := -164193/1000000) 302 253
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t192 : ((-6624464363/625000000000 : ℚ) : ℝ) ≤ stT302 192 := by
  have hc : ((-73433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6624464363/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-73433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c193 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((988881/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373161/10000000) (δ := 7559/500000000) (ψ := -164193/1000000) 302 253
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t193 : ((142347879103/2000000000000 : ℚ) : ℝ) ≤ stT302 193 := by
  have hc : ((988781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142347879103/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((988781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c194 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((39663/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3528679/10000000) (δ := 7559/500000000) (ψ := -164193/1000000) 302 253
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t194 : ((7114604801/625000000000 : ℚ) : ℝ) ≤ stT302 194 := by
  have hc : ((19819/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7114604801/625000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((19819/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c195 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-984303/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1852609/2500000) (δ := 7559/500000000) (ψ := -164193/1000000) 302 253
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t195 : ((-140989150869/2000000000000 : ℚ) : ℝ) ≤ stT302 195 := by
  have hc : ((-984403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140989150869/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-984403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c196 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-101027/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4435627/10000000) (δ := 7589/500000000) (ψ := -164193/1000000) 302 254
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t196 : ((-36098943011/2500000000000 : ℚ) : ℝ) ≤ stT302 196 := by
  have hc : ((-101077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36098943011/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-101077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c197 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((485983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148339/2500000) (δ := 609/40000000) (ψ := -164193/1000000) 302 254
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t197 : ((34621268451/500000000000 : ℚ) : ℝ) ≤ stT302 197 := by
  have hc : ((485933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34621268451/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((485933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c198 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((34427/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645887/2000000) (δ := 7589/500000000) (ψ := -164193/1000000) 302 254
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t198 : ((48914636601/2500000000000 : ℚ) : ℝ) ≤ stT302 198 := by
  have hc : ((68829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48914636601/2500000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((68829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c199 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-946559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3516487/5000000) (δ := 7589/500000000) (ψ := -164193/1000000) 302 254
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t199 : ((-335534762619/5000000000000 : ℚ) : ℝ) ≤ stT302 199 := by
  have hc : ((-946659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335534762619/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-946659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c200 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-375953/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -611319/1250000) (δ := 15271/1000000000) (ψ := -164193/1000000) 302 255
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t200 : ((-265909708671/10000000000000 : ℚ) : ℝ) ≤ stT302 200 := by
  have hc : ((-376053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265909708671/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-376053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c201 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((450231/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -562457/5000000) (δ := 15271/1000000000) (ψ := -164193/1000000) 302 255
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t201 : ((63506583489/1000000000000 : ℚ) : ℝ) ≤ stT302 201 := by
  have hc : ((450181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63506583489/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((450181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c202 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((249319/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104877/400000) (δ := 3783/250000000) (ψ := -164193/1000000) 302 255
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t202 : ((175384920593/5000000000000 : ℚ) : ℝ) ≤ stT302 202 := by
  have hc : ((249269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175384920593/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((249269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c203 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-12883/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6350341/10000000) (δ := 15271/1000000000) (ψ := -164193/1000000) 302 255
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t203 : ((-144691163039/2500000000000 : ℚ) : ℝ) ≤ stT302 203 := by
  have hc : ((-206153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144691163039/2500000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-206153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c204 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-635167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88243/156250) (δ := 3791/250000000) (ψ := -164193/1000000) 302 256
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t204 : ((-444776472647/10000000000000 : ℚ) : ℝ) ≤ stT302 204 := by
  have hc : ((-635267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444776472647/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-635267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c205 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((88667/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -977801/5000000) (δ := 3791/250000000) (ψ := -164193/1000000) 302 256
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t205 : ((12383792487/250000000000 : ℚ) : ℝ) ≤ stT302 205 := by
  have hc : ((177309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12383792487/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((177309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c206 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((772929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1718379/10000000) (δ := 3791/250000000) (ψ := -164193/1000000) 302 256
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t206 : ((538455467657/10000000000000 : ℚ) : ℝ) ≤ stT302 206 := by
  have hc : ((772829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538455467657/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((772829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c207 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-136801/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2687271/5000000) (δ := 3791/250000000) (ψ := -164193/1000000) 302 256
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t207 : ((-47550387237/1250000000000 : ℚ) : ℝ) ≤ stT302 207 := by
  have hc : ((-68413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47550387237/1250000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-68413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c208 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-35777/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133897/200000) (δ := 1907/125000000) (ψ := -164193/1000000) 302 257
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t208 : ((-193825677/3125000000 : ℚ) : ℝ) ≤ stT302 208 := by
  have hc : ((-35781/40000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193825677/3125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-35781/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c209 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((334721/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3073719/10000000) (δ := 1907/125000000) (ψ := -164193/1000000) 302 257
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t209 : ((115731015197/5000000000000 : ℚ) : ℝ) ≤ stT302 209 := by
  have hc : ((334621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115731015197/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((334621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c210 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((488801/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530123/10000000) (δ := 15147/1000000000) (ψ := -164193/1000000) 302 257
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t210 : ((67453991763/1000000000000 : ℚ) : ℝ) ≤ stT302 210 := by
  have hc : ((488751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67453991763/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((488751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c211 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-75861/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2058413/5000000) (δ := 15147/1000000000) (ψ := -164193/1000000) 302 257
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t211 : ((-52293755269/10000000000000 : ℚ) : ℝ) ≤ stT302 211 := by
  have hc : ((-75961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52293755269/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-75961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c212 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-498879/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7686541/10000000) (δ := 1907/125000000) (ψ := -164193/1000000) 302 257
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t212 : ((-342665933987/5000000000000 : ℚ) : ℝ) ≤ stT302 212 := by
  have hc : ((-498929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342665933987/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-498929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c213 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-214901/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4468467/10000000) (δ := 7627/500000000) (ψ := -164193/1000000) 302 258
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t213 : ((-147316320189/10000000000000 : ℚ) : ℝ) ≤ stT302 213 := by
  have hc : ((-215001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147316320189/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-215001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c214 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((931293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932123/10000000) (δ := 15149/1000000000) (ψ := -164193/1000000) 302 258
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t214 : ((127309913381/2000000000000 : ℚ) : ℝ) ≤ stT302 214 := by
  have hc : ((931193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127309913381/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((931193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c215 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((255231/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2587687/10000000) (δ := 15149/1000000000) (ψ := -164193/1000000) 302 258
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t215 : ((87015955457/2500000000000 : ℚ) : ℝ) ≤ stT302 215 := by
  have hc : ((255181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87015955457/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((255181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c216 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-11899/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6091189/10000000) (δ := 15149/1000000000) (ψ := -164193/1000000) 302 258
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t216 : ((-64778474663/1250000000000 : ℚ) : ℝ) ≤ stT302 216 := by
  have hc : ((-190409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64778474663/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-190409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c217 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-771379/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1225901/2000000) (δ := 7621/500000000) (ψ := -164193/1000000) 302 259
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t217 : ((-104742932351/2000000000000 : ℚ) : ℝ) ≤ stT302 217 := by
  have hc : ((-771479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104742932351/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-771479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c218 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((242997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2658241/10000000) (δ := 15161/1000000000) (ψ := -164193/1000000) 302 259
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t218 : ((32908871779/1000000000000 : ℚ) : ℝ) ≤ stT302 218 := by
  have hc : ((242947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32908871779/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((242947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c219 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((949591/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 797167/10000000) (δ := 7621/500000000) (ψ := -164193/1000000) 302 259
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t219 : ((641606199867/10000000000000 : ℚ) : ℝ) ≤ stT302 219 := by
  have hc : ((949491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((641606199867/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((949491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c220 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-24721/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1059199/2500000) (δ := 7621/500000000) (ψ := -164193/1000000) 302 259
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t220 : ((-83401911/10000000000 : ℚ) : ℝ) ≤ stT302 220 := by
  have hc : ((-24741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83401911/10000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-24741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c221 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-498509/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 957609/1250000) (δ := 7621/500000000) (ψ := -164193/1000000) 302 259
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t221 : ((-335367178207/5000000000000 : ℚ) : ℝ) ≤ stT302 221 := by
  have hc : ((-498559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335367178207/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-498559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c222 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-280803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579821/1250000) (δ := 3027/200000000) (ψ := -164193/1000000) 302 260
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t222 : ((-188530014771/10000000000000 : ℚ) : ℝ) ≤ stT302 222 := by
  have hc : ((-280903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188530014771/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-280903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c223 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((878483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77831/625000) (δ := 3027/200000000) (ψ := -164193/1000000) 302 260
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t223 : ((588208297567/10000000000000 : ℚ) : ℝ) ≤ stT302 223 := by
  have hc : ((878383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((588208297567/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((878383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c224 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((164409/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2132801/10000000) (δ := 3817/250000000) (ψ := -164193/1000000) 302 260
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t224 : ((3432301961/78125000000 : ℚ) : ℝ) ≤ stT302 224 := by
  have hc : ((10274/15625 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3432301961/78125000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((10274/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c225 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-293583/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5495873/10000000) (δ := 3817/250000000) (ψ := -164193/1000000) 302 260
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t225 : ((-195755431211/5000000000000 : ℚ) : ℝ) ≤ stT302 225 := by
  have hc : ((-293633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195755431211/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-293633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c226 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-184523/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1372801/2000000) (δ := 243/8000000) (ψ := -164193/1000000) 302 261
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t226 : ((-122756342713/2000000000000 : ℚ) : ℝ) ≤ stT302 226 := by
  have hc : ((-184543/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122756342713/2000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-184543/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c227 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((39469/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3530643/10000000) (δ := 3807/250000000) (ψ := -164193/1000000) 302 261
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t227 : ((6544972503/625000000000 : ℚ) : ℝ) ≤ stT302 227 := by
  have hc : ((9861/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6544972503/625000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((9861/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c228 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((124551/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42393/2000000) (δ := 3807/250000000) (ψ := -164193/1000000) 302 261
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t228 : ((82477614241/1250000000000 : ℚ) : ℝ) ≤ stT302 228 := by
  have hc : ((249077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82477614241/1250000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((249077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c229 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((327739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3092217/10000000) (δ := 3807/250000000) (ψ := -164193/1000000) 302 261
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t229 : ((108254874351/5000000000000 : ℚ) : ℝ) ≤ stT302 229 := by
  have hc : ((327639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108254874351/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((327639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c230 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-831607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6381979/10000000) (δ := 607/40000000) (ψ := -164193/1000000) 302 261
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t230 : ((-548411793367/10000000000000 : ℚ) : ℝ) ≤ stT302 230 := by
  have hc : ((-831707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548411793367/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-831707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c231 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-150177/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1512623/2500000) (δ := 15283/1000000000) (ψ := -164193/1000000) 302 262
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t231 : ((-3088200517/62500000000 : ℚ) : ℝ) ≤ stT302 231 := by
  have hc : ((-150197/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3088200517/62500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-150197/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c232 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((439569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1394597/5000000) (δ := 15283/1000000000) (ψ := -164193/1000000) 302 262
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t232 : ((72131365377/2500000000000 : ℚ) : ℝ) ≤ stT302 232 := by
  have hc : ((439469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72131365377/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((439469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c233 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((122907/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57267/1250000) (δ := 189/12500000) (ψ := -164193/1000000) 302 262
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t233 : ((161021535469/2500000000000 : ℚ) : ℝ) ≤ stT302 233 := by
  have hc : ((245789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161021535469/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((245789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c234 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((94027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147663/400000) (δ := 15283/1000000000) (ψ := -164193/1000000) 302 262
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t234 : ((1535048961/250000000000 : ℚ) : ℝ) ≤ stT302 234 := by
  have hc : ((93927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1535048961/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((93927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c235 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-929731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6911197/10000000) (δ := 15283/1000000000) (ψ := -164193/1000000) 302 262
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t235 : ((-606555726399/10000000000000 : ℚ) : ℝ) ≤ stT302 235 := by
  have hc : ((-929831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-606555726399/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-929831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c236 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-308737/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -559081/1000000) (δ := 1519/100000000) (ψ := -164193/1000000) 302 263
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t236 : ((-40200670743/1000000000000 : ℚ) : ℝ) ≤ stT302 236 := by
  have hc : ((-308787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40200670743/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-308787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c237 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((57403/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -599611/2500000) (δ := 15213/1000000000) (ψ := -164193/1000000) 302 263
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t237 : ((37280713617/1000000000000 : ℚ) : ℝ) ≤ stT302 237 := by
  have hc : ((57393/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37280713617/1000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((57393/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c238 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((475831/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195121/2500000) (δ := 1519/100000000) (ψ := -164193/1000000) 302 263
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t238 : ((308402671543/5000000000000 : ℚ) : ℝ) ≤ stT302 238 := by
  have hc : ((475781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308402671543/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((475781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c239 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-7653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3946123/10000000) (δ := 15213/1000000000) (ψ := -164193/1000000) 302 263
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t239 : ((-5015004791/10000000000000 : ℚ) : ℝ) ≤ stT302 239 := by
  have hc : ((-7753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5015004791/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-7753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c240 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-238673/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141971/200000) (δ := 15213/1000000000) (ψ := -164193/1000000) 302 263
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t240 : ((-38519770401/625000000000 : ℚ) : ℝ) ≤ stT302 240 := by
  have hc : ((-119349/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38519770401/625000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-119349/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c241 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-578797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5470123/10000000) (δ := 7553/500000000) (ψ := -164193/1000000) 302 264
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t241 : ((-372900554829/10000000000000 : ℚ) : ℝ) ≤ stT302 241 := by
  have hc : ((-578897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-372900554829/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-578897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c242 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((591783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2343819/10000000) (δ := 7553/500000000) (ψ := -164193/1000000) 302 264
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t242 : ((47543504099/1250000000000 : ℚ) : ℝ) ≤ stT302 242 := by
  have hc : ((591683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47543504099/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((591683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c243 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((952993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30783/400000) (δ := 15297/1000000000) (ψ := -164193/1000000) 302 264
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t243 : ((1222561719/20000000000 : ℚ) : ℝ) ≤ stT302 243 := by
  have hc : ((952893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1222561719/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((952893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c244 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((22711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3870209/10000000) (δ := 15297/1000000000) (ψ := -164193/1000000) 302 264
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t244 : ((1809400053/1250000000000 : ℚ) : ℝ) ≤ stT302 244 := by
  have hc : ((22611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1809400053/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((22611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c245 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-936479/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6958121/10000000) (δ := 30297/1000000000) (ψ := -164193/1000000) 302 264
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t245 : ((-598358781783/10000000000000 : ℚ) : ℝ) ≤ stT302 245 := by
  have hc : ((-936579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-598358781783/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-936579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c246 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-160861/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5674463/10000000) (δ := 3801/250000000) (ψ := -164193/1000000) 302 265
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t246 : ((-51288606611/1250000000000 : ℚ) : ℝ) ≤ stT302 246 := by
  have hc : ((-80443/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51288606611/1250000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-80443/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c247 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((502221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2611579/10000000) (δ := 3801/250000000) (ψ := -164193/1000000) 302 265
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t247 : ((79872889591/2500000000000 : ℚ) : ℝ) ≤ stT302 247 := by
  have hc : ((502121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79872889591/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((502121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c248 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((984627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 438923/10000000) (δ := 3801/250000000) (ψ := -164193/1000000) 302 265
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t248 : ((125034929/2000000000 : ℚ) : ℝ) ≤ stT302 248 := by
  have hc : ((984527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125034929/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((984527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c249 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((8949/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1738559/5000000) (δ := 15199/1000000000) (ψ := -164193/1000000) 302 265
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t249 : ((88562929/7812500000 : ℚ) : ℝ) ≤ stT302 249 := by
  have hc : ((559/3125 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88562929/7812500000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((559/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c250 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-171511/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3251617/5000000) (δ := 3801/250000000) (ψ := -164193/1000000) 302 265
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t250 : ((-13560726267/250000000000 : ℚ) : ℝ) ≤ stT302 250 := by
  have hc : ((-171531/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13560726267/250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-171531/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c251 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-786741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619077/1000000) (δ := 3823/250000000) (ψ := -164193/1000000) 302 266
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t251 : ((-99330020999/2000000000000 : ℚ) : ℝ) ≤ stT302 251 := by
  have hc : ((-786841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99330020999/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-786841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c252 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((290999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1594407/5000000) (δ := 15111/1000000000) (ψ := -164193/1000000) 302 266
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t252 : ((9162445803/500000000000 : ℚ) : ℝ) ≤ stT302 252 := by
  have hc : ((290899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9162445803/500000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((290899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c253 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((996843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24839/1250000) (δ := 15111/1000000000) (ψ := -164193/1000000) 302 266
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t253 : ((313323171821/5000000000000 : ℚ) : ℝ) ≤ stT302 253 := by
  have hc : ((996743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313323171821/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((996743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c254 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((6922/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694903/2500000) (δ := 15111/1000000000) (ψ := -164193/1000000) 302 266
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t254 : ((13895241957/500000000000 : ℚ) : ℝ) ≤ stT302 254 := by
  have hc : ((110727/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13895241957/500000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((110727/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c255 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-10393/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5746233/10000000) (δ := 3823/250000000) (ψ := -164193/1000000) 302 266
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t255 : ((-4165974337/100000000000 : ℚ) : ℝ) ≤ stT302 255 := by
  have hc : ((-166313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4165974337/100000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-166313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c256 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-943121/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1401347/2000000) (δ := 7609/500000000) (ψ := -164193/1000000) 302 267
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t256 : ((-589514068221/10000000000000 : ℚ) : ℝ) ≤ stT302 256 := by
  have hc : ((-943221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-589514068221/10000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-943221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c257 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-54493/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1015823/2500000) (δ := 7609/500000000) (ψ := -164193/1000000) 302 267
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t257 : ((-34054185319/10000000000000 : ℚ) : ℝ) ≤ stT302 257 := by
  have hc : ((-54593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34054185319/10000000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-54593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c258 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((899357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181/1600) (δ := 3037/200000000) (ψ := -164193/1000000) 302 267
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t258 : ((139963057251/2500000000000 : ℚ) : ℝ) ≤ stT302 258 := by
  have hc : ((899257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139963057251/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((899257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c259 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((754577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 447367/2500000) (δ := 7609/500000000) (ψ := -164193/1000000) 302 267
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t259 : ((468808619013/10000000000000 : ℚ) : ℝ) ≤ stT302 259 := by
  have hc : ((754477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468808619013/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((754477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c260 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-60779/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587367/1250000) (δ := 7609/500000000) (ψ := -164193/1000000) 302 267
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t260 : ((-18852979513/1000000000000 : ℚ) : ℝ) ≤ stT302 260 := by
  have hc : ((-60799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18852979513/1000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-60799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c261 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-994731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 759723/1000000) (δ := 7609/500000000) (ψ := -164193/1000000) 302 267
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t261 : ((-123157093307/2000000000000 : ℚ) : ℝ) ≤ stT302 261 := by
  have hc : ((-994831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123157093307/2000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-994831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c262 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-495681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2611769/5000000) (δ := 22663/500000000) (ψ := -164193/1000000) 302 268
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t262 : ((-306294989143/10000000000000 : ℚ) : ℝ) ≤ stT302 262 := by
  have hc : ((-495781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306294989143/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-495781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c263 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((590639/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1173683/5000000) (δ := 15277/1000000000) (ψ := -164193/1000000) 302 268
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t263 : ((182070850707/5000000000000 : ℚ) : ℝ) ≤ stT302 263 := by
  have hc : ((590539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182070850707/5000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((590539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c264 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((122327/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103587/2000000) (δ := 22663/500000000) (ψ := -164193/1000000) 302 268
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t264 : ((150558630453/2500000000000 : ℚ) : ℝ) ≤ stT302 264 := by
  have hc : ((244629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150558630453/2500000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((244629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c265 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((55009/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3372363/10000000) (δ := 15277/1000000000) (ψ := -164193/1000000) 302 268
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t265 : ((844409907/62500000000 : ℚ) : ℝ) ≤ stT302 265 := by
  have hc : ((6873/31250 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((844409907/62500000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((6873/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c266 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-198237/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6216071/10000000) (δ := 7563/500000000) (ψ := -164193/1000000) 302 268
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t266 : ((-3039059067/62500000000 : ℚ) : ℝ) ≤ stT302 266 := by
  have hc : ((-99131/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3039059067/62500000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-99131/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c267 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-887903/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3329453/5000000) (δ := 1517/100000000) (ψ := -164193/1000000) 302 269
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t267 : ((-543449843973/10000000000000 : ℚ) : ℝ) ≤ stT302 267 := by
  have hc : ((-888003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543449843973/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-888003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c268 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((36193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3836489/10000000) (δ := 15233/1000000000) (ψ := -164193/1000000) 302 269
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t268 : ((22047300771/10000000000000 : ℚ) : ℝ) ≤ stT302 268 := by
  have hc : ((36093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22047300771/10000000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((36093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c269 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((91719/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1024567/10000000) (δ := 15233/1000000000) (ψ := -164193/1000000) 302 269
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t269 : ((5591589439/100000000000 : ℚ) : ℝ) ≤ stT302 269 := by
  have hc : ((91709/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5591589439/100000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((91709/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c270 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((757857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 222117/1250000) (δ := 15233/1000000000) (ψ := -164193/1000000) 302 269
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t270 : ((23057787753/500000000000 : ℚ) : ℝ) ≤ stT302 270 := by
  have hc : ((757757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23057787753/500000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((757757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c271 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-6341/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 913619/2000000) (δ := 1517/100000000) (ψ := -164193/1000000) 302 269
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t271 : ((-7706806959/500000000000 : ℚ) : ℝ) ≤ stT302 271 := by
  have hc : ((-12687/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).2
  have h0 : (0:ℝ) ≤ ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7706806959/500000000000 : ℚ) : ℝ)
      = ((607457/10000000 : ℚ) : ℝ) * ((-12687/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c272 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-489831/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7348911/10000000) (δ := 1517/100000000) (ψ := -164193/1000000) 302 269
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t272 : ((-14851722277/250000000000 : ℚ) : ℝ) ≤ stT302 272 := by
  have hc : ((-489881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14851722277/250000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-489881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c273 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-24669/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5588429/10000000) (δ := 15263/1000000000) (ψ := -164193/1000000) 302 270
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t273 : ((-3733197611/100000000000 : ℚ) : ℝ) ≤ stT302 273 := by
  have hc : ((-24673/40000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3733197611/100000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-24673/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c274 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((42563/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2827847/10000000) (δ := 15263/1000000000) (ψ := -164193/1000000) 302 270
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t274 : ((12853601733/500000000000 : ℚ) : ℝ) ≤ stT302 274 := by
  have hc : ((42553/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).1
  have hw2 : ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((302061/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12853601733/500000000000 : ℚ) : ℝ)
      = ((302061/5000000 : ℚ) : ℝ) * ((42553/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c275 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((6247/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77457/10000000) (δ := 757/50000000) (ψ := -164193/1000000) 302 270
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t275 : ((15066806181/250000000000 : ℚ) : ℝ) ≤ stT302 275 := by
  have hc : ((49971/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15066806181/250000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((49971/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c276 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((96863/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1331521/5000000) (δ := 757/50000000) (ψ := -164193/1000000) 302 270
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t276 : ((58292610147/2000000000000 : ℚ) : ℝ) ≤ stT302 276 := by
  have hc : ((96843/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58292610147/2000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((96843/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c277 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-276793/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107873/200000) (δ := 15263/1000000000) (ψ := -164193/1000000) 302 270
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t277 : ((-83169450903/2500000000000 : ℚ) : ℝ) ≤ stT302 277 := by
  have hc : ((-276843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83169450903/2500000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-276843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c278 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-994581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1518719/2000000) (δ := 3789/250000000) (ψ := -164193/1000000) 302 271
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t278 : ((-596570871241/10000000000000 : ℚ) : ℝ) ≤ stT302 278 := by
  have hc : ((-994681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596570871241/10000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-994681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c279 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-373037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1220673/2500000) (δ := 3789/250000000) (ψ := -164193/1000000) 302 271
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t279 : ((-44678304969/2000000000000 : ℚ) : ℝ) ≤ stT302 279 := by
  have hc : ((-373137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44678304969/2000000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-373137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c280 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((5143/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2181377/10000000) (δ := 15247/1000000000) (ψ := -164193/1000000) 302 271
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t280 : ((7682626777/200000000000 : ℚ) : ℝ) ≤ stT302 280 := by
  have hc : ((25711/40000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7682626777/200000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((25711/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c281 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((61203/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255099/5000000) (δ := 15247/1000000000) (ψ := -164193/1000000) 302 271
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t281 : ((146027440063/2500000000000 : ℚ) : ℝ) ≤ stT302 281 := by
  have hc : ((244787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146027440063/2500000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((244787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c282 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((3621/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159613/500000) (δ := 15247/1000000000) (ψ := -164193/1000000) 302 271
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t282 : ((8622114189/500000000000 : ℚ) : ℝ) ≤ stT302 282 := by
  have hc : ((14479/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8622114189/500000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((14479/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c283 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-699807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5864809/10000000) (δ := 15247/1000000000) (ψ := -164193/1000000) 302 271
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t283 : ((-416052017173/10000000000000 : ℚ) : ℝ) ≤ stT302 283 := by
  have hc : ((-699907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416052017173/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-699907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c284 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-240969/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112187/156250) (δ := 15249/1000000000) (ψ := -164193/1000000) 302 272
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t284 : ((-71501835327/1250000000000 : ℚ) : ℝ) ≤ stT302 284 := by
  have hc : ((-120497/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71501835327/1250000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-120497/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c285 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-118701/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2263109/5000000) (δ := 7577/500000000) (ψ := -164193/1000000) 302 272
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t285 : ((-70342036099/5000000000000 : ℚ) : ℝ) ≤ stT302 285 := by
  have hc : ((-118751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70342036099/5000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-118751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c286 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((145973/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23521/125000) (δ := 15249/1000000000) (ψ := -164193/1000000) 302 272
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t286 : ((5393985021/125000000000 : ℚ) : ℝ) ≤ stT302 286 := by
  have hc : ((145953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5393985021/125000000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((145953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c287 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((954913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188393/2500000) (δ := 15249/1000000000) (ψ := -164193/1000000) 302 272
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t287 : ((563607972453/10000000000000 : ℚ) : ℝ) ≤ stT302 287 := by
  have hc : ((954813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563607972453/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((954813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c288 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((108603/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3379613/10000000) (δ := 15249/1000000000) (ψ := -164193/1000000) 302 272
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t288 : ((12793079603/1000000000000 : ℚ) : ℝ) ≤ stT302 288 := by
  have hc : ((108553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12793079603/1000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((108553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c289 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-736473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2998297/5000000) (δ := 15249/1000000000) (ψ := -164193/1000000) 302 272
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t289 : ((-108319688807/2500000000000 : ℚ) : ℝ) ≤ stT302 289 := by
  have hc : ((-736573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108319688807/2500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-736573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c290 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-14926/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1775843/2500000) (δ := 7631/500000000) (ψ := -164193/1000000) 302 273
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t290 : ((-140252450861/2500000000000 : ℚ) : ℝ) ≤ stT302 290 := by
  have hc : ((-238841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140252450861/2500000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-238841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c291 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-22893/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1126109/2500000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 273
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t291 : ((-13425990533/1000000000000 : ℚ) : ℝ) ≤ stT302 291 := by
  have hc : ((-22903/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13425990533/1000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-22903/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c292 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((360437/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1914333/10000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 273
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t292 : ((42180054867/1000000000000 : ℚ) : ℝ) ≤ stT302 292 := by
  have hc : ((360387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42180054867/1000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((360387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c293 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((482317/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 666861/10000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 273
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t293 : ((140871637501/2500000000000 : ℚ) : ℝ) ≤ stT302 293 := by
  have hc : ((482267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140871637501/2500000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((482267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c294 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((5433/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619611/5000000) (δ := 7631/500000000) (ψ := -164193/1000000) 302 273
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t294 : ((3167418941/200000000000 : ℚ) : ℝ) ≤ stT302 294 := by
  have hc : ((5431/20000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3167418941/200000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((5431/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c295 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-136381/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58029/100000) (δ := 7631/500000000) (ψ := -164193/1000000) 302 273
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t295 : ((-79415799423/2000000000000 : ℚ) : ℝ) ≤ stT302 295 := by
  have hc : ((-136401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79415799423/2000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-136401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c296 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-489877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1837517/2500000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 274
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t296 : ((-284764679553/5000000000000 : ℚ) : ℝ) ≤ stT302 296 := by
  have hc : ((-489927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284764679553/5000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-489927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c297 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-85883/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30023/62500) (δ := 7617/500000000) (ψ := -164193/1000000) 302 274
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t297 : ((-12462222543/625000000000 : ℚ) : ℝ) ≤ stT302 297 := by
  have hc : ((-21477/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12462222543/625000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-21477/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c298 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((77077/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1132949/5000000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 274
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t298 : ((22321115909/625000000000 : ℚ) : ℝ) ≤ stT302 298 := by
  have hc : ((154129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22321115909/625000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((154129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c299 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((497227/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 263427/10000000) (δ := 7617/500000000) (ψ := -164193/1000000) 302 274
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t299 : ((143762209789/2500000000000 : ℚ) : ℝ) ≤ stT302 299 := by
  have hc : ((497177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143762209789/2500000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((497177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c300 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((27583/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2784297/10000000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 274
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t300 : ((1273714929/50000000000 : ℚ) : ℝ) ≤ stT302 300 := by
  have hc : ((110307/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1273714929/50000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((110307/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c301 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-520911/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2648393/5000000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 274
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t301 : ((-300306051301/10000000000000 : ℚ) : ℝ) ≤ stT302 301 := by
  have hc : ((-521011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300306051301/10000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-521011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c302 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-39991/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 780097/1000000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 274
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t302 : ((-1150728141/20000000000 : ℚ) : ℝ) ≤ stT302 302 := by
  have hc : ((-7999/8000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1150728141/20000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-7999/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c303 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-55939/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2705557/5000000) (δ := 3819/250000000) (ψ := -164193/1000000) 302 275
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t303 : ((-6428372253/200000000000 : ℚ) : ℝ) ≤ stT302 303 := by
  have hc : ((-55949/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6428372253/200000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-55949/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c304 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((390717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -584693/2000000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 275
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t304 : ((224034083563/10000000000000 : ℚ) : ℝ) ≤ stT302 304 := by
  have hc : ((390617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224034083563/10000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((390617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c305 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((984267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88809/2000000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 275
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t305 : ((281766027933/5000000000000 : ℚ) : ℝ) ≤ stT302 305 := by
  have hc : ((984167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281766027933/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((984167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c306 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((688811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 506843/2500000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 275
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t306 : ((393709218971/10000000000000 : ℚ) : ℝ) ≤ stT302 306 := by
  have hc : ((688711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((393709218971/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((688711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c307 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-3493/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 898127/2000000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 275
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t307 : ((-31911282403/2500000000000 : ℚ) : ℝ) ≤ stT302 307 := by
  have hc : ((-55913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31911282403/2500000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-55913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c308 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-29211/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1389179/2000000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 275
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t308 : ((-133170368539/2500000000000 : ℚ) : ℝ) ≤ stT302 308 := by
  have hc : ((-233713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133170368539/2500000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-233713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c309 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-81637/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -394671/625000) (δ := 761/50000000) (ψ := -164193/1000000) 302 276
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t309 : ((-46447427007/1000000000000 : ℚ) : ℝ) ≤ stT302 309 := by
  have hc : ((-81647/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46447427007/1000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-81647/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c310 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((10331/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3875331/10000000) (δ := 761/50000000) (ψ := -164193/1000000) 302 276
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t310 : ((5839207041/5000000000000 : ℚ) : ℝ) ≤ stT302 310 := by
  have hc : ((10281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5839207041/5000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((10281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c311 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((837841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -721851/5000000) (δ := 15183/1000000000) (ψ := -164193/1000000) 302 276
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t311 : ((475038520827/10000000000000 : ℚ) : ℝ) ≤ stT302 311 := by
  have hc : ((837741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475038520827/10000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((837741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c312 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((924147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 979999/10000000) (δ := 15183/1000000000) (ψ := -164193/1000000) 302 276
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t312 : ((261569060243/5000000000000 : ℚ) : ℝ) ≤ stT302 312 := by
  have hc : ((924047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261569060243/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((924047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c313 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((210803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3395999/10000000) (δ := 15183/1000000000) (ψ := -164193/1000000) 302 276
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t313 : ((119096288799/10000000000000 : ℚ) : ℝ) ≤ stT302 313 := by
  have hc : ((210703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119096288799/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((210703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c314 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-341157/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2902149/5000000) (δ := 15183/1000000000) (ψ := -164193/1000000) 302 276
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t314 : ((-192554369931/5000000000000 : ℚ) : ℝ) ≤ stT302 314 := by
  have hc : ((-341207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192554369931/5000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-341207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c315 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-990161/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -468937/625000) (δ := 15113/1000000000) (ψ := -164193/1000000) 302 277
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t315 : ((-557949687057/10000000000000 : ℚ) : ℝ) ≤ stT302 315 := by
  have hc : ((-990261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557949687057/10000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-990261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c316 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-11393/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -638743/1250000) (δ := 15113/1000000000) (ψ := -164193/1000000) 302 277
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t316 : ((-801308769/31250000000 : ℚ) : ℝ) ≤ stT302 316 := by
  have hc : ((-22791/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-801308769/31250000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-22791/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c317 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((92531/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2724521/10000000) (δ := 1529/100000000) (ψ := -164193/1000000) 302 277
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t317 : ((10391853141/400000000000 : ℚ) : ℝ) ≤ stT302 317 := by
  have hc : ((92511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10391853141/400000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((92511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c318 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((495203/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -346573/10000000) (δ := 1529/100000000) (ψ := -164193/1000000) 302 277
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t318 : ((69416984529/1250000000000 : ℚ) : ℝ) ≤ stT302 318 := by
  have hc : ((495153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69416984529/1250000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((495153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c319 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((137959/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 252997/1250000) (δ := 1529/100000000) (ψ := -164193/1000000) 302 277
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t319 : ((19307735647/500000000000 : ℚ) : ℝ) ≤ stT302 319 := by
  have hc : ((137939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19307735647/500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((137939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c320 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-182957/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175479/400000) (δ := 1529/100000000) (ψ := -164193/1000000) 302 277
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t320 : ((-102331974969/10000000000000 : ℚ) : ℝ) ≤ stT302 320 := by
  have hc : ((-183057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102331974969/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-183057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c321 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-36113/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3371363/5000000) (δ := 1529/100000000) (ψ := -164193/1000000) 302 277
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t321 : ((-10079279541/200000000000 : ℚ) : ℝ) ≤ stT302 321 := by
  have hc : ((-36117/40000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10079279541/200000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-36117/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c322 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-440023/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3308443/5000000) (δ := 7603/500000000) (ψ := -164193/1000000) 302 278
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t322 : ((-245243441367/5000000000000 : ℚ) : ℝ) ≤ stT302 322 := by
  have hc : ((-440073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245243441367/5000000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-440073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c323 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-17383/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2137891/5000000) (δ := 7603/500000000) (ψ := -164193/1000000) 302 278
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t323 : ((-3871646853/500000000000 : ℚ) : ℝ) ≤ stT302 323 := by
  have hc : ((-34791/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3871646853/500000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-34791/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c324 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((713181/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -970963/5000000) (δ := 7603/500000000) (ψ := -164193/1000000) 302 278
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t324 : ((79231142991/2000000000000 : ℚ) : ℝ) ≤ stT302 324 := by
  have hc : ((713081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79231142991/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((713081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c325 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((197637/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192341/5000000) (δ := 7603/500000000) (ψ := -164193/1000000) 302 278
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t325 : ((1096181499/20000000000 : ℚ) : ℝ) ≤ stT302 325 := by
  have hc : ((197617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1096181499/20000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((197617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c326 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((58731/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2704193/10000000) (δ := 7603/500000000) (ψ := -164193/1000000) 302 278
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t326 : ((8130280947/312500000000 : ℚ) : ℝ) ≤ stT302 326 := by
  have hc : ((117437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8130280947/312500000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((117437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c327 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-211089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5016607/10000000) (δ := 7603/500000000) (ψ := -164193/1000000) 302 278
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t327 : ((-58380144639/2500000000000 : ℚ) : ℝ) ≤ stT302 327 := by
  have hc : ((-211139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58380144639/2500000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-211139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c328 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-195489/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3661/5000) (δ := 15197/1000000000) (ψ := -164193/1000000) 302 278
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t328 : ((-53975929211/1000000000000 : ℚ) : ℝ) ≤ stT302 328 := by
  have hc : ((-195509/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53975929211/1000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-195509/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c329 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-380311/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1521917/2500000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 279
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t329 : ((-104849932899/2500000000000 : ℚ) : ℝ) ≤ stT302 329 := by
  have hc : ((-380361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104849932899/2500000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-380361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c330 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((10449/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3796319/10000000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 279
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t330 : ((5740966349/2000000000000 : ℚ) : ℝ) ≤ stT302 330 := by
  have hc : ((10429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5740966349/2000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((10429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c331 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((164527/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302383/2000000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 279
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t331 : ((90421108043/2000000000000 : ℚ) : ℝ) ≤ stT302 331 := by
  have hc : ((164507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90421108043/2000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((164507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c332 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((14898/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382809/5000000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 279
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t332 : ((130807643603/2500000000000 : ℚ) : ℝ) ≤ stT302 332 := by
  have hc : ((238343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130807643603/2500000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((238343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c333 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((174397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75907/250000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 279
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t333 : ((23885364653/1250000000000 : ℚ) : ℝ) ≤ stT302 333 := by
  have hc : ((174347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23885364653/1250000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((174347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c334 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-522059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1325037/2500000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 279
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t334 : ((-35714109123/1250000000000 : ℚ) : ℝ) ≤ stT302 334 := by
  have hc : ((-522159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35714109123/1250000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-522159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c335 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-496483/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 472331/625000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 279
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t335 : ((-271285273347/5000000000000 : ℚ) : ℝ) ≤ stT302 335 := by
  have hc : ((-496533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271285273347/5000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-496533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c336 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-709881/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2950157/5000000) (δ := 3803/250000000) (ψ := -164193/1000000) 302 280
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t336 : ((-77465316929/2000000000000 : ℚ) : ℝ) ≤ stT302 336 := by
  have hc : ((-709981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77465316929/2000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-709981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c337 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((13493/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -731321/2000000) (δ := 3803/250000000) (ψ := -164193/1000000) 302 280
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t337 : ((7343286687/1250000000000 : ℚ) : ℝ) ≤ stT302 337 := by
  have hc : ((26961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7343286687/1250000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((26961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c338 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((843061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44363/312500) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 280
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t338 : ((57313761351/1250000000000 : ℚ) : ℝ) ≤ stT302 338 := by
  have hc : ((842961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57313761351/1250000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((842961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c339 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((947857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 810881/10000000) (δ := 3803/250000000) (ψ := -164193/1000000) 302 280
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t339 : ((823600833/16000000000 : ℚ) : ℝ) ≤ stT302 339 := by
  have hc : ((947757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((823600833/16000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((947757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c340 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((174687/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3034733/10000000) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 280
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t340 : ((47355092831/2500000000000 : ℚ) : ℝ) ≤ stT302 340 := by
  have hc : ((174637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47355092831/2500000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((174637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c341 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-252771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5252017/10000000) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 280
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t341 : ((-136910408951/5000000000000 : ℚ) : ℝ) ≤ stT302 341 := by
  have hc : ((-252821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136910408951/5000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-252821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c342 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-246947/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1865721/2500000) (δ := 3803/250000000) (ψ := -164193/1000000) 302 280
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t342 : ((-33386848077/625000000000 : ℚ) : ℝ) ≤ stT302 342 := by
  have hc : ((-61743/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33386848077/625000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-61743/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c343 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-374147/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3020353/5000000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 281
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t343 : ((-4040953403/100000000000 : ℚ) : ℝ) ≤ stT302 343 := by
  have hc : ((-374197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4040953403/100000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-374197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c344 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((3369/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15371/40000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 281
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t344 : ((1811048517/1000000000000 : ℚ) : ℝ) ≤ stT302 344 := by
  have hc : ((3359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1811048517/1000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((3359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c345 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((394857/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25799/156250) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 281
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t345 : ((212556587467/5000000000000 : ℚ) : ℝ) ≤ stT302 345 := by
  have hc : ((394807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212556587467/5000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((394807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c346 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((977269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26703/500000) (δ := 3821/250000000) (ψ := -164193/1000000) 302 281
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t346 : ((525328985907/10000000000000 : ℚ) : ℝ) ≤ stT302 346 := by
  have hc : ((977169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525328985907/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((977169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c347 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((466739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271299/1000000) (δ := 3821/250000000) (ψ := -164193/1000000) 302 281
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t347 : ((62626220273/2500000000000 : ℚ) : ℝ) ≤ stT302 347 := by
  have hc : ((466639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62626220273/2500000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((466639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c348 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-46767/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2442827/5000000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 281
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t348 : ((-50152956863/2500000000000 : ℚ) : ℝ) ≤ stT302 348 := by
  have hc : ((-93559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50152956863/2500000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-93559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c349 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-474501/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3526063/5000000) (δ := 3821/250000000) (ψ := -164193/1000000) 302 281
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t349 : ((-31752681961/625000000000 : ℚ) : ℝ) ≤ stT302 349 := by
  have hc : ((-474551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31752681961/625000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-474551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c350 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-855987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6495631/10000000) (δ := 15177/1000000000) (ψ := -164193/1000000) 302 282
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t350 : ((-457598191501/10000000000000 : ℚ) : ℝ) ≤ stT302 350 := by
  have hc : ((-856087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-457598191501/10000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-856087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c351 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-165061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -217077/500000) (δ := 7613/500000000) (ψ := -164193/1000000) 302 282
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t351 : ((-88156500521/10000000000000 : ℚ) : ℝ) ≤ stT302 351 := by
  have hc : ((-165161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88156500521/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-165161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c352 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((63911/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2193641/10000000) (δ := 15177/1000000000) (ψ := -164193/1000000) 302 282
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t352 : ((34059296901/1000000000000 : ℚ) : ℝ) ≤ stT302 352 := by
  have hc : ((63901/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34059296901/1000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((63901/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c353 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((499893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51781/10000000) (δ := 7613/500000000) (ψ := -164193/1000000) 302 282
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t353 : ((133019718689/2500000000000 : ℚ) : ℝ) ≤ stT302 353 := by
  have hc : ((499843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133019718689/2500000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((499843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c354 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((168051/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1042019/5000000) (δ := 15177/1000000000) (ψ := -164193/1000000) 302 282
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t354 : ((22326202711/625000000000 : ℚ) : ℝ) ≤ stT302 354 := by
  have hc : ((84013/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22326202711/625000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((84013/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c355 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-114449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2106871/5000000) (δ := 15177/1000000000) (ψ := -164193/1000000) 302 282
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t355 : ((-12159261801/2000000000000 : ℚ) : ℝ) ≤ stT302 355 := by
  have hc : ((-114549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12159261801/2000000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-114549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c356 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-102701/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6337557/10000000) (δ := 15177/1000000000) (ψ := -164193/1000000) 302 282
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t356 : ((-108876104573/2500000000000 : ℚ) : ℝ) ≤ stT302 356 := by
  have hc : ((-205427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108876104573/2500000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-205427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c357 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-971209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7252631/10000000) (δ := 15133/1000000000) (ψ := -164193/1000000) 302 283
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t357 : ((-514072087413/10000000000000 : ℚ) : ℝ) ≤ stT302 357 := by
  have hc : ((-971309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-514072087413/10000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-971309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c358 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-116663/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1028149/2000000) (δ := 15133/1000000000) (ψ := -164193/1000000) 302 283
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t358 : ((-3854474481/156250000000 : ℚ) : ℝ) ≤ stT302 358 := by
  have hc : ((-7293/15625 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3854474481/156250000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-7293/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c359 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((349369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -758687/2500000) (δ := 15133/1000000000) (ψ := -164193/1000000) 302 283
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t359 : ((184336843551/10000000000000 : ℚ) : ℝ) ≤ stT302 359 := by
  have hc : ((349269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184336843551/10000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((349269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c360 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((930937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186913/2000000) (δ := 1527/100000000) (ψ := -164193/1000000) 302 283
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t360 : ((245296958751/5000000000000 : ℚ) : ℝ) ≤ stT302 360 := by
  have hc : ((930837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245296958751/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((930837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c361 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((447159/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115973/1000000) (δ := 15133/1000000000) (ψ := -164193/1000000) 302 283
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t361 : ((47064034667/1000000000000 : ℚ) : ℝ) ≤ stT302 361 := by
  have hc : ((447109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47064034667/1000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((447109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c362 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((268159/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1624143/5000000) (δ := 1527/100000000) (ψ := -164193/1000000) 302 283
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t362 : ((35222148423/2500000000000 : ℚ) : ℝ) ≤ stT302 362 := by
  have hc : ((268059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35222148423/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((268059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c363 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-266277/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5331029/10000000) (δ := 1527/100000000) (ψ := -164193/1000000) 302 283
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t363 : ((-2184147727/78125000000 : ℚ) : ℝ) ≤ stT302 363 := by
  have hc : ((-266327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2184147727/78125000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-266327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c364 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-984133/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3704017/5000000) (δ := 1527/100000000) (ψ := -164193/1000000) 302 283
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t364 : ((-515878837319/10000000000000 : ℚ) : ℝ) ≤ stT302 364 := by
  have hc : ((-984233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515878837319/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-984233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c365 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-198997/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3114293/5000000) (δ := 15241/1000000000) (ψ := -164193/1000000) 302 284
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t365 : ((-1627701427/39062500000 : ℚ) : ℝ) ≤ stT302 365 := by
  have hc : ((-99511/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1627701427/39062500000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-99511/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c366 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-47113/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2081453/5000000) (δ := 15241/1000000000) (ψ := -164193/1000000) 302 284
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t366 : ((-24652524567/5000000000000 : ℚ) : ℝ) ≤ stT302 366 := by
  have hc : ((-47163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24652524567/5000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-47163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c367 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((333301/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2102889/10000000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 284
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t367 : ((34791071149/1000000000000 : ℚ) : ℝ) ≤ stT302 367 := by
  have hc : ((333251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34791071149/1000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((333251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c368 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((249953/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24229/5000000) (δ := 15241/1000000000) (ψ := -164193/1000000) 302 284
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t368 : ((8142747963/156250000000 : ℚ) : ℝ) ≤ stT302 368 := by
  have hc : ((31241/31250 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8142747963/156250000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((31241/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c369 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((174149/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400077/2000000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 284
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t369 : ((22661324449/625000000000 : ℚ) : ℝ) ≤ stT302 369 := by
  have hc : ((43531/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22661324449/625000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((43531/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c370 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-23337/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4043717/10000000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 284
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t370 : ((-3039585003/1250000000000 : ℚ) : ℝ) ≤ stT302 370 := by
  have hc : ((-23387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3039585003/1250000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-23387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c371 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-23719/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3040731/5000000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 284
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t371 : ((-3941098959/100000000000 : ℚ) : ℝ) ≤ stT302 371 := by
  have hc : ((-189777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3941098959/100000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-189777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c372 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-497303/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -474637/625000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 285
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t372 : ((-64466398507/1250000000000 : ℚ) : ℝ) ≤ stT302 372 := by
  have hc : ((-497353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64466398507/1250000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-497353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c373 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-76257/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5567319/10000000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 285
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t373 : ((-78981795959/2500000000000 : ℚ) : ℝ) ≤ stT302 373 := by
  have hc : ((-152539/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78981795959/2500000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-152539/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c374 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((9489/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1772979/5000000) (δ := 3051/200000000) (ψ := -164193/1000000) 302 285
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t374 : ((19613626997/2500000000000 : ℚ) : ℝ) ≤ stT302 374 := by
  have hc : ((37931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19613626997/2500000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((37931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c375 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((25579/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1529881/10000000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 285
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t375 : ((105658440979/2500000000000 : ℚ) : ℝ) ≤ stT302 375 := by
  have hc : ((204607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105658440979/2500000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((204607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c376 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((981567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 480759/10000000) (δ := 3051/200000000) (ψ := -164193/1000000) 302 285
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t376 : ((50615234657/1000000000000 : ℚ) : ℝ) ≤ stT302 376 := by
  have hc : ((981467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50615234657/1000000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((981467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c377 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((544993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2486039/10000000) (δ := 3051/200000000) (ψ := -164193/1000000) 302 285
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t377 : ((140317031109/5000000000000 : ℚ) : ℝ) ≤ stT302 377 := by
  have hc : ((544893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140317031109/5000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((544893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c378 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-110879/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2243017/5000000) (δ := 3051/200000000) (ψ := -164193/1000000) 302 285
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t378 : ((-11411155301/1000000000000 : ℚ) : ℝ) ≤ stT302 378 := by
  have hc : ((-110929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11411155301/1000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-110929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c379 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-852909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 324041/500000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 285
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t379 : ((-219080860497/5000000000000 : ℚ) : ℝ) ≤ stT302 379 := by
  have hc : ((-853009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219080860497/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-853009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c380 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-969771/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3618859/5000000) (δ := 3051/200000000) (ψ := -164193/1000000) 302 286
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t380 : ((-49753412429/1000000000000 : ℚ) : ℝ) ≤ stT302 380 := by
  have hc : ((-969871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49753412429/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-969871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c381 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-101211/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5253503/10000000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 286
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t381 : ((-12965565249/500000000000 : ℚ) : ℝ) ≤ stT302 381 := by
  have hc : ((-101231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12965565249/500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-101231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c382 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((129037/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3274421/10000000) (δ := 3051/200000000) (ψ := -164193/1000000) 302 286
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t382 : ((16498856157/1250000000000 : ℚ) : ℝ) ≤ stT302 382 := by
  have hc : ((128987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16498856157/1250000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((128987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c383 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((173539/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2081/16000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 286
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t383 : ((86585981/1953125000 : ℚ) : ℝ) ≤ stT302 383 := by
  have hc : ((173519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86585981/1953125000 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((173519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c384 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((482251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 668113/10000000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 286
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t384 : ((24607199231/500000000000 : ℚ) : ℝ) ≤ stT302 384 := by
  have hc : ((482201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24607199231/500000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((482201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c385 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((495239/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2631717/10000000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 286
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t385 : ((252346105933/10000000000000 : ℚ) : ℝ) ≤ stT302 385 := by
  have hc : ((495139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252346105933/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((495139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c386 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-131089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4590187/10000000) (δ := 3787/250000000) (ψ := -164193/1000000) 302 286
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t386 : ((-66748046193/5000000000000 : ℚ) : ℝ) ≤ stT302 386 := by
  have hc : ((-131139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66748046193/5000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-131139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c387 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-216437/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6543599/10000000) (δ := 3051/200000000) (ψ := -164193/1000000) 302 286
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t387 : ((-55016955999/1250000000000 : ℚ) : ℝ) ≤ stT302 387 := by
  have hc : ((-108231/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55016955999/1250000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-108231/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c388 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-120951/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112749/156250) (δ := 7581/500000000) (ψ := -164193/1000000) 302 287
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t388 : ((-61410023899/1250000000000 : ℚ) : ℝ) ≤ stT302 388 := by
  have hc : ((-241927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61410023899/1250000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-241927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c389 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-512617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2636283/5000000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 287
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t389 : ((-259958286057/10000000000000 : ℚ) : ℝ) ≤ stT302 389 := by
  have hc : ((-512717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259958286057/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-512717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c390 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((234909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3334179/10000000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 287
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t390 : ((118899998521/10000000000000 : ℚ) : ℝ) ≤ stT302 390 := by
  have hc : ((234809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118899998521/10000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((234809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c391 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((84709/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56031/400000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 287
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t391 : ((42834062979/1000000000000 : ℚ) : ℝ) ≤ stT302 391 := by
  have hc : ((84699/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42834062979/1000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((84699/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c392 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((977803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527721/10000000) (δ := 15241/1000000000) (ψ := -164193/1000000) 302 287
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t392 : ((123453580107/2500000000000 : ℚ) : ℝ) ≤ stT302 392 := by
  have hc : ((977703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123453580107/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((977703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c393 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((556587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245131/1000000) (δ := 15241/1000000000) (ψ := -164193/1000000) 302 287
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t393 : ((280710406871/10000000000000 : ℚ) : ℝ) ≤ stT302 393 := by
  have hc : ((556487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280710406871/10000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((556487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c394 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-7051/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 546249/1250000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 287
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t394 : ((-710851923/80000000000 : ℚ) : ℝ) ≤ stT302 394 := by
  have hc : ((-1411/8000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-710851923/80000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-1411/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c395 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-404577/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3141883/5000000) (δ := 7581/500000000) (ψ := -164193/1000000) 302 287
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t395 : ((-40718019637/1000000000000 : ℚ) : ℝ) ≤ stT302 395 := by
  have hc : ((-404627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40718019637/1000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-404627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c396 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-990831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -375759/500000) (δ := 7567/500000000) (ψ := -164193/1000000) 302 288
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t396 : ((-497961655189/10000000000000 : ℚ) : ℝ) ≤ stT302 396 := by
  have hc : ((-990931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497961655189/10000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-990931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c397 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-155957/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -561107/1000000) (δ := 7567/500000000) (ψ := -164193/1000000) 302 288
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t397 : ((-19571295513/625000000000 : ℚ) : ℝ) ≤ stT302 397 := by
  have hc : ((-77991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19571295513/625000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-77991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c398 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((86033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3711641/10000000) (δ := 7567/500000000) (ψ := -164193/1000000) 302 288
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t398 : ((21537129991/5000000000000 : ℚ) : ℝ) ≤ stT302 398 := by
  have hc : ((85933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21537129991/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((85933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c399 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((747293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -454261/2500000) (δ := 7567/500000000) (ψ := -164193/1000000) 302 288
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t399 : ((187032121409/5000000000000 : ℚ) : ℝ) ≤ stT302 399 := by
  have hc : ((747193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187032121409/5000000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((747193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c400 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((124947/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72797/10000000) (δ := 15269/1000000000) (ψ := -164193/1000000) 302 288
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t400 : ((249869/5000000 : ℚ) : ℝ) ≤ stT302 400 := by
  have hc : ((249869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249869/5000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((249869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c401 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((11073/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489489/2500000) (δ := 7567/500000000) (ψ := -164193/1000000) 302 288
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t401 : ((5528810173/156250000000 : ℚ) : ℝ) ≤ stT302 401 := by
  have hc : ((177143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5528810173/156250000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((177143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c402 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((7089/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3838359/10000000) (δ := 7567/500000000) (ψ := -164193/1000000) 302 288
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t402 : ((1762846013/1000000000000 : ℚ) : ℝ) ≤ stT302 402 := by
  have hc : ((7069/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1762846013/1000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((7069/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c403 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-655517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5714157/10000000) (δ := 15269/1000000000) (ψ := -164193/1000000) 302 288
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t403 : ((-40823303739/1250000000000 : ℚ) : ℝ) ≤ stT302 403 := by
  have hc : ((-655617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40823303739/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-655617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c404 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-994229/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7585273/10000000) (δ := 7567/500000000) (ψ := -164193/1000000) 302 288
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t404 : ((-494697569751/10000000000000 : ℚ) : ℝ) ≤ stT302 404 := by
  have hc : ((-994329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-494697569751/10000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-994329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c405 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-40131/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6256179/10000000) (δ := 1897/125000000) (ψ := -164193/1000000) 302 289
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t405 : ((-311620921/7812500000 : ℚ) : ℝ) ≤ stT302 405 := by
  have hc : ((-5017/6250 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311620921/7812500000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-5017/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c406 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-185827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2197137/5000000) (δ := 15227/1000000000) (ψ := -164193/1000000) 302 289
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t406 : ((-23068520671/2500000000000 : ℚ) : ℝ) ≤ stT302 406 := by
  have hc : ((-185927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23068520671/2500000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-185927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c407 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((527799/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1268487/5000000) (δ := 15227/1000000000) (ψ := -164193/1000000) 302 289
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t407 : ((261570368019/10000000000000 : ℚ) : ℝ) ≤ stT302 407 := by
  have hc : ((527699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261570368019/10000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((527699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c408 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((481391/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171051/2500000) (δ := 15227/1000000000) (ψ := -164193/1000000) 302 289
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t408 : ((238298932893/5000000000000 : ℚ) : ℝ) ≤ stT302 408 := by
  have hc : ((481341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238298932893/5000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((481341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c409 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((446773/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291009/2500000) (δ := 15227/1000000000) (ψ := -164193/1000000) 302 289
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t409 : ((55222557091/1250000000000 : ℚ) : ℝ) ≤ stT302 409 := by
  have hc : ((446723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55222557091/1250000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((446723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c410 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((89867/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1503873/5000000) (δ := 15227/1000000000) (ψ := -164193/1000000) 302 289
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t410 : ((2773108093/156250000000 : ℚ) : ℝ) ≤ stT302 410 := by
  have hc : ((44921/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2773108093/156250000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((44921/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c411 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-179877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2423501/5000000) (δ := 1897/125000000) (ψ := -164193/1000000) 302 289
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t411 : ((-5546969483/312500000000 : ℚ) : ℝ) ≤ stT302 411 := by
  have hc : ((-179927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5546969483/312500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-179927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c412 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-178413/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6681727/10000000) (δ := 15227/1000000000) (ψ := -164193/1000000) 302 289
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t412 : ((-17581538789/400000000000 : ℚ) : ℝ) ≤ stT302 412 := by
  have hc : ((-178433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17581538789/400000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-178433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c413 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-965561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1439193/2000000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 290
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t413 : ((-118792719237/2500000000000 : ℚ) : ℝ) ≤ stT302 413 := by
  have hc : ((-965661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118792719237/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-965661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c414 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-545707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5370073/10000000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 290
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t414 : ((-134124974759/5000000000000 : ℚ) : ℝ) ≤ stT302 414 := by
  have hc : ((-545807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134124974759/5000000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-545807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c415 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((30159/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44357/125000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 290
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t415 : ((23116613/3125000000 : ℚ) : ℝ) ≤ stT302 415 := by
  have hc : ((30139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23116613/3125000000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((30139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c416 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((192397/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1731501/10000000) (δ := 3821/250000000) (ψ := -164193/1000000) 302 290
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t416 : ((2357951697/62500000000 : ℚ) : ℝ) ≤ stT302 416 := by
  have hc : ((48093/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2357951697/62500000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((48093/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c417 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((62467/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40627/5000000) (δ := 3821/250000000) (ψ := -164193/1000000) 302 290
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t417 : ((61174308393/1250000000000 : ℚ) : ℝ) ≤ stT302 417 := by
  have hc : ((249843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61174308393/1250000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((249843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c418 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((727687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188963/1000000) (δ := 3821/250000000) (ψ := -164193/1000000) 302 290
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t418 : ((71174743101/2000000000000 : ℚ) : ℝ) ≤ stT302 418 := by
  have hc : ((727587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71174743101/2000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((727587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c419 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((4659/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1846851/5000000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 290
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t419 : ((1136811637/250000000000 : ℚ) : ℝ) ≤ stT302 419 := by
  have hc : ((2327/25000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1136811637/250000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((2327/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c420 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-146597/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5493471/10000000) (δ := 15119/1000000000) (ψ := -164193/1000000) 302 290
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t420 : ((-35772175761/1250000000000 : ℚ) : ℝ) ≤ stT302 420 := by
  have hc : ((-73311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35772175761/1250000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-73311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c421 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-974567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7288937/10000000) (δ := 3821/250000000) (ψ := -164193/1000000) 302 290
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t421 : ((-475024430457/10000000000000 : ℚ) : ℝ) ≤ stT302 421 := by
  have hc : ((-974667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475024430457/10000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-974667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c422 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-220527/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6627789/10000000) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 291
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t422 : ((-13420396217/312500000000 : ℚ) : ℝ) ≤ stT302 422 := by
  have hc : ((-27569/31250 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13420396217/312500000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-27569/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c423 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-357459/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -968171/2000000) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 291
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t423 : ((-173851264303/10000000000000 : ℚ) : ℝ) ≤ stT302 423 := by
  have hc : ((-357559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173851264303/10000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-357559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c424 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((340611/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1529037/5000000) (δ := 3803/250000000) (ψ := -164193/1000000) 302 291
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t424 : ((82683221531/5000000000000 : ℚ) : ℝ) ≤ stT302 424 := by
  have hc : ((340511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82683221531/5000000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((340511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c425 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((43593/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7997/62500) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 291
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t425 : ((5285818687/125000000000 : ℚ) : ℝ) ≤ stT302 425 := by
  have hc : ((10897/12500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5285818687/125000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((10897/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c426 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((980471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 494881/10000000) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 291
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t426 : ((474990729871/10000000000000 : ℚ) : ℝ) ≤ stT302 426 := by
  have hc : ((980371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474990729871/10000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((980371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c427 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((308429/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2265129/10000000) (δ := 3803/250000000) (ψ := -164193/1000000) 302 291
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t427 : ((149234774607/5000000000000 : ℚ) : ℝ) ≤ stT302 427 := by
  have hc : ((308379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149234774607/5000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((308379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c428 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-10413/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80623/200000) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 291
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t428 : ((-2522702811/1250000000000 : ℚ) : ℝ) ≤ stT302 428 := by
  have hc : ((-5219/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2522702811/1250000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-5219/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c429 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-679053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5793169/10000000) (δ := 15191/1000000000) (ψ := -164193/1000000) 302 291
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t429 : ((-65579692833/2000000000000 : ℚ) : ℝ) ≤ stT302 429 := by
  have hc : ((-679153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65579692833/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-679153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c430 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-992667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1510207/2000000) (δ := 3803/250000000) (ψ := -164193/1000000) 302 291
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t430 : ((-478754936381/10000000000000 : ℚ) : ℝ) ≤ stT302 430 := by
  have hc : ((-992767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478754936381/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-992767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c431 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-418147/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3201607/5000000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 292
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t431 : ((-50359700937/1250000000000 : ℚ) : ℝ) ≤ stT302 431 := by
  have hc : ((-418197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50359700937/1250000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-418197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c432 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-286531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4653501/10000000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 292
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t432 : ((-68952813253/5000000000000 : ℚ) : ℝ) ≤ stT302 432 := by
  have hc : ((-286631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68952813253/5000000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-286631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c433 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((396481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290779/1000000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 292
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t433 : ((190488420789/10000000000000 : ℚ) : ℝ) ≤ stT302 433 := by
  have hc : ((396381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190488420789/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((396381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c434 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((178633/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -291539/2500000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 292
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t434 : ((17147383839/400000000000 : ℚ) : ℝ) ≤ stT302 434 := by
  have hc : ((178613/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17147383839/400000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((178613/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c435 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((973987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142869/2500000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 292
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t435 : ((466942782681/10000000000000 : ℚ) : ℝ) ≤ stT302 435 := by
  have hc : ((973887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466942782681/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((973887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c436 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((302097/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2305107/10000000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 292
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t436 : ((144654234911/5000000000000 : ℚ) : ℝ) ≤ stT302 436 := by
  have hc : ((302047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144654234911/5000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((302047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c437 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-8617/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4034737/10000000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 292
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t437 : ((-826327701/400000000000 : ℚ) : ℝ) ≤ stT302 437 := by
  have hc : ((-8637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-826327701/400000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-8637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c438 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-669407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1440129/2500000) (δ := 7649/500000000) (ψ := -164193/1000000) 302 292
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t438 : ((-319903165233/10000000000000 : ℚ) : ℝ) ≤ stT302 438 := by
  have hc : ((-669507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319903165233/10000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-669507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c439 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-123621/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7482293/10000000) (δ := 3021/200000000) (ψ := -164193/1000000) 302 292
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t439 : ((-59007055079/1250000000000 : ℚ) : ℝ) ≤ stT302 439 := by
  have hc : ((-247267/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59007055079/1250000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-247267/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c440 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-858497/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6507819/10000000) (δ := 7599/500000000) (ψ := -164193/1000000) 302 293
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t440 : ((-102330166251/2500000000000 : ℚ) : ℝ) ≤ stT302 440 := by
  have hc : ((-858597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102330166251/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-858597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c441 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-339853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4793893/10000000) (δ := 3041/200000000) (ψ := -164193/1000000) 302 293
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t441 : ((-161882559023/10000000000000 : ℚ) : ℝ) ≤ stT302 441 := by
  have hc : ((-339953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161882559023/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-339953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c442 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((330911/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1541909/5000000) (δ := 3041/200000000) (ψ := -164193/1000000) 302 293
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t442 : ((157350582961/10000000000000 : ℚ) : ℝ) ≤ stT302 442 := by
  have hc : ((330811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157350582961/10000000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((330811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c443 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((425991/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -688797/5000000) (δ := 7599/500000000) (ψ := -164193/1000000) 302 293
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t443 : ((101185266137/2500000000000 : ℚ) : ℝ) ≤ stT302 443 := by
  have hc : ((425941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101185266137/2500000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((425941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c444 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((991573/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16239/500000) (δ := 7599/500000000) (ψ := -164193/1000000) 302 293
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t444 : ((235265636697/5000000000000 : ℚ) : ℝ) ≤ stT302 444 := by
  have hc : ((991473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235265636697/5000000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((991473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c445 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((68999/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 252913/1250000) (δ := 3041/200000000) (ψ := -164193/1000000) 302 293
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t445 : ((6540778101/200000000000 : ℚ) : ℝ) ≤ stT302 445 := by
  have hc : ((68989/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6540778101/200000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((68989/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c446 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((41739/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 929513/2500000) (δ := 7599/500000000) (ψ := -164193/1000000) 302 293
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t446 : ((19740283457/5000000000000 : ℚ) : ℝ) ≤ stT302 446 := by
  have hc : ((41689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19740283457/5000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((41689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c447 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-34917/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108179/200000) (δ := 7599/500000000) (ψ := -164193/1000000) 302 293
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t447 : ((-8259069239/312500000000 : ℚ) : ℝ) ≤ stT302 447 := by
  have hc : ((-139693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8259069239/312500000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-139693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c448 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-477203/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7096149/10000000) (δ := 3041/200000000) (ψ := -164193/1000000) 302 293
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t448 : ((-28185130421/625000000000 : ℚ) : ℝ) ≤ stT302 448 := by
  have hc : ((-477253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28185130421/625000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-477253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c449 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-932253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6928467/10000000) (δ := 15291/1000000000) (ψ := -164193/1000000) 302 294
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t449 : ((-44000535129/1000000000000 : ℚ) : ℝ) ≤ stT302 449 := by
  have hc : ((-932353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44000535129/1000000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-932353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c450 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-252219/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2624409/5000000) (δ := 1889/125000000) (ψ := -164193/1000000) 302 294
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t450 : ((-23784173589/1000000000000 : ℚ) : ℝ) ≤ stT302 450 := by
  have hc : ((-252269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23784173589/1000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-252269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c451 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((17647/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3572869/10000000) (δ := 1889/125000000) (ψ := -164193/1000000) 302 294
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t451 : ((16607501989/2500000000000 : ℚ) : ℝ) ≤ stT302 451 := by
  have hc : ((35269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16607501989/2500000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((35269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c452 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((181161/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -380139/2000000) (δ := 1889/125000000) (ψ := -164193/1000000) 302 294
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t452 : ((133123639/3906250000 : ℚ) : ℝ) ≤ stT302 452 := by
  have hc : ((11321/15625 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133123639/3906250000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((11321/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c453 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((248923/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46429/2000000) (δ := 1889/125000000) (ψ := -164193/1000000) 302 294
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t453 : ((730888977/15625000000 : ℚ) : ℝ) ≤ stT302 453 := by
  have hc : ((124449/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((730888977/15625000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((124449/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c454 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((3361/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143263/1000000) (δ := 1889/125000000) (ψ := -164193/1000000) 302 294
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t454 : ((7886034369/200000000000 : ℚ) : ℝ) ≤ stT302 454 := by
  have hc : ((16803/20000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7886034369/200000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((16803/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c455 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((4089/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96683/312500) (δ := 15291/1000000000) (ψ := -164193/1000000) 302 294
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t455 : ((7665463257/500000000000 : ℚ) : ℝ) ≤ stT302 455 := by
  have hc : ((16351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7665463257/500000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((16351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c456 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-323813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4751383/10000000) (δ := 15291/1000000000) (ψ := -164193/1000000) 302 294
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t456 : ((-151686190509/10000000000000 : ℚ) : ℝ) ≤ stT302 456 := by
  have hc : ((-323913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151686190509/10000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-323913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c457 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-209183/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6405211/10000000) (δ := 1889/125000000) (ψ := -164193/1000000) 302 294
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t457 : ((-12232940931/312500000000 : ℚ) : ℝ) ≤ stT302 457 := by
  have hc : ((-26151/31250 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12232940931/312500000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-26151/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c458 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-996753/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7652473/10000000) (δ := 15219/1000000000) (ψ := -164193/1000000) 302 295
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t458 : ((-46579950131/1000000000000 : ℚ) : ℝ) ≤ stT302 458 := by
  have hc : ((-996853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46579950131/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-996853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c459 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-738943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6005743/10000000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t459 : ((-344956449723/10000000000000 : ℚ) : ℝ) ≤ stT302 459 := by
  have hc : ((-739043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344956449723/10000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-739043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c460 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-173407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -545339/1250000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t460 : ((-80898159271/10000000000000 : ℚ) : ℝ) ≤ stT302 460 := by
  have hc : ((-173507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80898159271/10000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-173507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c461 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((23157/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1361577/5000000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t461 : ((336967231/15625000000 : ℚ) : ℝ) ≤ stT302 461 := by
  have hc : ((1447/3125 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336967231/15625000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((1447/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c462 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((906917/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54361/500000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t462 : ((210944677357/5000000000000 : ℚ) : ℝ) ≤ stT302 462 := by
  have hc : ((906817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210944677357/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((906817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c463 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((976311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 545241/10000000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t463 : ((453683323929/10000000000000 : ℚ) : ℝ) ≤ stT302 463 := by
  have hc : ((976211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453683323929/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((976211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c464 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((129017/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1087077/5000000) (δ := 15219/1000000000) (ψ := -164193/1000000) 302 295
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t464 : ((29942654643/1000000000000 : ℚ) : ℝ) ≤ stT302 464 := by
  have hc : ((128997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29942654643/1000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((128997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c465 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((50937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3799593/10000000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t465 : ((11787524353/5000000000000 : ℚ) : ℝ) ≤ stT302 465 := by
  have hc : ((50837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11787524353/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((50837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c466 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-562823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1355371/2500000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t466 : ((-130384788183/5000000000000 : ℚ) : ℝ) ≤ stT302 466 := by
  have hc : ((-562923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130384788183/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-562923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c467 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-947449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3519951/5000000) (δ := 949/62500000) (ψ := -164193/1000000) 302 295
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t467 : ((-87694712401/2000000000000 : ℚ) : ℝ) ≤ stT302 467 := by
  have hc : ((-947549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87694712401/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-947549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c468 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-474563/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1763279/2500000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 296
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t468 : ((-219390333863/5000000000000 : ℚ) : ℝ) ≤ stT302 468 := by
  have hc : ((-474613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219390333863/5000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-474613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c469 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-284723/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5441569/10000000) (δ := 3819/250000000) (ψ := -164193/1000000) 302 296
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t469 : ((-65748105467/2500000000000 : ℚ) : ℝ) ≤ stT302 469 := by
  have hc : ((-284773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65748105467/2500000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-284773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c470 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((3739/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1916747/5000000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 296
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t470 : ((344011437/200000000000 : ℚ) : ℝ) ≤ stT302 470 := by
  have hc : ((3729/100000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344011437/200000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((3729/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c471 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((25129/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2228817/10000000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 296
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t471 : ((3704631/128000000 : ℚ) : ℝ) ≤ stT302 471 := by
  have hc : ((201/320 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3704631/128000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((201/320 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c472 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((968661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313769/5000000) (δ := 3819/250000000) (ψ := -164193/1000000) 302 296
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t472 : ((445816037007/10000000000000 : ℚ) : ℝ) ≤ stT302 472 := by
  have hc : ((968561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445816037007/10000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((968561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c473 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((57851/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121293/1250000) (δ := 3819/250000000) (ψ := -164193/1000000) 302 296
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t473 : ((531940321/12500000000 : ℚ) : ℝ) ≤ stT302 473 := by
  have hc : ((231379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((531940321/12500000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((231379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c474 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((518277/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 320613/1250000) (δ := 3819/250000000) (ψ := -164193/1000000) 302 296
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t474 : ((47601293751/2000000000000 : ℚ) : ℝ) ≤ stT302 474 := by
  have hc : ((518177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47601293751/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((518177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c475 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-45751/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4156067/10000000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 296
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t475 : ((-1313435277/312500000000 : ℚ) : ℝ) ≤ stT302 475 := by
  have hc : ((-45801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1313435277/312500000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-45801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c476 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-332217/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 717979/1250000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 296
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t476 : ((-3045891589/100000000000 : ℚ) : ℝ) ≤ stT302 476 := by
  have hc : ((-332267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3045891589/100000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-332267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c477 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-244493/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 293131/400000) (δ := 15127/1000000000) (ψ := -164193/1000000) 302 296
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t477 : ((-55978606071/1250000000000 : ℚ) : ℝ) ≤ stT302 477 := by
  have hc : ((-122259/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55978606071/1250000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-122259/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c478 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-912191/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1699623/2500000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 297
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t478 : ((-41727278049/1000000000000 : ℚ) : ℝ) ≤ stT302 478 := by
  have hc : ((-912291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41727278049/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-912291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c479 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-123673/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5220693/10000000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 297
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t479 : ((-1766221893/78125000000 : ℚ) : ℝ) ≤ stT302 479 := by
  have hc : ((-61849/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1766221893/78125000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-61849/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c480 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((56067/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -729213/2000000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 297
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t480 : ((5113623879/1000000000000 : ℚ) : ℝ) ≤ stT302 480 := by
  have hc : ((56017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5113623879/1000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((56017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c481 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((26997/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1037417/5000000) (δ := 7617/500000000) (ψ := -164193/1000000) 302 297
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t481 : ((307693207/10000000000 : ℚ) : ℝ) ≤ stT302 481 := by
  have hc : ((26993/40000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307693207/10000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((26993/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c482 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((39181/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20271/400000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 297
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t482 : ((17844614199/400000000000 : ℚ) : ℝ) ≤ stT302 482 := by
  have hc : ((39177/40000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17844614199/400000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((39177/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c483 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((455893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1057963/10000000) (δ := 7617/500000000) (ψ := -164193/1000000) 302 297
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t483 : ((41483080529/1000000000000 : ℚ) : ℝ) ≤ stT302 483 := by
  have hc : ((455843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41483080529/1000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((455843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c484 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((124867/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2619529/10000000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 297
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t484 : ((5674630689/250000000000 : ℚ) : ℝ) ≤ stT302 484 := by
  have hc : ((62421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5674630689/250000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((62421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c485 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-20029/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2088887/5000000) (δ := 7617/500000000) (ψ := -164193/1000000) 302 297
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t485 : ((-9103789773/2000000000000 : ℚ) : ℝ) ≤ stT302 485 := by
  have hc : ((-20049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9103789773/2000000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-20049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c486 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-661167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5732923/10000000) (δ := 7617/500000000) (ψ := -164193/1000000) 302 297
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t486 : ((-29995732387/1000000000000 : ℚ) : ℝ) ≤ stT302 486 := by
  have hc : ((-661267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29995732387/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-661267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c487 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-974197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291393/400000) (δ := 15169/1000000000) (ψ := -164193/1000000) 302 297
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t487 : ((-55187104971/1250000000000 : ℚ) : ℝ) ≤ stT302 487 := by
  have hc : ((-974297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55187104971/1250000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-974297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c488 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-231053/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6874407/10000000) (δ := 7631/500000000) (ψ := -164193/1000000) 302 298
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t488 : ((-52302078981/1250000000000 : ℚ) : ℝ) ≤ stT302 488 := by
  have hc : ((-115539/125000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52302078981/1250000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-115539/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c489 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-531841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2664461/5000000) (δ := 7631/500000000) (ψ := -164193/1000000) 302 298
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t489 : ((-30069028907/1250000000000 : ℚ) : ℝ) ≤ stT302 489 := by
  have hc : ((-531941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30069028907/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-531941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c490 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((28077/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -946633/2500000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 298
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t490 : ((12661281331/5000000000000 : ℚ) : ℝ) ≤ stT302 490 := by
  have hc : ((28027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12661281331/5000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((28027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c491 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((24899/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1123619/5000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 298
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t491 : ((2246987847/80000000000 : ℚ) : ℝ) ≤ stT302 491 := by
  have hc : ((4979/8000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2246987847/80000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((4979/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c492 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((959817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142223/2000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 298
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t492 : ((216336526989/5000000000000 : ℚ) : ℝ) ≤ stT302 492 := by
  have hc : ((959717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216336526989/5000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((959717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c493 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((236613/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 821837/10000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 298
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t493 : ((26638448419/625000000000 : ℚ) : ℝ) ≤ stT302 493 := by
  have hc : ((59147/62500 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26638448419/625000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((59147/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c494 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((18413/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2351769/10000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 298
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t494 : ((66263914959/2500000000000 : ℚ) : ℝ) ≤ stT302 494 := by
  have hc : ((147279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66263914959/2500000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((147279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c495 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((19383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 387853/1000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 298
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t495 : ((4333526439/5000000000000 : ℚ) : ℝ) ≤ stT302 495 := by
  have hc : ((19283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4333526439/5000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((19283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c496 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-278227/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5402271/10000000) (δ := 15141/1000000000) (ψ := -164193/1000000) 302 298
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t496 : ((-62475134439/2500000000000 : ℚ) : ℝ) ≤ stT302 496 := by
  have hc : ((-278277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62475134439/2500000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-278277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c497 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-931447/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1730729/2500000) (δ := 7631/500000000) (ψ := -164193/1000000) 302 298
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t497 : ((-208928292707/5000000000000 : ℚ) : ℝ) ≤ stT302 497 := by
  have hc : ((-931547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208928292707/5000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-931547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c498 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-972609/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7267497/10000000) (δ := 3031/200000000) (ψ := -164193/1000000) 302 299
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t498 : ((-435881602699/10000000000000 : ℚ) : ℝ) ≤ stT302 498 := by
  have hc : ((-972709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435881602699/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-972709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c499 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-667161/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5752967/10000000) (δ := 3031/200000000) (ψ := -164193/1000000) 302 299
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t499 : ((-149353696891/5000000000000 : ℚ) : ℝ) ≤ stT302 499 := by
  have hc : ((-667261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149353696891/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-667261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_c500 :
    |Real.cos (((302 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-25091/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4241457/10000000) (δ := 3031/200000000) (ψ := -164193/1000000) 302 299
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st302_t500 : ((-5614995377/1000000000000 : ℚ) : ℝ) ≤ stT302 500 := by
  have hc : ((-25111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((302 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st302_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5614995377/1000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-25111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st302_p1 : ((986451/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT302 (i+1) := by
  rw [Finset.sum_range_one]
  exact st302_t1

theorem st302_p2 : ((749531745791/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT302 (i+1))
      = (∑ i ∈ Finset.range 1, stT302 (i+1)) + stT302 2 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 1
    simpa using h
  have hprev := st302_p1
  have hstep := st302_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p3 : ((54996134771/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT302 (i+1))
      = (∑ i ∈ Finset.range 2, stT302 (i+1)) + stT302 3 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 2
    simpa using h
  have hprev := st302_p2
  have hstep := st302_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p4 : ((3034545508651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT302 (i+1))
      = (∑ i ∈ Finset.range 3, stT302 (i+1)) + stT302 4 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 3
    simpa using h
  have hprev := st302_p3
  have hstep := st302_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p5 : ((274331105459/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT302 (i+1))
      = (∑ i ∈ Finset.range 4, stT302 (i+1)) + stT302 5 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 4
    simpa using h
  have hprev := st302_p4
  have hstep := st302_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p6 : ((2605459154853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT302 (i+1))
      = (∑ i ∈ Finset.range 5, stT302 (i+1)) + stT302 6 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 5
    simpa using h
  have hprev := st302_p5
  have hstep := st302_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p7 : ((1661646452101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT302 (i+1))
      = (∑ i ∈ Finset.range 6, stT302 (i+1)) + stT302 7 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 6
    simpa using h
  have hprev := st302_p6
  have hstep := st302_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p8 : ((321873092497/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT302 (i+1))
      = (∑ i ∈ Finset.range 7, stT302 (i+1)) + stT302 8 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 7
    simpa using h
  have hprev := st302_p7
  have hstep := st302_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p9 : ((1474792853271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT302 (i+1))
      = (∑ i ∈ Finset.range 8, stT302 (i+1)) + stT302 9 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 8
    simpa using h
  have hprev := st302_p8
  have hstep := st302_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p10 : ((490211432779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT302 (i+1))
      = (∑ i ∈ Finset.range 9, stT302 (i+1)) + stT302 10 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 9
    simpa using h
  have hprev := st302_p9
  have hstep := st302_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p11 : ((69340813367/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT302 (i+1))
      = (∑ i ∈ Finset.range 10, stT302 (i+1)) + stT302 11 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 10
    simpa using h
  have hprev := st302_p10
  have hstep := st302_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p12 : ((-355279685701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT302 (i+1))
      = (∑ i ∈ Finset.range 11, stT302 (i+1)) + stT302 12 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 11
    simpa using h
  have hprev := st302_p11
  have hstep := st302_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p13 : ((-2440627201893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT302 (i+1))
      = (∑ i ∈ Finset.range 12, stT302 (i+1)) + stT302 13 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 12
    simpa using h
  have hprev := st302_p12
  have hstep := st302_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p14 : ((-588517776341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT302 (i+1))
      = (∑ i ∈ Finset.range 13, stT302 (i+1)) + stT302 14 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 13
    simpa using h
  have hprev := st302_p13
  have hstep := st302_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p15 : ((78342662391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT302 (i+1))
      = (∑ i ∈ Finset.range 14, stT302 (i+1)) + stT302 15 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 14
    simpa using h
  have hprev := st302_p14
  have hstep := st302_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p16 : ((-115404718527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT302 (i+1))
      = (∑ i ∈ Finset.range 15, stT302 (i+1)) + stT302 16 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 15
    simpa using h
  have hprev := st302_p15
  have hstep := st302_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p17 : ((230514106329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT302 (i+1))
      = (∑ i ∈ Finset.range 16, stT302 (i+1)) + stT302 17 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 16
    simpa using h
  have hprev := st302_p16
  have hstep := st302_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p18 : ((338513954439/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT302 (i+1))
      = (∑ i ∈ Finset.range 17, stT302 (i+1)) + stT302 18 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 17
    simpa using h
  have hprev := st302_p17
  have hstep := st302_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p19 : ((262960008351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT302 (i+1))
      = (∑ i ∈ Finset.range 18, stT302 (i+1)) + stT302 19 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 18
    simpa using h
  have hprev := st302_p18
  have hstep := st302_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p20 : ((2751327685313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT302 (i+1))
      = (∑ i ∈ Finset.range 19, stT302 (i+1)) + stT302 20 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 19
    simpa using h
  have hprev := st302_p19
  have hstep := st302_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p21 : ((169393194643/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT302 (i+1))
      = (∑ i ∈ Finset.range 20, stT302 (i+1)) + stT302 21 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 20
    simpa using h
  have hprev := st302_p20
  have hstep := st302_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p22 : ((-49680221393/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT302 (i+1))
      = (∑ i ∈ Finset.range 21, stT302 (i+1)) + stT302 22 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 21
    simpa using h
  have hprev := st302_p21
  have hstep := st302_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p23 : ((-309886220957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT302 (i+1))
      = (∑ i ∈ Finset.range 22, stT302 (i+1)) + stT302 23 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 22
    simpa using h
  have hprev := st302_p22
  have hstep := st302_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p24 : ((-254735272643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT302 (i+1))
      = (∑ i ∈ Finset.range 23, stT302 (i+1)) + stT302 24 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 23
    simpa using h
  have hprev := st302_p23
  have hstep := st302_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p25 : ((-371323330937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT302 (i+1))
      = (∑ i ∈ Finset.range 24, stT302 (i+1)) + stT302 25 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 24
    simpa using h
  have hprev := st302_p24
  have hstep := st302_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p26 : ((-1750688973179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT302 (i+1))
      = (∑ i ∈ Finset.range 25, stT302 (i+1)) + stT302 26 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 25
    simpa using h
  have hprev := st302_p25
  have hstep := st302_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p27 : ((-1769778458101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT302 (i+1))
      = (∑ i ∈ Finset.range 26, stT302 (i+1)) + stT302 27 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 26
    simpa using h
  have hprev := st302_p26
  have hstep := st302_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p28 : ((-35255263259/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT302 (i+1))
      = (∑ i ∈ Finset.range 27, stT302 (i+1)) + stT302 28 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 27
    simpa using h
  have hprev := st302_p27
  have hstep := st302_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p29 : ((-188949502431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT302 (i+1))
      = (∑ i ∈ Finset.range 28, stT302 (i+1)) + stT302 29 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 28
    simpa using h
  have hprev := st302_p28
  have hstep := st302_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p30 : ((-104279717567/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT302 (i+1))
      = (∑ i ∈ Finset.range 29, stT302 (i+1)) + stT302 30 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 29
    simpa using h
  have hprev := st302_p29
  have hstep := st302_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p31 : ((-352666747607/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT302 (i+1))
      = (∑ i ∈ Finset.range 30, stT302 (i+1)) + stT302 31 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 30
    simpa using h
  have hprev := st302_p30
  have hstep := st302_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p32 : ((-630679928163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT302 (i+1))
      = (∑ i ∈ Finset.range 31, stT302 (i+1)) + stT302 32 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 31
    simpa using h
  have hprev := st302_p31
  have hstep := st302_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p33 : ((-1655454929711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT302 (i+1))
      = (∑ i ∈ Finset.range 32, stT302 (i+1)) + stT302 33 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 32
    simpa using h
  have hprev := st302_p32
  have hstep := st302_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p34 : ((-3357196092833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT302 (i+1))
      = (∑ i ∈ Finset.range 33, stT302 (i+1)) + stT302 34 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 33
    simpa using h
  have hprev := st302_p33
  have hstep := st302_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p35 : ((-1912273485809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT302 (i+1))
      = (∑ i ∈ Finset.range 34, stT302 (i+1)) + stT302 35 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 34
    simpa using h
  have hprev := st302_p34
  have hstep := st302_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p36 : ((-2092500188521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT302 (i+1))
      = (∑ i ∈ Finset.range 35, stT302 (i+1)) + stT302 36 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 35
    simpa using h
  have hprev := st302_p35
  have hstep := st302_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p37 : ((-3512138161201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT302 (i+1))
      = (∑ i ∈ Finset.range 36, stT302 (i+1)) + stT302 37 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 36
    simpa using h
  have hprev := st302_p36
  have hstep := st302_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p38 : ((-97288628059/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT302 (i+1))
      = (∑ i ∈ Finset.range 37, stT302 (i+1)) + stT302 38 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 37
    simpa using h
  have hprev := st302_p37
  have hstep := st302_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p39 : ((-30691902211/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT302 (i+1))
      = (∑ i ∈ Finset.range 38, stT302 (i+1)) + stT302 39 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 38
    simpa using h
  have hprev := st302_p38
  have hstep := st302_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p40 : ((-2001354280503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT302 (i+1))
      = (∑ i ∈ Finset.range 39, stT302 (i+1)) + stT302 40 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 39
    simpa using h
  have hprev := st302_p39
  have hstep := st302_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p41 : ((-3553044058211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT302 (i+1))
      = (∑ i ∈ Finset.range 40, stT302 (i+1)) + stT302 41 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 40
    simpa using h
  have hprev := st302_p40
  have hstep := st302_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p42 : ((-4241170871749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT302 (i+1))
      = (∑ i ∈ Finset.range 41, stT302 (i+1)) + stT302 42 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 41
    simpa using h
  have hprev := st302_p41
  have hstep := st302_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p43 : ((-1851417195957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT302 (i+1))
      = (∑ i ∈ Finset.range 42, stT302 (i+1)) + stT302 43 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 42
    simpa using h
  have hprev := st302_p42
  have hstep := st302_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p44 : ((-241796099623/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT302 (i+1))
      = (∑ i ∈ Finset.range 43, stT302 (i+1)) + stT302 44 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 43
    simpa using h
  have hprev := st302_p43
  have hstep := st302_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p45 : ((-464510480449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT302 (i+1))
      = (∑ i ∈ Finset.range 44, stT302 (i+1)) + stT302 45 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 44
    simpa using h
  have hprev := st302_p44
  have hstep := st302_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p46 : ((95192645027/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT302 (i+1))
      = (∑ i ∈ Finset.range 45, stT302 (i+1)) + stT302 46 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 45
    simpa using h
  have hprev := st302_p45
  have hstep := st302_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p47 : ((871011210859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT302 (i+1))
      = (∑ i ∈ Finset.range 46, stT302 (i+1)) + stT302 47 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 46
    simpa using h
  have hprev := st302_p46
  have hstep := st302_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p48 : ((2937657980093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT302 (i+1))
      = (∑ i ∈ Finset.range 47, stT302 (i+1)) + stT302 48 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 47
    simpa using h
  have hprev := st302_p47
  have hstep := st302_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p49 : ((4164091897877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT302 (i+1))
      = (∑ i ∈ Finset.range 48, stT302 (i+1)) + stT302 49 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 48
    simpa using h
  have hprev := st302_p48
  have hstep := st302_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p50 : ((5489333929621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT302 (i+1))
      = (∑ i ∈ Finset.range 49, stT302 (i+1)) + stT302 50 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 49
    simpa using h
  have hprev := st302_p49
  have hstep := st302_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p51 : ((6887468700661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT302 (i+1))
      = (∑ i ∈ Finset.range 50, stT302 (i+1)) + stT302 51 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 50
    simpa using h
  have hprev := st302_p50
  have hstep := st302_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p52 : ((8182526790661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT302 (i+1))
      = (∑ i ∈ Finset.range 51, stT302 (i+1)) + stT302 52 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 51
    simpa using h
  have hprev := st302_p51
  have hstep := st302_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p53 : ((9040499704131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT302 (i+1))
      = (∑ i ∈ Finset.range 52, stT302 (i+1)) + stT302 53 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 52
    simpa using h
  have hprev := st302_p52
  have hstep := st302_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p54 : ((4545074738613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT302 (i+1))
      = (∑ i ∈ Finset.range 53, stT302 (i+1)) + stT302 54 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 53
    simpa using h
  have hprev := st302_p53
  have hstep := st302_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p55 : ((4108019195013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT302 (i+1))
      = (∑ i ∈ Finset.range 54, stT302 (i+1)) + stT302 55 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 54
    simpa using h
  have hprev := st302_p54
  have hstep := st302_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p56 : ((6879983952049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT302 (i+1))
      = (∑ i ∈ Finset.range 55, stT302 (i+1)) + stT302 56 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 55
    simpa using h
  have hprev := st302_p55
  have hstep := st302_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p57 : ((6070980388177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT302 (i+1))
      = (∑ i ∈ Finset.range 56, stT302 (i+1)) + stT302 57 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 56
    simpa using h
  have hprev := st302_p56
  have hstep := st302_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p58 : ((6550489038889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT302 (i+1))
      = (∑ i ∈ Finset.range 57, stT302 (i+1)) + stT302 58 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 57
    simpa using h
  have hprev := st302_p57
  have hstep := st302_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p59 : ((784847107/1000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT302 (i+1))
      = (∑ i ∈ Finset.range 58, stT302 (i+1)) + stT302 59 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 58
    simpa using h
  have hprev := st302_p58
  have hstep := st302_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p60 : ((4198843514237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT302 (i+1))
      = (∑ i ∈ Finset.range 59, stT302 (i+1)) + stT302 60 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 59
    simpa using h
  have hprev := st302_p59
  have hstep := st302_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p61 : ((371706242581/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT302 (i+1))
      = (∑ i ∈ Finset.range 60, stT302 (i+1)) + stT302 61 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 60
    simpa using h
  have hprev := st302_p60
  have hstep := st302_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p62 : ((3212839246759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT302 (i+1))
      = (∑ i ∈ Finset.range 61, stT302 (i+1)) + stT302 62 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 61
    simpa using h
  have hprev := st302_p61
  have hstep := st302_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p63 : ((3533287459347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT302 (i+1))
      = (∑ i ∈ Finset.range 62, stT302 (i+1)) + stT302 63 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 62
    simpa using h
  have hprev := st302_p62
  have hstep := st302_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p64 : ((4084628084347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT302 (i+1))
      = (∑ i ∈ Finset.range 63, stT302 (i+1)) + stT302 64 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 63
    simpa using h
  have hprev := st302_p63
  have hstep := st302_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p65 : ((3776248423369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT302 (i+1))
      = (∑ i ∈ Finset.range 64, stT302 (i+1)) + stT302 65 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 64
    simpa using h
  have hprev := st302_p64
  have hstep := st302_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p66 : ((1637981973587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT302 (i+1))
      = (∑ i ∈ Finset.range 65, stT302 (i+1)) + stT302 66 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 65
    simpa using h
  have hprev := st302_p65
  have hstep := st302_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p67 : ((1855522915697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT302 (i+1))
      = (∑ i ∈ Finset.range 66, stT302 (i+1)) + stT302 67 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 66
    simpa using h
  have hprev := st302_p66
  have hstep := st302_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p68 : ((804515227973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT302 (i+1))
      = (∑ i ∈ Finset.range 67, stT302 (i+1)) + stT302 68 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 67
    simpa using h
  have hprev := st302_p67
  have hstep := st302_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p69 : ((6874588408093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT302 (i+1))
      = (∑ i ∈ Finset.range 68, stT302 (i+1)) + stT302 69 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 68
    simpa using h
  have hprev := st302_p68
  have hstep := st302_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p70 : ((7030406696769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT302 (i+1))
      = (∑ i ∈ Finset.range 69, stT302 (i+1)) + stT302 70 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 69
    simpa using h
  have hprev := st302_p69
  have hstep := st302_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p71 : ((401806085319/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT302 (i+1))
      = (∑ i ∈ Finset.range 70, stT302 (i+1)) + stT302 71 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 70
    simpa using h
  have hprev := st302_p70
  have hstep := st302_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p72 : ((350745285151/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT302 (i+1))
      = (∑ i ∈ Finset.range 71, stT302 (i+1)) + stT302 72 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 71
    simpa using h
  have hprev := st302_p71
  have hstep := st302_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p73 : ((352145096707/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT302 (i+1))
      = (∑ i ∈ Finset.range 72, stT302 (i+1)) + stT302 73 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 72
    simpa using h
  have hprev := st302_p72
  have hstep := st302_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p74 : ((1995948433469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT302 (i+1))
      = (∑ i ∈ Finset.range 73, stT302 (i+1)) + stT302 74 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 73
    simpa using h
  have hprev := st302_p73
  have hstep := st302_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p75 : ((343772352541/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT302 (i+1))
      = (∑ i ∈ Finset.range 74, stT302 (i+1)) + stT302 75 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 74
    simpa using h
  have hprev := st302_p74
  have hstep := st302_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p76 : ((3675545486533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT302 (i+1))
      = (∑ i ∈ Finset.range 75, stT302 (i+1)) + stT302 76 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 75
    simpa using h
  have hprev := st302_p75
  have hstep := st302_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p77 : ((7772098667031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT302 (i+1))
      = (∑ i ∈ Finset.range 76, stT302 (i+1)) + stT302 77 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 76
    simpa using h
  have hprev := st302_p76
  have hstep := st302_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p78 : ((269845572267/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT302 (i+1))
      = (∑ i ∈ Finset.range 77, stT302 (i+1)) + stT302 78 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 77
    simpa using h
  have hprev := st302_p77
  have hstep := st302_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p79 : ((7830792930069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT302 (i+1))
      = (∑ i ∈ Finset.range 78, stT302 (i+1)) + stT302 79 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 78
    simpa using h
  have hprev := st302_p78
  have hstep := st302_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p80 : ((7158465420237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT302 (i+1))
      = (∑ i ∈ Finset.range 79, stT302 (i+1)) + stT302 80 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 79
    simpa using h
  have hprev := st302_p79
  have hstep := st302_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p81 : ((359865104151/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT302 (i+1))
      = (∑ i ∈ Finset.range 80, stT302 (i+1)) + stT302 81 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 80
    simpa using h
  have hprev := st302_p80
  have hstep := st302_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p82 : ((1550885579241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT302 (i+1))
      = (∑ i ∈ Finset.range 81, stT302 (i+1)) + stT302 82 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 81
    simpa using h
  have hprev := st302_p81
  have hstep := st302_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p83 : ((1360659656769/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT302 (i+1))
      = (∑ i ∈ Finset.range 82, stT302 (i+1)) + stT302 83 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 82
    simpa using h
  have hprev := st302_p82
  have hstep := st302_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p84 : ((1973260492777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT302 (i+1))
      = (∑ i ∈ Finset.range 83, stT302 (i+1)) + stT302 84 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 83
    simpa using h
  have hprev := st302_p83
  have hstep := st302_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p85 : ((1377520019009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT302 (i+1))
      = (∑ i ∈ Finset.range 84, stT302 (i+1)) + stT302 85 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 84
    simpa using h
  have hprev := st302_p84
  have hstep := st302_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p86 : ((7657564392817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT302 (i+1))
      = (∑ i ∈ Finset.range 85, stT302 (i+1)) + stT302 86 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 85
    simpa using h
  have hprev := st302_p85
  have hstep := st302_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p87 : ((3597693063767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT302 (i+1))
      = (∑ i ∈ Finset.range 86, stT302 (i+1)) + stT302 87 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 86
    simpa using h
  have hprev := st302_p86
  have hstep := st302_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p88 : ((7339508667131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT302 (i+1))
      = (∑ i ∈ Finset.range 87, stT302 (i+1)) + stT302 88 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 87
    simpa using h
  have hprev := st302_p87
  have hstep := st302_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p89 : ((7482216063241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT302 (i+1))
      = (∑ i ∈ Finset.range 88, stT302 (i+1)) + stT302 89 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 88
    simpa using h
  have hprev := st302_p88
  have hstep := st302_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p90 : ((1420602907847/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT302 (i+1))
      = (∑ i ∈ Finset.range 89, stT302 (i+1)) + stT302 90 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 89
    simpa using h
  have hprev := st302_p89
  have hstep := st302_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p91 : ((7662713284231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT302 (i+1))
      = (∑ i ∈ Finset.range 90, stT302 (i+1)) + stT302 91 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 90
    simpa using h
  have hprev := st302_p90
  have hstep := st302_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p92 : ((3486664805861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT302 (i+1))
      = (∑ i ∈ Finset.range 91, stT302 (i+1)) + stT302 92 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 91
    simpa using h
  have hprev := st302_p91
  have hstep := st302_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p93 : ((7749266564659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT302 (i+1))
      = (∑ i ∈ Finset.range 92, stT302 (i+1)) + stT302 93 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 92
    simpa using h
  have hprev := st302_p92
  have hstep := st302_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p94 : ((6919886725973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT302 (i+1))
      = (∑ i ∈ Finset.range 93, stT302 (i+1)) + stT302 94 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 93
    simpa using h
  have hprev := st302_p93
  have hstep := st302_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p95 : ((7776522953161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT302 (i+1))
      = (∑ i ∈ Finset.range 94, stT302 (i+1)) + stT302 95 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 94
    simpa using h
  have hprev := st302_p94
  have hstep := st302_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p96 : ((1382538766733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT302 (i+1))
      = (∑ i ∈ Finset.range 95, stT302 (i+1)) + stT302 96 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 95
    simpa using h
  have hprev := st302_p95
  have hstep := st302_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p97 : ((7765287992633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT302 (i+1))
      = (∑ i ∈ Finset.range 96, stT302 (i+1)) + stT302 97 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 96
    simpa using h
  have hprev := st302_p96
  have hstep := st302_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p98 : ((6941871876213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT302 (i+1))
      = (∑ i ∈ Finset.range 97, stT302 (i+1)) + stT302 98 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 97
    simpa using h
  have hprev := st302_p97
  have hstep := st302_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p99 : ((7714616684477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT302 (i+1))
      = (∑ i ∈ Finset.range 98, stT302 (i+1)) + stT302 99 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 98
    simpa using h
  have hprev := st302_p98
  have hstep := st302_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p100 : ((7017786684477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT302 (i+1))
      = (∑ i ∈ Finset.range 99, stT302 (i+1)) + stT302 100 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 99
    simpa using h
  have hprev := st302_p99
  have hstep := st302_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p101 : ((4754578257/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT302 (i+1))
      = (∑ i ∈ Finset.range 100, stT302 (i+1)) + stT302 101 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 100
    simpa using h
  have hprev := st302_p100
  have hstep := st302_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p102 : ((358025798773/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT302 (i+1))
      = (∑ i ∈ Finset.range 101, stT302 (i+1)) + stT302 102 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 101
    simpa using h
  have hprev := st302_p101
  have hstep := st302_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p103 : ((7425901532333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT302 (i+1))
      = (∑ i ∈ Finset.range 102, stT302 (i+1)) + stT302 103 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 102
    simpa using h
  have hprev := st302_p102
  have hstep := st302_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p104 : ((7377666752943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT302 (i+1))
      = (∑ i ∈ Finset.range 103, stT302 (i+1)) + stT302 104 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 103
    simpa using h
  have hprev := st302_p103
  have hstep := st302_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p105 : ((718130278503/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT302 (i+1))
      = (∑ i ∈ Finset.range 104, stT302 (i+1)) + stT302 105 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 104
    simpa using h
  have hprev := st302_p104
  have hstep := st302_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p106 : ((47693956209/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT302 (i+1))
      = (∑ i ∈ Finset.range 105, stT302 (i+1)) + stT302 106 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 105
    simpa using h
  have hprev := st302_p105
  have hstep := st302_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p107 : ((1389197730837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT302 (i+1))
      = (∑ i ∈ Finset.range 106, stT302 (i+1)) + stT302 107 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 106
    simpa using h
  have hprev := st302_p106
  have hstep := st302_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p108 : ((1562374248237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT302 (i+1))
      = (∑ i ∈ Finset.range 107, stT302 (i+1)) + stT302 108 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 107
    simpa using h
  have hprev := st302_p107
  have hstep := st302_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p109 : ((1714520849411/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT302 (i+1))
      = (∑ i ∈ Finset.range 108, stT302 (i+1)) + stT302 109 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 108
    simpa using h
  have hprev := st302_p108
  have hstep := st302_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p110 : ((60714590437/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT302 (i+1))
      = (∑ i ∈ Finset.range 109, stT302 (i+1)) + stT302 110 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 109
    simpa using h
  have hprev := st302_p109
  have hstep := st302_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p111 : ((1761223205471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT302 (i+1))
      = (∑ i ∈ Finset.range 110, stT302 (i+1)) + stT302 111 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 110
    simpa using h
  have hprev := st302_p110
  have hstep := st302_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p112 : ((1861514169189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT302 (i+1))
      = (∑ i ∈ Finset.range 111, stT302 (i+1)) + stT302 112 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 111
    simpa using h
  have hprev := st302_p111
  have hstep := st302_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p113 : ((1865849947669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT302 (i+1))
      = (∑ i ∈ Finset.range 112, stT302 (i+1)) + stT302 113 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 112
    simpa using h
  have hprev := st302_p112
  have hstep := st302_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p114 : ((350741751909/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT302 (i+1))
      = (∑ i ∈ Finset.range 113, stT302 (i+1)) + stT302 114 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 113
    simpa using h
  have hprev := st302_p113
  have hstep := st302_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p115 : ((1950274308343/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT302 (i+1))
      = (∑ i ∈ Finset.range 114, stT302 (i+1)) + stT302 115 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 114
    simpa using h
  have hprev := st302_p114
  have hstep := st302_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p116 : ((6873291522243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT302 (i+1))
      = (∑ i ∈ Finset.range 115, stT302 (i+1)) + stT302 116 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 115
    simpa using h
  have hprev := st302_p115
  have hstep := st302_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p117 : ((7680633335243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT302 (i+1))
      = (∑ i ∈ Finset.range 116, stT302 (i+1)) + stT302 117 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 116
    simpa using h
  have hprev := st302_p116
  have hstep := st302_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p118 : ((7246705579793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT302 (i+1))
      = (∑ i ∈ Finset.range 117, stT302 (i+1)) + stT302 118 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 117
    simpa using h
  have hprev := st302_p117
  have hstep := st302_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p119 : ((1788238464091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT302 (i+1))
      = (∑ i ∈ Finset.range 118, stT302 (i+1)) + stT302 119 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 118
    simpa using h
  have hprev := st302_p118
  have hstep := st302_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p120 : ((1938134456701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT302 (i+1))
      = (∑ i ∈ Finset.range 119, stT302 (i+1)) + stT302 120 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 119
    simpa using h
  have hprev := st302_p119
  have hstep := st302_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p121 : ((6865015010779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT302 (i+1))
      = (∑ i ∈ Finset.range 120, stT302 (i+1)) + stT302 121 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 120
    simpa using h
  have hprev := st302_p120
  have hstep := st302_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p122 : ((240159461639/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT302 (i+1))
      = (∑ i ∈ Finset.range 121, stT302 (i+1)) + stT302 122 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 121
    simpa using h
  have hprev := st302_p121
  have hstep := st302_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p123 : ((3643464904399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT302 (i+1))
      = (∑ i ∈ Finset.range 122, stT302 (i+1)) + stT302 123 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 122
    simpa using h
  have hprev := st302_p122
  have hstep := st302_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p124 : ((1768567906759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT302 (i+1))
      = (∑ i ∈ Finset.range 123, stT302 (i+1)) + stT302 124 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 123
    simpa using h
  have hprev := st302_p123
  have hstep := st302_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p125 : ((780423317913/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT302 (i+1))
      = (∑ i ∈ Finset.range 124, stT302 (i+1)) + stT302 125 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 124
    simpa using h
  have hprev := st302_p124
  have hstep := st302_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p126 : ((6919599167001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT302 (i+1))
      = (∑ i ∈ Finset.range 125, stT302 (i+1)) + stT302 126 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 125
    simpa using h
  have hprev := st302_p125
  have hstep := st302_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p127 : ((7489327861513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT302 (i+1))
      = (∑ i ∈ Finset.range 126, stT302 (i+1)) + stT302 127 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 126
    simpa using h
  have hprev := st302_p126
  have hstep := st302_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p128 : ((7556036279289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT302 (i+1))
      = (∑ i ∈ Finset.range 127, stT302 (i+1)) + stT302 128 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 127
    simpa using h
  have hprev := st302_p127
  have hstep := st302_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p129 : ((86058665903/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT302 (i+1))
      = (∑ i ∈ Finset.range 128, stT302 (i+1)) + stT302 129 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 128
    simpa using h
  have hprev := st302_p128
  have hstep := st302_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p130 : ((121199415099/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT302 (i+1))
      = (∑ i ∈ Finset.range 129, stT302 (i+1)) + stT302 130 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 129
    simpa using h
  have hprev := st302_p129
  have hstep := st302_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p131 : ((1809140526039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT302 (i+1))
      = (∑ i ∈ Finset.range 130, stT302 (i+1)) + stT302 131 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 130
    simpa using h
  have hprev := st302_p130
  have hstep := st302_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p132 : ((3528637077801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT302 (i+1))
      = (∑ i ∈ Finset.range 131, stT302 (i+1)) + stT302 132 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 131
    simpa using h
  have hprev := st302_p131
  have hstep := st302_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p133 : ((3908847032121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT302 (i+1))
      = (∑ i ∈ Finset.range 132, stT302 (i+1)) + stT302 133 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 132
    simpa using h
  have hprev := st302_p132
  have hstep := st302_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p134 : ((3507414018773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT302 (i+1))
      = (∑ i ∈ Finset.range 133, stT302 (i+1)) + stT302 134 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 133
    simpa using h
  have hprev := st302_p133
  have hstep := st302_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p135 : ((3632992350531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT302 (i+1))
      = (∑ i ∈ Finset.range 134, stT302 (i+1)) + stT302 135 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 134
    simpa using h
  have hprev := st302_p134
  have hstep := st302_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p136 : ((3880867991717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT302 (i+1))
      = (∑ i ∈ Finset.range 135, stT302 (i+1)) + stT302 136 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 135
    simpa using h
  have hprev := st302_p135
  have hstep := st302_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p137 : ((1726890417601/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT302 (i+1))
      = (∑ i ∈ Finset.range 136, stT302 (i+1)) + stT302 137 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 136
    simpa using h
  have hprev := st302_p136
  have hstep := st302_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p138 : ((1855775470723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT302 (i+1))
      = (∑ i ∈ Finset.range 137, stT302 (i+1)) + stT302 138 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 137
    simpa using h
  have hprev := st302_p137
  have hstep := st302_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p139 : ((1920519357139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT302 (i+1))
      = (∑ i ∈ Finset.range 138, stT302 (i+1)) + stT302 139 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 138
    simpa using h
  have hprev := st302_p138
  have hstep := st302_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p140 : ((3435311069513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT302 (i+1))
      = (∑ i ∈ Finset.range 139, stT302 (i+1)) + stT302 140 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 139
    simpa using h
  have hprev := st302_p139
  have hstep := st302_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p141 : ((7510051392457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT302 (i+1))
      = (∑ i ∈ Finset.range 140, stT302 (i+1)) + stT302 141 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 140
    simpa using h
  have hprev := st302_p140
  have hstep := st302_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p142 : ((953896403171/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT302 (i+1))
      = (∑ i ∈ Finset.range 141, stT302 (i+1)) + stT302 142 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 141
    simpa using h
  have hprev := st302_p141
  have hstep := st302_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p143 : ((857753545461/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT302 (i+1))
      = (∑ i ∈ Finset.range 142, stT302 (i+1)) + stT302 143 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 142
    simpa using h
  have hprev := st302_p142
  have hstep := st302_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p144 : ((18833953571/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT302 (i+1))
      = (∑ i ∈ Finset.range 143, stT302 (i+1)) + stT302 144 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 143
    simpa using h
  have hprev := st302_p143
  have hstep := st302_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p145 : ((76282116617/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT302 (i+1))
      = (∑ i ∈ Finset.range 144, stT302 (i+1)) + stT302 145 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 144
    simpa using h
  have hprev := st302_p144
  have hstep := st302_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p146 : ((3431416264617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT302 (i+1))
      = (∑ i ∈ Finset.range 145, stT302 (i+1)) + stT302 146 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 145
    simpa using h
  have hprev := st302_p145
  have hstep := st302_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p147 : ((3749523028241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT302 (i+1))
      = (∑ i ∈ Finset.range 146, stT302 (i+1)) + stT302 147 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 146
    simpa using h
  have hprev := st302_p146
  have hstep := st302_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p148 : ((959088693857/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT302 (i+1))
      = (∑ i ∈ Finset.range 147, stT302 (i+1)) + stT302 148 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 147
    simpa using h
  have hprev := st302_p147
  have hstep := st302_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p149 : ((859856043333/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT302 (i+1))
      = (∑ i ∈ Finset.range 148, stT302 (i+1)) + stT302 149 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 148
    simpa using h
  have hprev := st302_p148
  have hstep := st302_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p150 : ((925531613527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT302 (i+1))
      = (∑ i ∈ Finset.range 149, stT302 (i+1)) + stT302 150 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 149
    simpa using h
  have hprev := st302_p149
  have hstep := st302_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p151 : ((193691541969/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT302 (i+1))
      = (∑ i ∈ Finset.range 150, stT302 (i+1)) + stT302 151 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 150
    simpa using h
  have hprev := st302_p150
  have hstep := st302_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p152 : ((433533895203/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT302 (i+1))
      = (∑ i ∈ Finset.range 151, stT302 (i+1)) + stT302 152 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 151
    simpa using h
  have hprev := st302_p151
  have hstep := st302_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p153 : ((1812152209377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT302 (i+1))
      = (∑ i ∈ Finset.range 152, stT302 (i+1)) + stT302 153 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 152
    simpa using h
  have hprev := st302_p152
  have hstep := st302_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p154 : ((390697710649/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT302 (i+1))
      = (∑ i ∈ Finset.range 153, stT302 (i+1)) + stT302 154 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 153
    simpa using h
  have hprev := st302_p153
  have hstep := st302_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p155 : ((35360746087/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT302 (i+1))
      = (∑ i ∈ Finset.range 154, stT302 (i+1)) + stT302 155 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 154
    simpa using h
  have hprev := st302_p154
  have hstep := st302_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p156 : ((7054045923749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT302 (i+1))
      = (∑ i ∈ Finset.range 155, stT302 (i+1)) + stT302 156 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 155
    simpa using h
  have hprev := st302_p155
  have hstep := st302_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p157 : ((1561463240501/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT302 (i+1))
      = (∑ i ∈ Finset.range 156, stT302 (i+1)) + stT302 157 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 156
    simpa using h
  have hprev := st302_p156
  have hstep := st302_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p158 : ((7305097143823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT302 (i+1))
      = (∑ i ∈ Finset.range 157, stT302 (i+1)) + stT302 158 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 157
    simpa using h
  have hprev := st302_p157
  have hstep := st302_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p159 : ((6888377660747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT302 (i+1))
      = (∑ i ∈ Finset.range 158, stT302 (i+1)) + stT302 159 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 158
    simpa using h
  have hprev := st302_p158
  have hstep := st302_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p160 : ((7657955472659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT302 (i+1))
      = (∑ i ∈ Finset.range 159, stT302 (i+1)) + stT302 160 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 159
    simpa using h
  have hprev := st302_p159
  have hstep := st302_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p161 : ((189866576659/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT302 (i+1))
      = (∑ i ∈ Finset.range 160, stT302 (i+1)) + stT302 161 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 160
    simpa using h
  have hprev := st302_p160
  have hstep := st302_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p162 : ((343240278053/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT302 (i+1))
      = (∑ i ∈ Finset.range 161, stT302 (i+1)) + stT302 162 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 161
    simpa using h
  have hprev := st302_p161
  have hstep := st302_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p163 : ((91867224699/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT302 (i+1))
      = (∑ i ∈ Finset.range 162, stT302 (i+1)) + stT302 163 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 162
    simpa using h
  have hprev := st302_p162
  have hstep := st302_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p164 : ((195191539911/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT302 (i+1))
      = (∑ i ∈ Finset.range 163, stT302 (i+1)) + stT302 164 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 163
    simpa using h
  have hprev := st302_p163
  have hstep := st302_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p165 : ((7079614781133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT302 (i+1))
      = (∑ i ∈ Finset.range 164, stT302 (i+1)) + stT302 165 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 164
    simpa using h
  have hprev := st302_p164
  have hstep := st302_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p166 : ((6995647661349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT302 (i+1))
      = (∑ i ∈ Finset.range 165, stT302 (i+1)) + stT302 166 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 165
    simpa using h
  have hprev := st302_p165
  have hstep := st302_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p167 : ((3881189286777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT302 (i+1))
      = (∑ i ∈ Finset.range 166, stT302 (i+1)) + stT302 167 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 166
    simpa using h
  have hprev := st302_p166
  have hstep := st302_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p168 : ((1871380696043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT302 (i+1))
      = (∑ i ∈ Finset.range 167, stT302 (i+1)) + stT302 168 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 167
    simpa using h
  have hprev := st302_p167
  have hstep := st302_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p169 : ((6845592592193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT302 (i+1))
      = (∑ i ∈ Finset.range 168, stT302 (i+1)) + stT302 169 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 168
    simpa using h
  have hprev := st302_p168
  have hstep := st302_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p170 : ((1479070937657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT302 (i+1))
      = (∑ i ∈ Finset.range 169, stT302 (i+1)) + stT302 170 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 169
    simpa using h
  have hprev := st302_p169
  have hstep := st302_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p171 : ((7808576717687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT302 (i+1))
      = (∑ i ∈ Finset.range 170, stT302 (i+1)) + stT302 171 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 170
    simpa using h
  have hprev := st302_p170
  have hstep := st302_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p172 : ((7100640091837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT302 (i+1))
      = (∑ i ∈ Finset.range 171, stT302 (i+1)) + stT302 172 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 171
    simpa using h
  have hprev := st302_p171
  have hstep := st302_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p173 : ((6948833786217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT302 (i+1))
      = (∑ i ∈ Finset.range 172, stT302 (i+1)) + stT302 173 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 172
    simpa using h
  have hprev := st302_p172
  have hstep := st302_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p174 : ((7706489815083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT302 (i+1))
      = (∑ i ∈ Finset.range 173, stT302 (i+1)) + stT302 174 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 173
    simpa using h
  have hprev := st302_p173
  have hstep := st302_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p175 : ((3804660972747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT302 (i+1))
      = (∑ i ∈ Finset.range 174, stT302 (i+1)) + stT302 175 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 174
    simpa using h
  have hprev := st302_p174
  have hstep := st302_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p176 : ((6884573236121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT302 (i+1))
      = (∑ i ∈ Finset.range 175, stT302 (i+1)) + stT302 176 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 175
    simpa using h
  have hprev := st302_p175
  have hstep := st302_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p177 : ((7190352600319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT302 (i+1))
      = (∑ i ∈ Finset.range 176, stT302 (i+1)) + stT302 177 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 176
    simpa using h
  have hprev := st302_p176
  have hstep := st302_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p178 : ((7829395235609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT302 (i+1))
      = (∑ i ∈ Finset.range 177, stT302 (i+1)) + stT302 178 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 177
    simpa using h
  have hprev := st302_p177
  have hstep := st302_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p179 : ((1472943004369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT302 (i+1))
      = (∑ i ∈ Finset.range 178, stT302 (i+1)) + stT302 179 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 178
    simpa using h
  have hprev := st302_p178
  have hstep := st302_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p180 : ((6836031029621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT302 (i+1))
      = (∑ i ∈ Finset.range 179, stT302 (i+1)) + stT302 180 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 179
    simpa using h
  have hprev := st302_p179
  have hstep := st302_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p181 : ((7411095298601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT302 (i+1))
      = (∑ i ∈ Finset.range 180, stT302 (i+1)) + stT302 181 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 180
    simpa using h
  have hprev := st302_p180
  have hstep := st302_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p182 : ((978152684833/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT302 (i+1))
      = (∑ i ∈ Finset.range 181, stT302 (i+1)) + stT302 182 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 181
    simpa using h
  have hprev := st302_p181
  have hstep := st302_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p183 : ((717960198597/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT302 (i+1))
      = (∑ i ∈ Finset.range 182, stT302 (i+1)) + stT302 183 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 182
    simpa using h
  have hprev := st302_p182
  have hstep := st302_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p184 : ((34347889521/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT302 (i+1))
      = (∑ i ∈ Finset.range 183, stT302 (i+1)) + stT302 184 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 183
    simpa using h
  have hprev := st302_p183
  have hstep := st302_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p185 : ((1888883509157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT302 (i+1))
      = (∑ i ∈ Finset.range 184, stT302 (i+1)) + stT302 185 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 184
    simpa using h
  have hprev := st302_p184
  have hstep := st302_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p186 : ((486223649393/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT302 (i+1))
      = (∑ i ∈ Finset.range 185, stT302 (i+1)) + stT302 186 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 185
    simpa using h
  have hprev := st302_p185
  have hstep := st302_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p187 : ((1768301674621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT302 (i+1))
      = (∑ i ∈ Finset.range 186, stT302 (i+1)) + stT302 187 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 186
    simpa using h
  have hprev := st302_p186
  have hstep := st302_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p188 : ((3456190162717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT302 (i+1))
      = (∑ i ∈ Finset.range 187, stT302 (i+1)) + stT302 188 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 187
    simpa using h
  have hprev := st302_p187
  have hstep := st302_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p189 : ((3813243255277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT302 (i+1))
      = (∑ i ∈ Finset.range 188, stT302 (i+1)) + stT302 189 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 188
    simpa using h
  have hprev := st302_p188
  have hstep := st302_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p190 : ((3873874186501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT302 (i+1))
      = (∑ i ∈ Finset.range 189, stT302 (i+1)) + stT302 190 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 189
    simpa using h
  have hprev := st302_p189
  have hstep := st302_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p191 : ((3516305128751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT302 (i+1))
      = (∑ i ∈ Finset.range 190, stT302 (i+1)) + stT302 191 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 190
    simpa using h
  have hprev := st302_p190
  have hstep := st302_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p192 : ((3463309413847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT302 (i+1))
      = (∑ i ∈ Finset.range 191, stT302 (i+1)) + stT302 192 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 191
    simpa using h
  have hprev := st302_p191
  have hstep := st302_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p193 : ((7638358223209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT302 (i+1))
      = (∑ i ∈ Finset.range 192, stT302 (i+1)) + stT302 193 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 192
    simpa using h
  have hprev := st302_p192
  have hstep := st302_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p194 : ((310087676001/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT302 (i+1))
      = (∑ i ∈ Finset.range 193, stT302 (i+1)) + stT302 194 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 193
    simpa using h
  have hprev := st302_p193
  have hstep := st302_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p195 : ((88090576821/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT302 (i+1))
      = (∑ i ∈ Finset.range 194, stT302 (i+1)) + stT302 195 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 194
    simpa using h
  have hprev := st302_p194
  have hstep := st302_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p196 : ((1725712593409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT302 (i+1))
      = (∑ i ∈ Finset.range 195, stT302 (i+1)) + stT302 196 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 195
    simpa using h
  have hprev := st302_p195
  have hstep := st302_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p197 : ((118676183479/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT302 (i+1))
      = (∑ i ∈ Finset.range 196, stT302 (i+1)) + stT302 197 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 196
    simpa using h
  have hprev := st302_p196
  have hstep := st302_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p198 : ((389546714453/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT302 (i+1))
      = (∑ i ∈ Finset.range 197, stT302 (i+1)) + stT302 198 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 197
    simpa using h
  have hprev := st302_p197
  have hstep := st302_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p199 : ((3559932381911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT302 (i+1))
      = (∑ i ∈ Finset.range 198, stT302 (i+1)) + stT302 199 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 198
    simpa using h
  have hprev := st302_p198
  have hstep := st302_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p200 : ((6853955055151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT302 (i+1))
      = (∑ i ∈ Finset.range 199, stT302 (i+1)) + stT302 200 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 199
    simpa using h
  have hprev := st302_p199
  have hstep := st302_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p201 : ((7489020890041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT302 (i+1))
      = (∑ i ∈ Finset.range 200, stT302 (i+1)) + stT302 201 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 200
    simpa using h
  have hprev := st302_p200
  have hstep := st302_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p202 : ((7839790731227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT302 (i+1))
      = (∑ i ∈ Finset.range 201, stT302 (i+1)) + stT302 202 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 201
    simpa using h
  have hprev := st302_p201
  have hstep := st302_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p203 : ((7261026079071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT302 (i+1))
      = (∑ i ∈ Finset.range 202, stT302 (i+1)) + stT302 203 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 202
    simpa using h
  have hprev := st302_p202
  have hstep := st302_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p204 : ((852031200803/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT302 (i+1))
      = (∑ i ∈ Finset.range 203, stT302 (i+1)) + stT302 204 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 203
    simpa using h
  have hprev := st302_p203
  have hstep := st302_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p205 : ((456975081619/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT302 (i+1))
      = (∑ i ∈ Finset.range 204, stT302 (i+1)) + stT302 205 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 204
    simpa using h
  have hprev := st302_p204
  have hstep := st302_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p206 : ((7850056773561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT302 (i+1))
      = (∑ i ∈ Finset.range 205, stT302 (i+1)) + stT302 206 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 205
    simpa using h
  have hprev := st302_p205
  have hstep := st302_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p207 : ((1493930735133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT302 (i+1))
      = (∑ i ∈ Finset.range 206, stT302 (i+1)) + stT302 207 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 206
    simpa using h
  have hprev := st302_p206
  have hstep := st302_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p208 : ((1369882301853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT302 (i+1))
      = (∑ i ∈ Finset.range 207, stT302 (i+1)) + stT302 208 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 207
    simpa using h
  have hprev := st302_p207
  have hstep := st302_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p209 : ((7080873539659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT302 (i+1))
      = (∑ i ∈ Finset.range 208, stT302 (i+1)) + stT302 209 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 208
    simpa using h
  have hprev := st302_p208
  have hstep := st302_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p210 : ((7755413457289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT302 (i+1))
      = (∑ i ∈ Finset.range 209, stT302 (i+1)) + stT302 210 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 209
    simpa using h
  have hprev := st302_p209
  have hstep := st302_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p211 : ((385155985101/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT302 (i+1))
      = (∑ i ∈ Finset.range 210, stT302 (i+1)) + stT302 211 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 210
    simpa using h
  have hprev := st302_p210
  have hstep := st302_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p212 : ((3508893917023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT302 (i+1))
      = (∑ i ∈ Finset.range 211, stT302 (i+1)) + stT302 212 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 211
    simpa using h
  have hprev := st302_p211
  have hstep := st302_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p213 : ((6870471513857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT302 (i+1))
      = (∑ i ∈ Finset.range 212, stT302 (i+1)) + stT302 213 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 212
    simpa using h
  have hprev := st302_p212
  have hstep := st302_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p214 : ((3753510540381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT302 (i+1))
      = (∑ i ∈ Finset.range 213, stT302 (i+1)) + stT302 214 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 213
    simpa using h
  have hprev := st302_p213
  have hstep := st302_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p215 : ((785508490259/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT302 (i+1))
      = (∑ i ∈ Finset.range 214, stT302 (i+1)) + stT302 215 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 214
    simpa using h
  have hprev := st302_p214
  have hstep := st302_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p216 : ((3668428552643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT302 (i+1))
      = (∑ i ∈ Finset.range 215, stT302 (i+1)) + stT302 216 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 215
    simpa using h
  have hprev := st302_p215
  have hstep := st302_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p217 : ((6813142443531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT302 (i+1))
      = (∑ i ∈ Finset.range 216, stT302 (i+1)) + stT302 217 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 216
    simpa using h
  have hprev := st302_p216
  have hstep := st302_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p218 : ((7142231161321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT302 (i+1))
      = (∑ i ∈ Finset.range 217, stT302 (i+1)) + stT302 218 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 217
    simpa using h
  have hprev := st302_p217
  have hstep := st302_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p219 : ((1945959340297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT302 (i+1))
      = (∑ i ∈ Finset.range 218, stT302 (i+1)) + stT302 219 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 218
    simpa using h
  have hprev := st302_p218
  have hstep := st302_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p220 : ((1925108862547/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT302 (i+1))
      = (∑ i ∈ Finset.range 219, stT302 (i+1)) + stT302 220 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 219
    simpa using h
  have hprev := st302_p219
  have hstep := st302_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p221 : ((3514850546887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT302 (i+1))
      = (∑ i ∈ Finset.range 220, stT302 (i+1)) + stT302 221 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 220
    simpa using h
  have hprev := st302_p220
  have hstep := st302_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p222 : ((6841171079003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT302 (i+1))
      = (∑ i ∈ Finset.range 221, stT302 (i+1)) + stT302 222 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 221
    simpa using h
  have hprev := st302_p221
  have hstep := st302_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p223 : ((742937937657/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT302 (i+1))
      = (∑ i ∈ Finset.range 222, stT302 (i+1)) + stT302 223 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 222
    simpa using h
  have hprev := st302_p222
  have hstep := st302_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p224 : ((3934357013789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT302 (i+1))
      = (∑ i ∈ Finset.range 223, stT302 (i+1)) + stT302 224 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 223
    simpa using h
  have hprev := st302_p223
  have hstep := st302_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p225 : ((1869300791289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT302 (i+1))
      = (∑ i ∈ Finset.range 224, stT302 (i+1)) + stT302 225 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 224
    simpa using h
  have hprev := st302_p224
  have hstep := st302_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p226 : ((6863421451591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT302 (i+1))
      = (∑ i ∈ Finset.range 225, stT302 (i+1)) + stT302 226 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 225
    simpa using h
  have hprev := st302_p225
  have hstep := st302_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p227 : ((6968141011639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT302 (i+1))
      = (∑ i ∈ Finset.range 226, stT302 (i+1)) + stT302 227 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 226
    simpa using h
  have hprev := st302_p226
  have hstep := st302_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p228 : ((7627961925567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT302 (i+1))
      = (∑ i ∈ Finset.range 227, stT302 (i+1)) + stT302 228 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 227
    simpa using h
  have hprev := st302_p227
  have hstep := st302_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p229 : ((7844471674269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT302 (i+1))
      = (∑ i ∈ Finset.range 228, stT302 (i+1)) + stT302 229 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 228
    simpa using h
  have hprev := st302_p228
  have hstep := st302_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p230 : ((3648029940451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT302 (i+1))
      = (∑ i ∈ Finset.range 229, stT302 (i+1)) + stT302 230 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 229
    simpa using h
  have hprev := st302_p229
  have hstep := st302_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p231 : ((3400973899091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT302 (i+1))
      = (∑ i ∈ Finset.range 230, stT302 (i+1)) + stT302 231 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 230
    simpa using h
  have hprev := st302_p230
  have hstep := st302_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p232 : ((709047325969/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT302 (i+1))
      = (∑ i ∈ Finset.range 231, stT302 (i+1)) + stT302 232 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 231
    simpa using h
  have hprev := st302_p231
  have hstep := st302_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p233 : ((3867279700783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT302 (i+1))
      = (∑ i ∈ Finset.range 232, stT302 (i+1)) + stT302 233 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 232
    simpa using h
  have hprev := st302_p232
  have hstep := st302_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p234 : ((3897980680003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT302 (i+1))
      = (∑ i ∈ Finset.range 233, stT302 (i+1)) + stT302 234 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 233
    simpa using h
  have hprev := st302_p233
  have hstep := st302_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p235 : ((7189405633607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT302 (i+1))
      = (∑ i ∈ Finset.range 234, stT302 (i+1)) + stT302 235 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 234
    simpa using h
  have hprev := st302_p234
  have hstep := st302_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p236 : ((6787398926177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT302 (i+1))
      = (∑ i ∈ Finset.range 235, stT302 (i+1)) + stT302 236 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 235
    simpa using h
  have hprev := st302_p235
  have hstep := st302_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p237 : ((7160206062347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT302 (i+1))
      = (∑ i ∈ Finset.range 236, stT302 (i+1)) + stT302 237 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 236
    simpa using h
  have hprev := st302_p236
  have hstep := st302_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p238 : ((7777011405433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT302 (i+1))
      = (∑ i ∈ Finset.range 237, stT302 (i+1)) + stT302 238 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 237
    simpa using h
  have hprev := st302_p237
  have hstep := st302_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p239 : ((3885998200321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT302 (i+1))
      = (∑ i ∈ Finset.range 238, stT302 (i+1)) + stT302 239 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 238
    simpa using h
  have hprev := st302_p238
  have hstep := st302_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p240 : ((3577840037113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT302 (i+1))
      = (∑ i ∈ Finset.range 239, stT302 (i+1)) + stT302 240 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 239
    simpa using h
  have hprev := st302_p239
  have hstep := st302_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p241 : ((6782779519397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT302 (i+1))
      = (∑ i ∈ Finset.range 240, stT302 (i+1)) + stT302 241 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 240
    simpa using h
  have hprev := st302_p240
  have hstep := st302_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p242 : ((7163127552189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT302 (i+1))
      = (∑ i ∈ Finset.range 241, stT302 (i+1)) + stT302 242 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 241
    simpa using h
  have hprev := st302_p241
  have hstep := st302_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p243 : ((7774408411689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT302 (i+1))
      = (∑ i ∈ Finset.range 242, stT302 (i+1)) + stT302 243 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 242
    simpa using h
  have hprev := st302_p242
  have hstep := st302_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p244 : ((7788883612113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT302 (i+1))
      = (∑ i ∈ Finset.range 243, stT302 (i+1)) + stT302 244 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 243
    simpa using h
  have hprev := st302_p243
  have hstep := st302_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p245 : ((719052483033/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT302 (i+1))
      = (∑ i ∈ Finset.range 244, stT302 (i+1)) + stT302 245 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 244
    simpa using h
  have hprev := st302_p244
  have hstep := st302_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p246 : ((3390107988721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT302 (i+1))
      = (∑ i ∈ Finset.range 245, stT302 (i+1)) + stT302 246 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 245
    simpa using h
  have hprev := st302_p245
  have hstep := st302_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p247 : ((3549853767903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT302 (i+1))
      = (∑ i ∈ Finset.range 246, stT302 (i+1)) + stT302 247 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 246
    simpa using h
  have hprev := st302_p246
  have hstep := st302_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p248 : ((3862441090403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT302 (i+1))
      = (∑ i ∈ Finset.range 247, stT302 (i+1)) + stT302 248 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 247
    simpa using h
  have hprev := st302_p247
  have hstep := st302_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p249 : ((3919121364963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT302 (i+1))
      = (∑ i ∈ Finset.range 248, stT302 (i+1)) + stT302 249 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 248
    simpa using h
  have hprev := st302_p248
  have hstep := st302_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p250 : ((3647906839623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT302 (i+1))
      = (∑ i ∈ Finset.range 249, stT302 (i+1)) + stT302 250 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 249
    simpa using h
  have hprev := st302_p249
  have hstep := st302_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p251 : ((6799163574251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT302 (i+1))
      = (∑ i ∈ Finset.range 250, stT302 (i+1)) + stT302 251 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 250
    simpa using h
  have hprev := st302_p250
  have hstep := st302_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p252 : ((6982412490311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT302 (i+1))
      = (∑ i ∈ Finset.range 251, stT302 (i+1)) + stT302 252 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 251
    simpa using h
  have hprev := st302_p251
  have hstep := st302_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p253 : ((7609058833953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT302 (i+1))
      = (∑ i ∈ Finset.range 252, stT302 (i+1)) + stT302 253 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 252
    simpa using h
  have hprev := st302_p252
  have hstep := st302_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p254 : ((7886963673093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT302 (i+1))
      = (∑ i ∈ Finset.range 253, stT302 (i+1)) + stT302 254 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 253
    simpa using h
  have hprev := st302_p253
  have hstep := st302_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p255 : ((7470366239393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT302 (i+1))
      = (∑ i ∈ Finset.range 254, stT302 (i+1)) + stT302 255 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 254
    simpa using h
  have hprev := st302_p254
  have hstep := st302_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p256 : ((1720213042793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT302 (i+1))
      = (∑ i ∈ Finset.range 255, stT302 (i+1)) + stT302 256 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 255
    simpa using h
  have hprev := st302_p255
  have hstep := st302_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p257 : ((6846797985853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT302 (i+1))
      = (∑ i ∈ Finset.range 256, stT302 (i+1)) + stT302 257 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 256
    simpa using h
  have hprev := st302_p256
  have hstep := st302_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p258 : ((7406650214857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT302 (i+1))
      = (∑ i ∈ Finset.range 257, stT302 (i+1)) + stT302 258 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 257
    simpa using h
  have hprev := st302_p257
  have hstep := st302_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p259 : ((787545883387/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT302 (i+1))
      = (∑ i ∈ Finset.range 258, stT302 (i+1)) + stT302 259 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 258
    simpa using h
  have hprev := st302_p258
  have hstep := st302_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p260 : ((384346451937/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT302 (i+1))
      = (∑ i ∈ Finset.range 259, stT302 (i+1)) + stT302 260 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 259
    simpa using h
  have hprev := st302_p259
  have hstep := st302_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p261 : ((1414228714441/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT302 (i+1))
      = (∑ i ∈ Finset.range 260, stT302 (i+1)) + stT302 261 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 260
    simpa using h
  have hprev := st302_p260
  have hstep := st302_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p262 : ((3382424291531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT302 (i+1))
      = (∑ i ∈ Finset.range 261, stT302 (i+1)) + stT302 262 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 261
    simpa using h
  have hprev := st302_p261
  have hstep := st302_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p263 : ((1782247571119/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT302 (i+1))
      = (∑ i ∈ Finset.range 262, stT302 (i+1)) + stT302 263 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 262
    simpa using h
  have hprev := st302_p262
  have hstep := st302_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p264 : ((483201550393/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT302 (i+1))
      = (∑ i ∈ Finset.range 263, stT302 (i+1)) + stT302 264 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 263
    simpa using h
  have hprev := st302_p263
  have hstep := st302_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p265 : ((491645649463/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT302 (i+1))
      = (∑ i ∈ Finset.range 264, stT302 (i+1)) + stT302 265 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 264
    simpa using h
  have hprev := st302_p264
  have hstep := st302_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p266 : ((461255058793/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT302 (i+1))
      = (∑ i ∈ Finset.range 265, stT302 (i+1)) + stT302 266 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 265
    simpa using h
  have hprev := st302_p265
  have hstep := st302_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p267 : ((1367326219343/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT302 (i+1))
      = (∑ i ∈ Finset.range 266, stT302 (i+1)) + stT302 267 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 266
    simpa using h
  have hprev := st302_p266
  have hstep := st302_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p268 : ((3429339198743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT302 (i+1))
      = (∑ i ∈ Finset.range 267, stT302 (i+1)) + stT302 268 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 267
    simpa using h
  have hprev := st302_p267
  have hstep := st302_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p269 : ((3708918670693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT302 (i+1))
      = (∑ i ∈ Finset.range 268, stT302 (i+1)) + stT302 269 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 268
    simpa using h
  have hprev := st302_p268
  have hstep := st302_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p270 : ((3939496548223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT302 (i+1))
      = (∑ i ∈ Finset.range 269, stT302 (i+1)) + stT302 270 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 269
    simpa using h
  have hprev := st302_p269
  have hstep := st302_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p271 : ((3862428478633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT302 (i+1))
      = (∑ i ∈ Finset.range 270, stT302 (i+1)) + stT302 271 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 270
    simpa using h
  have hprev := st302_p270
  have hstep := st302_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p272 : ((3565394033093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT302 (i+1))
      = (∑ i ∈ Finset.range 271, stT302 (i+1)) + stT302 272 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 271
    simpa using h
  have hprev := st302_p271
  have hstep := st302_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p273 : ((3378734152543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT302 (i+1))
      = (∑ i ∈ Finset.range 272, stT302 (i+1)) + stT302 273 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 272
    simpa using h
  have hprev := st302_p272
  have hstep := st302_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p274 : ((3507270169873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT302 (i+1))
      = (∑ i ∈ Finset.range 273, stT302 (i+1)) + stT302 274 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 273
    simpa using h
  have hprev := st302_p273
  have hstep := st302_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p275 : ((3808606293493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT302 (i+1))
      = (∑ i ∈ Finset.range 274, stT302 (i+1)) + stT302 275 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 274
    simpa using h
  have hprev := st302_p274
  have hstep := st302_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p276 : ((7908675637721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT302 (i+1))
      = (∑ i ∈ Finset.range 275, stT302 (i+1)) + stT302 276 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 275
    simpa using h
  have hprev := st302_p275
  have hstep := st302_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p277 : ((7575997834109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT302 (i+1))
      = (∑ i ∈ Finset.range 276, stT302 (i+1)) + stT302 277 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 276
    simpa using h
  have hprev := st302_p276
  have hstep := st302_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p278 : ((1744856740717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT302 (i+1))
      = (∑ i ∈ Finset.range 277, stT302 (i+1)) + stT302 278 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 277
    simpa using h
  have hprev := st302_p277
  have hstep := st302_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p279 : ((6756035438023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT302 (i+1))
      = (∑ i ∈ Finset.range 278, stT302 (i+1)) + stT302 279 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 278
    simpa using h
  have hprev := st302_p278
  have hstep := st302_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p280 : ((7140166776873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT302 (i+1))
      = (∑ i ∈ Finset.range 279, stT302 (i+1)) + stT302 280 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 279
    simpa using h
  have hprev := st302_p279
  have hstep := st302_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p281 : ((61794212297/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT302 (i+1))
      = (∑ i ∈ Finset.range 280, stT302 (i+1)) + stT302 281 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 280
    simpa using h
  have hprev := st302_p280
  have hstep := st302_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p282 : ((1579343764181/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT302 (i+1))
      = (∑ i ∈ Finset.range 281, stT302 (i+1)) + stT302 282 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 281
    simpa using h
  have hprev := st302_p281
  have hstep := st302_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p283 : ((1870166700933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT302 (i+1))
      = (∑ i ∈ Finset.range 282, stT302 (i+1)) + stT302 283 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 282
    simpa using h
  have hprev := st302_p282
  have hstep := st302_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p284 : ((1727163030279/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT302 (i+1))
      = (∑ i ∈ Finset.range 283, stT302 (i+1)) + stT302 284 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 283
    simpa using h
  have hprev := st302_p283
  have hstep := st302_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p285 : ((3383984024459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT302 (i+1))
      = (∑ i ∈ Finset.range 284, stT302 (i+1)) + stT302 285 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 284
    simpa using h
  have hprev := st302_p284
  have hstep := st302_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p286 : ((3599743425299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT302 (i+1))
      = (∑ i ∈ Finset.range 285, stT302 (i+1)) + stT302 286 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 285
    simpa using h
  have hprev := st302_p285
  have hstep := st302_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p287 : ((7763094823051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT302 (i+1))
      = (∑ i ∈ Finset.range 286, stT302 (i+1)) + stT302 287 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 286
    simpa using h
  have hprev := st302_p286
  have hstep := st302_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p288 : ((7891025619081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT302 (i+1))
      = (∑ i ∈ Finset.range 287, stT302 (i+1)) + stT302 288 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 287
    simpa using h
  have hprev := st302_p287
  have hstep := st302_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p289 : ((7457746863853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT302 (i+1))
      = (∑ i ∈ Finset.range 288, stT302 (i+1)) + stT302 289 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 288
    simpa using h
  have hprev := st302_p288
  have hstep := st302_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p290 : ((6896737060409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT302 (i+1))
      = (∑ i ∈ Finset.range 289, stT302 (i+1)) + stT302 290 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 289
    simpa using h
  have hprev := st302_p289
  have hstep := st302_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p291 : ((6762477155079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT302 (i+1))
      = (∑ i ∈ Finset.range 290, stT302 (i+1)) + stT302 291 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 290
    simpa using h
  have hprev := st302_p290
  have hstep := st302_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p292 : ((7184277703749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT302 (i+1))
      = (∑ i ∈ Finset.range 291, stT302 (i+1)) + stT302 292 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 291
    simpa using h
  have hprev := st302_p291
  have hstep := st302_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p293 : ((7747764253753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT302 (i+1))
      = (∑ i ∈ Finset.range 292, stT302 (i+1)) + stT302 293 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 292
    simpa using h
  have hprev := st302_p292
  have hstep := st302_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p294 : ((7906135200803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT302 (i+1))
      = (∑ i ∈ Finset.range 293, stT302 (i+1)) + stT302 294 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 293
    simpa using h
  have hprev := st302_p293
  have hstep := st302_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p295 : ((938632025461/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT302 (i+1))
      = (∑ i ∈ Finset.range 294, stT302 (i+1)) + stT302 295 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 294
    simpa using h
  have hprev := st302_p294
  have hstep := st302_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p296 : ((3469763422291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT302 (i+1))
      = (∑ i ∈ Finset.range 295, stT302 (i+1)) + stT302 296 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 295
    simpa using h
  have hprev := st302_p295
  have hstep := st302_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p297 : ((3370065641947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT302 (i+1))
      = (∑ i ∈ Finset.range 296, stT302 (i+1)) + stT302 297 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 296
    simpa using h
  have hprev := st302_p296
  have hstep := st302_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p298 : ((3548634569219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT302 (i+1))
      = (∑ i ∈ Finset.range 297, stT302 (i+1)) + stT302 298 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 297
    simpa using h
  have hprev := st302_p297
  have hstep := st302_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p299 : ((3836158988797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT302 (i+1))
      = (∑ i ∈ Finset.range 298, stT302 (i+1)) + stT302 299 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 298
    simpa using h
  have hprev := st302_p298
  have hstep := st302_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p300 : ((3963530481697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT302 (i+1))
      = (∑ i ∈ Finset.range 299, stT302 (i+1)) + stT302 300 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 299
    simpa using h
  have hprev := st302_p299
  have hstep := st302_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p301 : ((7626754912093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT302 (i+1))
      = (∑ i ∈ Finset.range 300, stT302 (i+1)) + stT302 301 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 300
    simpa using h
  have hprev := st302_p300
  have hstep := st302_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p302 : ((7051390841593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT302 (i+1))
      = (∑ i ∈ Finset.range 301, stT302 (i+1)) + stT302 302 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 301
    simpa using h
  have hprev := st302_p301
  have hstep := st302_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p303 : ((6729972228943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT302 (i+1))
      = (∑ i ∈ Finset.range 302, stT302 (i+1)) + stT302 303 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 302
    simpa using h
  have hprev := st302_p302
  have hstep := st302_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p304 : ((3477003156253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT302 (i+1))
      = (∑ i ∈ Finset.range 303, stT302 (i+1)) + stT302 304 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 303
    simpa using h
  have hprev := st302_p303
  have hstep := st302_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p305 : ((1879384592093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT302 (i+1))
      = (∑ i ∈ Finset.range 304, stT302 (i+1)) + stT302 305 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 304
    simpa using h
  have hprev := st302_p304
  have hstep := st302_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p306 : ((7911247587343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT302 (i+1))
      = (∑ i ∈ Finset.range 305, stT302 (i+1)) + stT302 306 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 305
    simpa using h
  have hprev := st302_p305
  have hstep := st302_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p307 : ((7783602457731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT302 (i+1))
      = (∑ i ∈ Finset.range 306, stT302 (i+1)) + stT302 307 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 306
    simpa using h
  have hprev := st302_p306
  have hstep := st302_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p308 : ((290036839343/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT302 (i+1))
      = (∑ i ∈ Finset.range 307, stT302 (i+1)) + stT302 308 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 307
    simpa using h
  have hprev := st302_p307
  have hstep := st302_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p309 : ((1357289342701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT302 (i+1))
      = (∑ i ∈ Finset.range 308, stT302 (i+1)) + stT302 309 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 308
    simpa using h
  have hprev := st302_p308
  have hstep := st302_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p310 : ((6798125127587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT302 (i+1))
      = (∑ i ∈ Finset.range 309, stT302 (i+1)) + stT302 310 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 309
    simpa using h
  have hprev := st302_p309
  have hstep := st302_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p311 : ((3636581824207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT302 (i+1))
      = (∑ i ∈ Finset.range 310, stT302 (i+1)) + stT302 311 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 310
    simpa using h
  have hprev := st302_p310
  have hstep := st302_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p312 : ((77963017689/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT302 (i+1))
      = (∑ i ∈ Finset.range 311, stT302 (i+1)) + stT302 312 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 311
    simpa using h
  have hprev := st302_p311
  have hstep := st302_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p313 : ((7915398057699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT302 (i+1))
      = (∑ i ∈ Finset.range 312, stT302 (i+1)) + stT302 313 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 312
    simpa using h
  have hprev := st302_p312
  have hstep := st302_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p314 : ((7530289317837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT302 (i+1))
      = (∑ i ∈ Finset.range 313, stT302 (i+1)) + stT302 314 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 313
    simpa using h
  have hprev := st302_p313
  have hstep := st302_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p315 : ((348616981539/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT302 (i+1))
      = (∑ i ∈ Finset.range 314, stT302 (i+1)) + stT302 315 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 314
    simpa using h
  have hprev := st302_p314
  have hstep := st302_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p316 : ((67159208247/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT302 (i+1))
      = (∑ i ∈ Finset.range 315, stT302 (i+1)) + stT302 316 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 315
    simpa using h
  have hprev := st302_p315
  have hstep := st302_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p317 : ((279028686129/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT302 (i+1))
      = (∑ i ∈ Finset.range 316, stT302 (i+1)) + stT302 317 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 316
    simpa using h
  have hprev := st302_p316
  have hstep := st302_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p318 : ((7531053029457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT302 (i+1))
      = (∑ i ∈ Finset.range 317, stT302 (i+1)) + stT302 318 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 317
    simpa using h
  have hprev := st302_p317
  have hstep := st302_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p319 : ((7917207742397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT302 (i+1))
      = (∑ i ∈ Finset.range 318, stT302 (i+1)) + stT302 319 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 318
    simpa using h
  have hprev := st302_p318
  have hstep := st302_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p320 : ((1953718941857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT302 (i+1))
      = (∑ i ∈ Finset.range 319, stT302 (i+1)) + stT302 320 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 319
    simpa using h
  have hprev := st302_p319
  have hstep := st302_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p321 : ((3655455895189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT302 (i+1))
      = (∑ i ∈ Finset.range 320, stT302 (i+1)) + stT302 321 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 320
    simpa using h
  have hprev := st302_p320
  have hstep := st302_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p322 : ((1705106226911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT302 (i+1))
      = (∑ i ∈ Finset.range 321, stT302 (i+1)) + stT302 322 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 321
    simpa using h
  have hprev := st302_p321
  have hstep := st302_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p323 : ((842873996323/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT302 (i+1))
      = (∑ i ∈ Finset.range 322, stT302 (i+1)) + stT302 323 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 322
    simpa using h
  have hprev := st302_p322
  have hstep := st302_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p324 : ((7139147685539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT302 (i+1))
      = (∑ i ∈ Finset.range 323, stT302 (i+1)) + stT302 324 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 323
    simpa using h
  have hprev := st302_p323
  have hstep := st302_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p325 : ((7687238435039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT302 (i+1))
      = (∑ i ∈ Finset.range 324, stT302 (i+1)) + stT302 325 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 324
    simpa using h
  have hprev := st302_p324
  have hstep := st302_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p326 : ((7947407425343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT302 (i+1))
      = (∑ i ∈ Finset.range 325, stT302 (i+1)) + stT302 326 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 325
    simpa using h
  have hprev := st302_p325
  have hstep := st302_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p327 : ((7713886846787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT302 (i+1))
      = (∑ i ∈ Finset.range 326, stT302 (i+1)) + stT302 327 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 326
    simpa using h
  have hprev := st302_p326
  have hstep := st302_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p328 : ((7174127554677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT302 (i+1))
      = (∑ i ∈ Finset.range 327, stT302 (i+1)) + stT302 328 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 327
    simpa using h
  have hprev := st302_p327
  have hstep := st302_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p329 : ((6754727823081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT302 (i+1))
      = (∑ i ∈ Finset.range 328, stT302 (i+1)) + stT302 329 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 328
    simpa using h
  have hprev := st302_p328
  have hstep := st302_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p330 : ((3391716327413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT302 (i+1))
      = (∑ i ∈ Finset.range 329, stT302 (i+1)) + stT302 330 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 329
    simpa using h
  have hprev := st302_p329
  have hstep := st302_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p331 : ((7235538195041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT302 (i+1))
      = (∑ i ∈ Finset.range 330, stT302 (i+1)) + stT302 331 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 330
    simpa using h
  have hprev := st302_p330
  have hstep := st302_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p332 : ((7758768769453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT302 (i+1))
      = (∑ i ∈ Finset.range 331, stT302 (i+1)) + stT302 332 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 331
    simpa using h
  have hprev := st302_p331
  have hstep := st302_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p333 : ((7949851686677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT302 (i+1))
      = (∑ i ∈ Finset.range 332, stT302 (i+1)) + stT302 333 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 332
    simpa using h
  have hprev := st302_p332
  have hstep := st302_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p334 : ((7664138813693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT302 (i+1))
      = (∑ i ∈ Finset.range 333, stT302 (i+1)) + stT302 334 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 333
    simpa using h
  have hprev := st302_p333
  have hstep := st302_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p335 : ((7121568266999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT302 (i+1))
      = (∑ i ∈ Finset.range 334, stT302 (i+1)) + stT302 335 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 334
    simpa using h
  have hprev := st302_p334
  have hstep := st302_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p336 : ((3367120841177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT302 (i+1))
      = (∑ i ∈ Finset.range 335, stT302 (i+1)) + stT302 336 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 335
    simpa using h
  have hprev := st302_p335
  have hstep := st302_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p337 : ((135859759517/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT302 (i+1))
      = (∑ i ∈ Finset.range 336, stT302 (i+1)) + stT302 337 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 336
    simpa using h
  have hprev := st302_p336
  have hstep := st302_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p338 : ((3625749033329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT302 (i+1))
      = (∑ i ∈ Finset.range 337, stT302 (i+1)) + stT302 338 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 337
    simpa using h
  have hprev := st302_p337
  have hstep := st302_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p339 : ((7766248587283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT302 (i+1))
      = (∑ i ∈ Finset.range 338, stT302 (i+1)) + stT302 339 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 338
    simpa using h
  have hprev := st302_p338
  have hstep := st302_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p340 : ((7955668958607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT302 (i+1))
      = (∑ i ∈ Finset.range 339, stT302 (i+1)) + stT302 340 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 339
    simpa using h
  have hprev := st302_p339
  have hstep := st302_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p341 : ((1536369628141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT302 (i+1))
      = (∑ i ∈ Finset.range 340, stT302 (i+1)) + stT302 341 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 340
    simpa using h
  have hprev := st302_p340
  have hstep := st302_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p342 : ((7147658571473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT302 (i+1))
      = (∑ i ∈ Finset.range 341, stT302 (i+1)) + stT302 342 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 341
    simpa using h
  have hprev := st302_p341
  have hstep := st302_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p343 : ((6743563231173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT302 (i+1))
      = (∑ i ∈ Finset.range 342, stT302 (i+1)) + stT302 343 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 342
    simpa using h
  have hprev := st302_p342
  have hstep := st302_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p344 : ((6761673716343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT302 (i+1))
      = (∑ i ∈ Finset.range 343, stT302 (i+1)) + stT302 344 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 343
    simpa using h
  have hprev := st302_p343
  have hstep := st302_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p345 : ((7186786891277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT302 (i+1))
      = (∑ i ∈ Finset.range 344, stT302 (i+1)) + stT302 345 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 344
    simpa using h
  have hprev := st302_p344
  have hstep := st302_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p346 : ((120501810581/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT302 (i+1))
      = (∑ i ∈ Finset.range 345, stT302 (i+1)) + stT302 346 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 345
    simpa using h
  have hprev := st302_p345
  have hstep := st302_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p347 : ((1990655189569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT302 (i+1))
      = (∑ i ∈ Finset.range 346, stT302 (i+1)) + stT302 347 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 346
    simpa using h
  have hprev := st302_p346
  have hstep := st302_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p348 : ((970251116353/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT302 (i+1))
      = (∑ i ∈ Finset.range 347, stT302 (i+1)) + stT302 348 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 347
    simpa using h
  have hprev := st302_p347
  have hstep := st302_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p349 : ((906745752431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT302 (i+1))
      = (∑ i ∈ Finset.range 348, stT302 (i+1)) + stT302 349 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 348
    simpa using h
  have hprev := st302_p348
  have hstep := st302_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p350 : ((6796367827947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT302 (i+1))
      = (∑ i ∈ Finset.range 349, stT302 (i+1)) + stT302 350 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 349
    simpa using h
  have hprev := st302_p349
  have hstep := st302_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p351 : ((3354105663713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT302 (i+1))
      = (∑ i ∈ Finset.range 350, stT302 (i+1)) + stT302 351 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 350
    simpa using h
  have hprev := st302_p350
  have hstep := st302_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p352 : ((1762201074109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT302 (i+1))
      = (∑ i ∈ Finset.range 351, stT302 (i+1)) + stT302 352 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 351
    simpa using h
  have hprev := st302_p351
  have hstep := st302_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p353 : ((947610396399/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT302 (i+1))
      = (∑ i ∈ Finset.range 352, stT302 (i+1)) + stT302 353 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 352
    simpa using h
  have hprev := st302_p352
  have hstep := st302_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p354 : ((992262801821/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT302 (i+1))
      = (∑ i ∈ Finset.range 353, stT302 (i+1)) + stT302 354 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 353
    simpa using h
  have hprev := st302_p353
  have hstep := st302_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p355 : ((7877306105563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT302 (i+1))
      = (∑ i ∈ Finset.range 354, stT302 (i+1)) + stT302 355 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 354
    simpa using h
  have hprev := st302_p354
  have hstep := st302_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p356 : ((7441801687271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT302 (i+1))
      = (∑ i ∈ Finset.range 355, stT302 (i+1)) + stT302 356 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 355
    simpa using h
  have hprev := st302_p355
  have hstep := st302_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p357 : ((3463864799929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT302 (i+1))
      = (∑ i ∈ Finset.range 356, stT302 (i+1)) + stT302 357 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 356
    simpa using h
  have hprev := st302_p356
  have hstep := st302_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p358 : ((3340521616537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT302 (i+1))
      = (∑ i ∈ Finset.range 357, stT302 (i+1)) + stT302 358 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 357
    simpa using h
  have hprev := st302_p357
  have hstep := st302_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p359 : ((54923040613/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT302 (i+1))
      = (∑ i ∈ Finset.range 358, stT302 (i+1)) + stT302 359 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 358
    simpa using h
  have hprev := st302_p358
  have hstep := st302_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p360 : ((7355973994127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT302 (i+1))
      = (∑ i ∈ Finset.range 359, stT302 (i+1)) + stT302 360 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 359
    simpa using h
  have hprev := st302_p359
  have hstep := st302_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p361 : ((7826614340797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT302 (i+1))
      = (∑ i ∈ Finset.range 360, stT302 (i+1)) + stT302 361 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 360
    simpa using h
  have hprev := st302_p360
  have hstep := st302_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p362 : ((7967502934489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT302 (i+1))
      = (∑ i ∈ Finset.range 361, stT302 (i+1)) + stT302 362 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 361
    simpa using h
  have hprev := st302_p361
  have hstep := st302_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p363 : ((7687932025433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT302 (i+1))
      = (∑ i ∈ Finset.range 362, stT302 (i+1)) + stT302 363 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 362
    simpa using h
  have hprev := st302_p362
  have hstep := st302_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p364 : ((3586026594057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT302 (i+1))
      = (∑ i ∈ Finset.range 363, stT302 (i+1)) + stT302 364 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 363
    simpa using h
  have hprev := st302_p363
  have hstep := st302_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p365 : ((3377680811401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT302 (i+1))
      = (∑ i ∈ Finset.range 364, stT302 (i+1)) + stT302 365 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 364
    simpa using h
  have hprev := st302_p364
  have hstep := st302_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p366 : ((1676514143417/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT302 (i+1))
      = (∑ i ∈ Finset.range 365, stT302 (i+1)) + stT302 366 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 365
    simpa using h
  have hprev := st302_p365
  have hstep := st302_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p367 : ((3526983642579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT302 (i+1))
      = (∑ i ∈ Finset.range 366, stT302 (i+1)) + stT302 367 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 366
    simpa using h
  have hprev := st302_p366
  have hstep := st302_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p368 : ((757510315479/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT302 (i+1))
      = (∑ i ∈ Finset.range 367, stT302 (i+1)) + stT302 368 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 367
    simpa using h
  have hprev := st302_p367
  have hstep := st302_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p369 : ((3968842172987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT302 (i+1))
      = (∑ i ∈ Finset.range 368, stT302 (i+1)) + stT302 369 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 368
    simpa using h
  have hprev := st302_p368
  have hstep := st302_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p370 : ((158267353319/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT302 (i+1))
      = (∑ i ∈ Finset.range 369, stT302 (i+1)) + stT302 370 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 369
    simpa using h
  have hprev := st302_p369
  have hstep := st302_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p371 : ((150385155401/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT302 (i+1))
      = (∑ i ∈ Finset.range 370, stT302 (i+1)) + stT302 371 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 370
    simpa using h
  have hprev := st302_p370
  have hstep := st302_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p372 : ((3501763290997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT302 (i+1))
      = (∑ i ∈ Finset.range 371, stT302 (i+1)) + stT302 372 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 371
    simpa using h
  have hprev := st302_p371
  have hstep := st302_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p373 : ((3343799699079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT302 (i+1))
      = (∑ i ∈ Finset.range 372, stT302 (i+1)) + stT302 373 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 372
    simpa using h
  have hprev := st302_p372
  have hstep := st302_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p374 : ((3383026953073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT302 (i+1))
      = (∑ i ∈ Finset.range 373, stT302 (i+1)) + stT302 374 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 373
    simpa using h
  have hprev := st302_p373
  have hstep := st302_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p375 : ((3594343835031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT302 (i+1))
      = (∑ i ∈ Finset.range 374, stT302 (i+1)) + stT302 375 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 374
    simpa using h
  have hprev := st302_p374
  have hstep := st302_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p376 : ((961855002079/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT302 (i+1))
      = (∑ i ∈ Finset.range 375, stT302 (i+1)) + stT302 376 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 375
    simpa using h
  have hprev := st302_p375
  have hstep := st302_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p377 : ((159509481577/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT302 (i+1))
      = (∑ i ∈ Finset.range 376, stT302 (i+1)) + stT302 377 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 376
    simpa using h
  have hprev := st302_p376
  have hstep := st302_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p378 : ((98267031573/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT302 (i+1))
      = (∑ i ∈ Finset.range 377, stT302 (i+1)) + stT302 378 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 377
    simpa using h
  have hprev := st302_p377
  have hstep := st302_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p379 : ((3711600402423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT302 (i+1))
      = (∑ i ∈ Finset.range 378, stT302 (i+1)) + stT302 379 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 378
    simpa using h
  have hprev := st302_p378
  have hstep := st302_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p380 : ((1731416670139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT302 (i+1))
      = (∑ i ∈ Finset.range 379, stT302 (i+1)) + stT302 380 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 379
    simpa using h
  have hprev := st302_p379
  have hstep := st302_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p381 : ((833294421947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT302 (i+1))
      = (∑ i ∈ Finset.range 380, stT302 (i+1)) + stT302 381 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 380
    simpa using h
  have hprev := st302_p380
  have hstep := st302_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p382 : ((106224159763/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT302 (i+1))
      = (∑ i ∈ Finset.range 381, stT302 (i+1)) + stT302 382 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 381
    simpa using h
  have hprev := st302_p381
  have hstep := st302_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p383 : ((113151038243/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT302 (i+1))
      = (∑ i ∈ Finset.range 382, stT302 (i+1)) + stT302 383 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 382
    simpa using h
  have hprev := st302_p382
  have hstep := st302_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p384 : ((1933452608043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT302 (i+1))
      = (∑ i ∈ Finset.range 383, stT302 (i+1)) + stT302 384 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 383
    simpa using h
  have hprev := st302_p383
  have hstep := st302_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p385 : ((1597231307621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT302 (i+1))
      = (∑ i ∈ Finset.range 384, stT302 (i+1)) + stT302 385 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 384
    simpa using h
  have hprev := st302_p384
  have hstep := st302_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p386 : ((7852660445719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT302 (i+1))
      = (∑ i ∈ Finset.range 385, stT302 (i+1)) + stT302 386 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 385
    simpa using h
  have hprev := st302_p385
  have hstep := st302_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p387 : ((7412524797727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT302 (i+1))
      = (∑ i ∈ Finset.range 386, stT302 (i+1)) + stT302 387 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 386
    simpa using h
  have hprev := st302_p386
  have hstep := st302_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p388 : ((1384248921307/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT302 (i+1))
      = (∑ i ∈ Finset.range 387, stT302 (i+1)) + stT302 388 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 387
    simpa using h
  have hprev := st302_p387
  have hstep := st302_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p389 : ((3330643160239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT302 (i+1))
      = (∑ i ∈ Finset.range 388, stT302 (i+1)) + stT302 389 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 388
    simpa using h
  have hprev := st302_p388
  have hstep := st302_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p390 : ((6780186318999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT302 (i+1))
      = (∑ i ∈ Finset.range 389, stT302 (i+1)) + stT302 390 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 389
    simpa using h
  have hprev := st302_p389
  have hstep := st302_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p391 : ((7208526948789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT302 (i+1))
      = (∑ i ∈ Finset.range 390, stT302 (i+1)) + stT302 391 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 390
    simpa using h
  have hprev := st302_p390
  have hstep := st302_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p392 : ((7702341269217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT302 (i+1))
      = (∑ i ∈ Finset.range 391, stT302 (i+1)) + stT302 392 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 391
    simpa using h
  have hprev := st302_p391
  have hstep := st302_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p393 : ((997881459511/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT302 (i+1))
      = (∑ i ∈ Finset.range 392, stT302 (i+1)) + stT302 393 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 392
    simpa using h
  have hprev := st302_p392
  have hstep := st302_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p394 : ((7894195185713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT302 (i+1))
      = (∑ i ∈ Finset.range 393, stT302 (i+1)) + stT302 394 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 393
    simpa using h
  have hprev := st302_p393
  have hstep := st302_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p395 : ((7487014989343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT302 (i+1))
      = (∑ i ∈ Finset.range 394, stT302 (i+1)) + stT302 395 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 394
    simpa using h
  have hprev := st302_p394
  have hstep := st302_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p396 : ((3494526667077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT302 (i+1))
      = (∑ i ∈ Finset.range 395, stT302 (i+1)) + stT302 396 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 395
    simpa using h
  have hprev := st302_p395
  have hstep := st302_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p397 : ((3337956302973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT302 (i+1))
      = (∑ i ∈ Finset.range 396, stT302 (i+1)) + stT302 397 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 396
    simpa using h
  have hprev := st302_p396
  have hstep := st302_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p398 : ((839873358241/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT302 (i+1))
      = (∑ i ∈ Finset.range 397, stT302 (i+1)) + stT302 398 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 397
    simpa using h
  have hprev := st302_p397
  have hstep := st302_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p399 : ((3546525554373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT302 (i+1))
      = (∑ i ∈ Finset.range 398, stT302 (i+1)) + stT302 399 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 398
    simpa using h
  have hprev := st302_p398
  have hstep := st302_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p400 : ((3796394554373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT302 (i+1))
      = (∑ i ∈ Finset.range 399, stT302 (i+1)) + stT302 400 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 399
    simpa using h
  have hprev := st302_p399
  have hstep := st302_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p401 : ((3973316479909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT302 (i+1))
      = (∑ i ∈ Finset.range 400, stT302 (i+1)) + stT302 401 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 400
    simpa using h
  have hprev := st302_p400
  have hstep := st302_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p402 : ((1991065354987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT302 (i+1))
      = (∑ i ∈ Finset.range 401, stT302 (i+1)) + stT302 402 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 401
    simpa using h
  have hprev := st302_p401
  have hstep := st302_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p403 : ((1909418747509/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT302 (i+1))
      = (∑ i ∈ Finset.range 402, stT302 (i+1)) + stT302 403 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 402
    simpa using h
  have hprev := st302_p402
  have hstep := st302_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p404 : ((1428595484057/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT302 (i+1))
      = (∑ i ∈ Finset.range 403, stT302 (i+1)) + stT302 404 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 403
    simpa using h
  have hprev := st302_p403
  have hstep := st302_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p405 : ((1348820528281/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT302 (i+1))
      = (∑ i ∈ Finset.range 404, stT302 (i+1)) + stT302 405 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 404
    simpa using h
  have hprev := st302_p404
  have hstep := st302_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p406 : ((6651828558721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT302 (i+1))
      = (∑ i ∈ Finset.range 405, stT302 (i+1)) + stT302 406 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 405
    simpa using h
  have hprev := st302_p405
  have hstep := st302_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p407 : ((345669946337/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT302 (i+1))
      = (∑ i ∈ Finset.range 406, stT302 (i+1)) + stT302 407 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 406
    simpa using h
  have hprev := st302_p406
  have hstep := st302_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p408 : ((3694998396263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT302 (i+1))
      = (∑ i ∈ Finset.range 407, stT302 (i+1)) + stT302 408 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 407
    simpa using h
  have hprev := st302_p407
  have hstep := st302_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p409 : ((3915888624627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT302 (i+1))
      = (∑ i ∈ Finset.range 408, stT302 (i+1)) + stT302 409 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 408
    simpa using h
  have hprev := st302_p408
  have hstep := st302_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p410 : ((4004628083603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT302 (i+1))
      = (∑ i ∈ Finset.range 409, stT302 (i+1)) + stT302 410 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 409
    simpa using h
  have hprev := st302_p409
  have hstep := st302_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p411 : ((1253080503/1600000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT302 (i+1))
      = (∑ i ∈ Finset.range 410, stT302 (i+1)) + stT302 411 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 410
    simpa using h
  have hprev := st302_p410
  have hstep := st302_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p412 : ((295688586961/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT302 (i+1))
      = (∑ i ∈ Finset.range 411, stT302 (i+1)) + stT302 412 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 411
    simpa using h
  have hprev := st302_p411
  have hstep := st302_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p413 : ((6917043797077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT302 (i+1))
      = (∑ i ∈ Finset.range 412, stT302 (i+1)) + stT302 413 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 412
    simpa using h
  have hprev := st302_p412
  have hstep := st302_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p414 : ((6648793847559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT302 (i+1))
      = (∑ i ∈ Finset.range 413, stT302 (i+1)) + stT302 414 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 413
    simpa using h
  have hprev := st302_p413
  have hstep := st302_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p415 : ((6722767009159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT302 (i+1))
      = (∑ i ∈ Finset.range 414, stT302 (i+1)) + stT302 415 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 414
    simpa using h
  have hprev := st302_p414
  have hstep := st302_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p416 : ((7100039280679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT302 (i+1))
      = (∑ i ∈ Finset.range 415, stT302 (i+1)) + stT302 416 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 415
    simpa using h
  have hprev := st302_p415
  have hstep := st302_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p417 : ((7589433747823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT302 (i+1))
      = (∑ i ∈ Finset.range 416, stT302 (i+1)) + stT302 417 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 416
    simpa using h
  have hprev := st302_p416
  have hstep := st302_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p418 : ((248290858229/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT302 (i+1))
      = (∑ i ∈ Finset.range 417, stT302 (i+1)) + stT302 418 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 417
    simpa using h
  have hprev := st302_p417
  have hstep := st302_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p419 : ((998847491101/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT302 (i+1))
      = (∑ i ∈ Finset.range 418, stT302 (i+1)) + stT302 419 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 418
    simpa using h
  have hprev := st302_p418
  have hstep := st302_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p420 : ((48153765767/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT302 (i+1))
      = (∑ i ∈ Finset.range 419, stT302 (i+1)) + stT302 420 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 419
    simpa using h
  have hprev := st302_p419
  have hstep := st302_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p421 : ((7229578092263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT302 (i+1))
      = (∑ i ∈ Finset.range 420, stT302 (i+1)) + stT302 421 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 420
    simpa using h
  have hprev := st302_p420
  have hstep := st302_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p422 : ((6800125413319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT302 (i+1))
      = (∑ i ∈ Finset.range 421, stT302 (i+1)) + stT302 422 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 421
    simpa using h
  have hprev := st302_p421
  have hstep := st302_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p423 : ((828284268627/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT302 (i+1))
      = (∑ i ∈ Finset.range 422, stT302 (i+1)) + stT302 423 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 422
    simpa using h
  have hprev := st302_p422
  have hstep := st302_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p424 : ((3395820296039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT302 (i+1))
      = (∑ i ∈ Finset.range 423, stT302 (i+1)) + stT302 424 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 423
    simpa using h
  have hprev := st302_p423
  have hstep := st302_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p425 : ((3607253043519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT302 (i+1))
      = (∑ i ∈ Finset.range 424, stT302 (i+1)) + stT302 425 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 424
    simpa using h
  have hprev := st302_p424
  have hstep := st302_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p426 : ((7689496816909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT302 (i+1))
      = (∑ i ∈ Finset.range 425, stT302 (i+1)) + stT302 426 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 425
    simpa using h
  have hprev := st302_p425
  have hstep := st302_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p427 : ((7987966366123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT302 (i+1))
      = (∑ i ∈ Finset.range 426, stT302 (i+1)) + stT302 427 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 426
    simpa using h
  have hprev := st302_p426
  have hstep := st302_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p428 : ((1593556948727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT302 (i+1))
      = (∑ i ∈ Finset.range 427, stT302 (i+1)) + stT302 428 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 427
    simpa using h
  have hprev := st302_p427
  have hstep := st302_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p429 : ((763988627947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT302 (i+1))
      = (∑ i ∈ Finset.range 428, stT302 (i+1)) + stT302 429 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 428
    simpa using h
  have hprev := st302_p428
  have hstep := st302_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p430 : ((7161131343089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT302 (i+1))
      = (∑ i ∈ Finset.range 429, stT302 (i+1)) + stT302 430 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 429
    simpa using h
  have hprev := st302_p429
  have hstep := st302_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p431 : ((6758253735593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT302 (i+1))
      = (∑ i ∈ Finset.range 430, stT302 (i+1)) + stT302 431 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 430
    simpa using h
  have hprev := st302_p430
  have hstep := st302_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p432 : ((6620348109087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT302 (i+1))
      = (∑ i ∈ Finset.range 431, stT302 (i+1)) + stT302 432 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 431
    simpa using h
  have hprev := st302_p431
  have hstep := st302_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p433 : ((1702709132469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT302 (i+1))
      = (∑ i ∈ Finset.range 432, stT302 (i+1)) + stT302 433 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 432
    simpa using h
  have hprev := st302_p432
  have hstep := st302_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p434 : ((7239521125851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT302 (i+1))
      = (∑ i ∈ Finset.range 433, stT302 (i+1)) + stT302 434 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 433
    simpa using h
  have hprev := st302_p433
  have hstep := st302_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p435 : ((1926615977133/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT302 (i+1))
      = (∑ i ∈ Finset.range 434, stT302 (i+1)) + stT302 435 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 434
    simpa using h
  have hprev := st302_p434
  have hstep := st302_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p436 : ((3997886189177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT302 (i+1))
      = (∑ i ∈ Finset.range 435, stT302 (i+1)) + stT302 436 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 435
    simpa using h
  have hprev := st302_p435
  have hstep := st302_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p437 : ((7975114185829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT302 (i+1))
      = (∑ i ∈ Finset.range 436, stT302 (i+1)) + stT302 437 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 436
    simpa using h
  have hprev := st302_p436
  have hstep := st302_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p438 : ((1913802755149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT302 (i+1))
      = (∑ i ∈ Finset.range 437, stT302 (i+1)) + stT302 438 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 437
    simpa using h
  have hprev := st302_p437
  have hstep := st302_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p439 : ((1795788644991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT302 (i+1))
      = (∑ i ∈ Finset.range 438, stT302 (i+1)) + stT302 439 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 438
    simpa using h
  have hprev := st302_p438
  have hstep := st302_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p440 : ((84672923937/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT302 (i+1))
      = (∑ i ∈ Finset.range 439, stT302 (i+1)) + stT302 440 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 439
    simpa using h
  have hprev := st302_p439
  have hstep := st302_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p441 : ((6611951355937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT302 (i+1))
      = (∑ i ∈ Finset.range 440, stT302 (i+1)) + stT302 441 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 440
    simpa using h
  have hprev := st302_p440
  have hstep := st302_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p442 : ((3384650969449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT302 (i+1))
      = (∑ i ∈ Finset.range 441, stT302 (i+1)) + stT302 442 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 441
    simpa using h
  have hprev := st302_p441
  have hstep := st302_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p443 : ((3587021501723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT302 (i+1))
      = (∑ i ∈ Finset.range 442, stT302 (i+1)) + stT302 443 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 442
    simpa using h
  have hprev := st302_p442
  have hstep := st302_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p444 : ((191114356921/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT302 (i+1))
      = (∑ i ∈ Finset.range 443, stT302 (i+1)) + stT302 444 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 443
    simpa using h
  have hprev := st302_p443
  have hstep := st302_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p445 : ((797161318189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT302 (i+1))
      = (∑ i ∈ Finset.range 444, stT302 (i+1)) + stT302 445 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 444
    simpa using h
  have hprev := st302_p444
  have hstep := st302_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p446 : ((2002773437201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT302 (i+1))
      = (∑ i ∈ Finset.range 445, stT302 (i+1)) + stT302 446 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 445
    simpa using h
  have hprev := st302_p445
  have hstep := st302_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p447 : ((1936700883289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT302 (i+1))
      = (∑ i ∈ Finset.range 446, stT302 (i+1)) + stT302 447 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 446
    simpa using h
  have hprev := st302_p446
  have hstep := st302_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p448 : ((364792072321/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT302 (i+1))
      = (∑ i ∈ Finset.range 447, stT302 (i+1)) + stT302 448 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 447
    simpa using h
  have hprev := st302_p447
  have hstep := st302_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p449 : ((685583609513/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT302 (i+1))
      = (∑ i ∈ Finset.range 448, stT302 (i+1)) + stT302 449 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 448
    simpa using h
  have hprev := st302_p448
  have hstep := st302_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p450 : ((165449858981/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT302 (i+1))
      = (∑ i ∈ Finset.range 449, stT302 (i+1)) + stT302 450 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 449
    simpa using h
  have hprev := st302_p449
  have hstep := st302_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p451 : ((1671106091799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT302 (i+1))
      = (∑ i ∈ Finset.range 450, stT302 (i+1)) + stT302 451 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 450
    simpa using h
  have hprev := st302_p450
  have hstep := st302_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p452 : ((1756305220759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT302 (i+1))
      = (∑ i ∈ Finset.range 451, stT302 (i+1)) + stT302 452 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 451
    simpa using h
  have hprev := st302_p451
  have hstep := st302_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p453 : ((1873247457079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT302 (i+1))
      = (∑ i ∈ Finset.range 452, stT302 (i+1)) + stT302 453 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 452
    simpa using h
  have hprev := st302_p452
  have hstep := st302_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p454 : ((3943645773383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT302 (i+1))
      = (∑ i ∈ Finset.range 453, stT302 (i+1)) + stT302 454 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 453
    simpa using h
  have hprev := st302_p453
  have hstep := st302_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p455 : ((4020300405953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT302 (i+1))
      = (∑ i ∈ Finset.range 454, stT302 (i+1)) + stT302 455 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 454
    simpa using h
  have hprev := st302_p454
  have hstep := st302_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p456 : ((7888914621397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT302 (i+1))
      = (∑ i ∈ Finset.range 455, stT302 (i+1)) + stT302 456 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 455
    simpa using h
  have hprev := st302_p455
  have hstep := st302_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p457 : ((1499492102321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT302 (i+1))
      = (∑ i ∈ Finset.range 456, stT302 (i+1)) + stT302 457 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 456
    simpa using h
  have hprev := st302_p456
  have hstep := st302_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p458 : ((1406332202059/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT302 (i+1))
      = (∑ i ∈ Finset.range 457, stT302 (i+1)) + stT302 458 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 457
    simpa using h
  have hprev := st302_p457
  have hstep := st302_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p459 : ((1671676140143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT302 (i+1))
      = (∑ i ∈ Finset.range 458, stT302 (i+1)) + stT302 459 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 458
    simpa using h
  have hprev := st302_p458
  have hstep := st302_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p460 : ((6605806401301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT302 (i+1))
      = (∑ i ∈ Finset.range 459, stT302 (i+1)) + stT302 460 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 459
    simpa using h
  have hprev := st302_p459
  have hstep := st302_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p461 : ((6821465429141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT302 (i+1))
      = (∑ i ∈ Finset.range 460, stT302 (i+1)) + stT302 461 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 460
    simpa using h
  have hprev := st302_p460
  have hstep := st302_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p462 : ((1448670956771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT302 (i+1))
      = (∑ i ∈ Finset.range 461, stT302 (i+1)) + stT302 462 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 461
    simpa using h
  have hprev := st302_p461
  have hstep := st302_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p463 : ((962129763473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT302 (i+1))
      = (∑ i ∈ Finset.range 462, stT302 (i+1)) + stT302 463 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 462
    simpa using h
  have hprev := st302_p462
  have hstep := st302_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p464 : ((3998232327107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT302 (i+1))
      = (∑ i ∈ Finset.range 463, stT302 (i+1)) + stT302 464 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 463
    simpa using h
  have hprev := st302_p463
  have hstep := st302_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p465 : ((200500992573/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT302 (i+1))
      = (∑ i ∈ Finset.range 464, stT302 (i+1)) + stT302 465 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 464
    simpa using h
  have hprev := st302_p464
  have hstep := st302_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p466 : ((3879635063277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT302 (i+1))
      = (∑ i ∈ Finset.range 465, stT302 (i+1)) + stT302 466 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 465
    simpa using h
  have hprev := st302_p465
  have hstep := st302_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p467 : ((7320796564549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT302 (i+1))
      = (∑ i ∈ Finset.range 466, stT302 (i+1)) + stT302 467 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 466
    simpa using h
  have hprev := st302_p466
  have hstep := st302_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p468 : ((6882015896823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT302 (i+1))
      = (∑ i ∈ Finset.range 467, stT302 (i+1)) + stT302 468 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 467
    simpa using h
  have hprev := st302_p467
  have hstep := st302_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p469 : ((1323804694991/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT302 (i+1))
      = (∑ i ∈ Finset.range 468, stT302 (i+1)) + stT302 469 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 468
    simpa using h
  have hprev := st302_p468
  have hstep := st302_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p470 : ((1327244809361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT302 (i+1))
      = (∑ i ∈ Finset.range 469, stT302 (i+1)) + stT302 470 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 469
    simpa using h
  have hprev := st302_p469
  have hstep := st302_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p471 : ((10821325537/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT302 (i+1))
      = (∑ i ∈ Finset.range 470, stT302 (i+1)) + stT302 471 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 470
    simpa using h
  have hprev := st302_p470
  have hstep := st302_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p472 : ((7371464380687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT302 (i+1))
      = (∑ i ∈ Finset.range 471, stT302 (i+1)) + stT302 472 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 471
    simpa using h
  have hprev := st302_p471
  have hstep := st302_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p473 : ((7797016637487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT302 (i+1))
      = (∑ i ∈ Finset.range 472, stT302 (i+1)) + stT302 473 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 472
    simpa using h
  have hprev := st302_p472
  have hstep := st302_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p474 : ((4017511553121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT302 (i+1))
      = (∑ i ∈ Finset.range 473, stT302 (i+1)) + stT302 474 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 473
    simpa using h
  have hprev := st302_p473
  have hstep := st302_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p475 : ((3996496588689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT302 (i+1))
      = (∑ i ∈ Finset.range 474, stT302 (i+1)) + stT302 475 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 474
    simpa using h
  have hprev := st302_p474
  have hstep := st302_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p476 : ((3844202009239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT302 (i+1))
      = (∑ i ∈ Finset.range 475, stT302 (i+1)) + stT302 476 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 475
    simpa using h
  have hprev := st302_p475
  have hstep := st302_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p477 : ((724057516991/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT302 (i+1))
      = (∑ i ∈ Finset.range 476, stT302 (i+1)) + stT302 477 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 476
    simpa using h
  have hprev := st302_p476
  have hstep := st302_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p478 : ((341165119471/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT302 (i+1))
      = (∑ i ∈ Finset.range 477, stT302 (i+1)) + stT302 478 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 477
    simpa using h
  have hprev := st302_p477
  have hstep := st302_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p479 : ((1649306496779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT302 (i+1))
      = (∑ i ∈ Finset.range 478, stT302 (i+1)) + stT302 479 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 478
    simpa using h
  have hprev := st302_p478
  have hstep := st302_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p480 : ((3324181112953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT302 (i+1))
      = (∑ i ∈ Finset.range 479, stT302 (i+1)) + stT302 480 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 479
    simpa using h
  have hprev := st302_p479
  have hstep := st302_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p481 : ((3478027716453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT302 (i+1))
      = (∑ i ∈ Finset.range 480, stT302 (i+1)) + stT302 481 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 480
    simpa using h
  have hprev := st302_p480
  have hstep := st302_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p482 : ((7402170787881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT302 (i+1))
      = (∑ i ∈ Finset.range 481, stT302 (i+1)) + stT302 482 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 481
    simpa using h
  have hprev := st302_p481
  have hstep := st302_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p483 : ((7817001593171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT302 (i+1))
      = (∑ i ∈ Finset.range 482, stT302 (i+1)) + stT302 483 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 482
    simpa using h
  have hprev := st302_p482
  have hstep := st302_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p484 : ((8043986820731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT302 (i+1))
      = (∑ i ∈ Finset.range 483, stT302 (i+1)) + stT302 484 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 483
    simpa using h
  have hprev := st302_p483
  have hstep := st302_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p485 : ((3999233935933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT302 (i+1))
      = (∑ i ∈ Finset.range 484, stT302 (i+1)) + stT302 485 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 484
    simpa using h
  have hprev := st302_p484
  have hstep := st302_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p486 : ((1924627636999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT302 (i+1))
      = (∑ i ∈ Finset.range 485, stT302 (i+1)) + stT302 486 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 485
    simpa using h
  have hprev := st302_p485
  have hstep := st302_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p487 : ((1814253427057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT302 (i+1))
      = (∑ i ∈ Finset.range 486, stT302 (i+1)) + stT302 487 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 486
    simpa using h
  have hprev := st302_p486
  have hstep := st302_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p488 : ((341929853819/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT302 (i+1))
      = (∑ i ∈ Finset.range 487, stT302 (i+1)) + stT302 488 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 487
    simpa using h
  have hprev := st302_p487
  have hstep := st302_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p489 : ((1649511211281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT302 (i+1))
      = (∑ i ∈ Finset.range 488, stT302 (i+1)) + stT302 489 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 488
    simpa using h
  have hprev := st302_p488
  have hstep := st302_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p490 : ((3311683703893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT302 (i+1))
      = (∑ i ∈ Finset.range 489, stT302 (i+1)) + stT302 490 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 489
    simpa using h
  have hprev := st302_p489
  have hstep := st302_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p491 : ((6904240888661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT302 (i+1))
      = (∑ i ∈ Finset.range 490, stT302 (i+1)) + stT302 491 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 490
    simpa using h
  have hprev := st302_p490
  have hstep := st302_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p492 : ((7336913942639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT302 (i+1))
      = (∑ i ∈ Finset.range 491, stT302 (i+1)) + stT302 492 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 491
    simpa using h
  have hprev := st302_p491
  have hstep := st302_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p493 : ((7763129117343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT302 (i+1))
      = (∑ i ∈ Finset.range 492, stT302 (i+1)) + stT302 493 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 492
    simpa using h
  have hprev := st302_p492
  have hstep := st302_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p494 : ((8028184777179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT302 (i+1))
      = (∑ i ∈ Finset.range 493, stT302 (i+1)) + stT302 494 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 493
    simpa using h
  have hprev := st302_p493
  have hstep := st302_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p495 : ((8036851830057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT302 (i+1))
      = (∑ i ∈ Finset.range 494, stT302 (i+1)) + stT302 495 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 494
    simpa using h
  have hprev := st302_p494
  have hstep := st302_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p496 : ((7786951292301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT302 (i+1))
      = (∑ i ∈ Finset.range 495, stT302 (i+1)) + stT302 496 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 495
    simpa using h
  have hprev := st302_p495
  have hstep := st302_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p497 : ((7369094706887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT302 (i+1))
      = (∑ i ∈ Finset.range 496, stT302 (i+1)) + stT302 497 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 496
    simpa using h
  have hprev := st302_p496
  have hstep := st302_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p498 : ((1733303276047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT302 (i+1))
      = (∑ i ∈ Finset.range 497, stT302 (i+1)) + stT302 498 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 497
    simpa using h
  have hprev := st302_p497
  have hstep := st302_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p499 : ((3317252855203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT302 (i+1))
      = (∑ i ∈ Finset.range 498, stT302 (i+1)) + stT302 499 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 498
    simpa using h
  have hprev := st302_p498
  have hstep := st302_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_p500 : ((1644588939159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT302 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT302 (i+1))
      = (∑ i ∈ Finset.range 499, stT302 (i+1)) + stT302 500 := by
    have h := Finset.sum_range_succ (fun i => stT302 (i+1)) 499
    simpa using h
  have hprev := st302_p499
  have hstep := st302_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st302_s500 :
    |Real.sin (((302 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))
      - ((-992099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -4241457/10000000) (δ := 3031/200000000) (ψ := -164193/1000000) 302 299
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 302`** (evaluated boundary). -/
theorem station_302_sign : 0 < hardyG ((((302:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 302 500 (by norm_num) (by norm_num)
    ((-164193/1000000 : ℚ) : ℝ)
  have hchain := st302_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT302 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((302 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-164193/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st302_c500
  have hsinb := abs_le.mp st302_s500
  have hbdy_lo : ((268011509052963/3648170000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((302 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ))) / 2
          - ((((302:ℕ)):ℝ))
            * Real.sin (((302 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-164193/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((302:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((302:ℝ) * Real.log (500:ℝ) - ((-164193/1000000 : ℚ) : ℝ))) / 2
        - ((302:ℝ)) * Real.sin ((302:ℝ) * Real.log (500:ℝ) - ((-164193/1000000 : ℚ) : ℝ))
        ≥ ((599292751/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((302:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((599292751/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((599292751/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((599292751/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((302:ℕ)):ℝ))+1) * (((((302:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((444364575999/625000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1644588939159/2500000000000 : ℚ) : ℝ) + ((268011509052963/3648170000000000 : ℚ) : ℝ)
      - ((444364575999/625000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-164193/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((302:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-164193/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((302:ℕ)):ℝ)))).re
      - Real.sin ((-164193/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((302:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((302:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((302:ℕ)):ℝ))
      = (((((302:ℕ)):ℝ)) * (Real.log ((((302:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((302:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_302
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
  have hθwin : |(((-164193/1000000 : ℚ) : ℝ) + ((69:ℤ)) * (2*Real.pi)) - theta ((((302:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((302:ℕ)):ℝ)))
    (φ := ((-164193/1000000 : ℚ) : ℝ) + ((69:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-164193/1000000 : ℚ)) : ℝ) 69).1,
    (cos_sin_shift (((-164193/1000000 : ℚ)) : ℝ) 69).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_302_sign
end AxiomAudit
