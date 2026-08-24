import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 284` (rung-290.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT284 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((284 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-92959/500000 : ℚ) : ℝ))

theorem st284_c1 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((982767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92959/2000000) (δ := 1/1000000000) (ψ := -92959/500000) 284 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t1 : ((982667/1000000 : ℚ) : ℝ) ≤ stT284 1 := by
  have hc : ((982667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((982667/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((982667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c2 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-318333/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565241/1000000) (δ := 14279/1000000000) (ψ := -92959/500000) 284 31
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t2 : ((-562826960761/1250000000000 : ℚ) : ℝ) ≤ stT284 2 := by
  have hc : ((-318383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562826960761/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-318383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c3 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-386351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4918671/10000000) (δ := 14243/1000000000) (ψ := -92959/500000) 284 50
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t3 : ((-2231176007853/10000000000000 : ℚ) : ℝ) ≤ stT284 3 := by
  have hc : ((-386451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2231176007853/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-386451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c4 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-183771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2433951/5000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 63
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t4 : ((-919105183821/5000000000000 : ℚ) : ℝ) ≤ stT284 4 := by
  have hc : ((-183821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-919105183821/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-183821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c5 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((163823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3515579/10000000) (δ := 7113/500000000) (ψ := -92959/500000) 284 73
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t5 : ((146438271721/2000000000000 : ℚ) : ℝ) ≤ stT284 5 := by
  have hc : ((163723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146438271721/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((163723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c6 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((497109/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13449/500000) (δ := 14283/1000000000) (ψ := -92959/500000) 284 81
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t6 : ((1014617210219/2500000000000 : ℚ) : ℝ) ≤ stT284 6 := by
  have hc : ((497059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1014617210219/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((497059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c7 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((199081/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119883/5000000) (δ := 14233/1000000000) (ψ := -92959/500000) 284 88
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t7 : ((188094928571/500000000000 : ℚ) : ℝ) ≤ stT284 7 := by
  have hc : ((199061/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188094928571/500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((199061/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c8 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((123979/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79937/2500000) (δ := 14327/1000000000) (ψ := -92959/500000) 284 94
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t8 : ((876575303289/2500000000000 : ℚ) : ℝ) ≤ stT284 8 := by
  have hc : ((247933/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((876575303289/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((247933/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c9 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-557647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2702931/5000000) (δ := 3553/250000000) (ψ := -92959/500000) 284 99
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t9 : ((-929578519249/5000000000000 : ℚ) : ℝ) ≤ stT284 9 := by
  have hc : ((-557747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-929578519249/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-557747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c10 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((392283/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1672001/10000000) (δ := 3587/250000000) (ψ := -92959/500000) 284 104
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t10 : ((1240349394541/5000000000000 : ℚ) : ℝ) ≤ stT284 10 := by
  have hc : ((392233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1240349394541/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((392233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c11 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-53689/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651039/1000000) (δ := 14377/1000000000) (ψ := -92959/500000) 284 108
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t11 : ((-323794600017/1250000000000 : ℚ) : ℝ) ≤ stT284 11 := by
  have hc : ((-214781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323794600017/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-214781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c12 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-574387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 545663/1000000) (δ := 14397/1000000000) (ψ := -92959/500000) 284 112
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t12 : ((-51825046757/312500000000 : ℚ) : ℝ) ≤ stT284 12 := by
  have hc : ((-574487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51825046757/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-574487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c13 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((48817/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272453/5000000) (δ := 14369/1000000000) (ψ := -92959/500000) 284 116
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t13 : ((67690041/250000000 : ℚ) : ℝ) ≤ stT284 13 := by
  have hc : ((12203/12500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67690041/250000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((12203/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c14 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-397103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 989577/2000000) (δ := 3589/250000000) (ψ := -92959/500000) 284 119
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t14 : ((-1061569901439/10000000000000 : ℚ) : ℝ) ≤ stT284 14 := by
  have hc : ((-397203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1061569901439/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-397203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c15 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-456949/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3404477/5000000) (δ := 14277/1000000000) (ψ := -92959/500000) 284 122
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t15 : ((-1179966391011/5000000000000 : ℚ) : ℝ) ≤ stT284 15 := by
  have hc : ((-456999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1179966391011/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-456999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c16 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-590891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5507399/10000000) (δ := 3551/250000000) (ψ := -92959/500000) 284 125
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t16 : ((-1477478090991/10000000000000 : ℚ) : ℝ) ≤ stT284 16 := by
  have hc : ((-590991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1477478090991/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-590991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c17 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((420737/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57079/400000) (δ := 14283/1000000000) (ψ := -92959/500000) 284 128
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t17 : ((255078934893/1250000000000 : ℚ) : ℝ) ≤ stT284 17 := by
  have hc : ((420687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255078934893/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((420687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c18 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-114331/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5114451/10000000) (δ := 14361/1000000000) (ψ := -92959/500000) 284 131
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t18 : ((-67384930547/625000000000 : ℚ) : ℝ) ≤ stT284 18 := by
  have hc : ((-28589/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67384930547/625000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-28589/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c19 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((736487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371467/2000000) (δ := 891/62500000) (ψ := -92959/500000) 284 133
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t19 : ((1689387390759/10000000000000 : ℚ) : ℝ) ≤ stT284 19 := by
  have hc : ((736387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1689387390759/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((736387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c20 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-460971/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6859651/10000000) (δ := 3583/250000000) (ψ := -92959/500000) 284 135
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t20 : ((-257718576357/1250000000000 : ℚ) : ℝ) ≤ stT284 20 := by
  have hc : ((-461021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257718576357/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-461021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c21 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-156903/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1405799/2500000) (δ := 1799/125000000) (ψ := -92959/500000) 284 138
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t21 : ((-1337675727/9765625000 : ℚ) : ℝ) ≤ stT284 21 := by
  have hc : ((-9808/15625 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1337675727/9765625000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-9808/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c22 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-33167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4009923/10000000) (δ := 14207/1000000000) (ψ := -92959/500000) 284 140
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t22 : ((-8865688767/1250000000000 : ℚ) : ℝ) ≤ stT284 22 := by
  have hc : ((-33267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8865688767/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-33267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c23 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((4953/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241567/625000) (δ := 7191/500000000) (ψ := -92959/500000) 284 142
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t23 : ((1285751919/250000000000 : ℚ) : ℝ) ≤ stT284 23 := by
  have hc : ((4933/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1285751919/250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((4933/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c24 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-109793/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2531841/5000000) (δ := 2847/200000000) (ψ := -92959/500000) 284 144
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t24 : ((-56041278489/625000000000 : ℚ) : ℝ) ≤ stT284 24 := by
  have hc : ((-54909/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56041278489/625000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-54909/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c25 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-197953/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7495989/10000000) (δ := 14353/1000000000) (ψ := -92959/500000) 284 146
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t25 : ((-395946197973/2000000000000 : ℚ) : ℝ) ≤ stT284 25 := by
  have hc : ((-197973/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395946197973/2000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-197973/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c26 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-141203/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 928549/2000000) (δ := 7123/500000000) (ψ := -92959/500000) 284 147
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t26 : ((-138510007993/2500000000000 : ℚ) : ℝ) ≤ stT284 26 := by
  have hc : ((-141253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138510007993/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-141253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c27 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((24999/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701/312500) (δ := 14371/1000000000) (ψ := -92959/500000) 284 149
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t27 : ((192423057/1000000000 : ℚ) : ℝ) ≤ stT284 27 := by
  have hc : ((49993/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192423057/1000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((49993/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c28 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-305837/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1393107/2500000) (δ := 14217/1000000000) (ψ := -92959/500000) 284 151
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t28 : ((-578072288001/5000000000000 : ℚ) : ℝ) ≤ stT284 28 := by
  have hc : ((-305887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-578072288001/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-305887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c29 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((116757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28394/78125) (δ := 14293/1000000000) (ψ := -92959/500000) 284 152
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t29 : ((216626566121/10000000000000 : ℚ) : ℝ) ≤ stT284 29 := by
  have hc : ((116657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216626566121/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((116657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c30 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((43059/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371143/1000000) (δ := 1787/125000000) (ψ := -92959/500000) 284 154
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t30 : ((78523294669/5000000000000 : ℚ) : ℝ) ≤ stT284 30 := by
  have hc : ((43009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78523294669/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((43009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c31 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((26219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 965359/2500000) (δ := 7107/500000000) (ψ := -92959/500000) 284 155
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t31 : ((46911108307/10000000000000 : ℚ) : ℝ) ≤ stT284 31 := by
  have hc : ((26119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46911108307/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((26119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c32 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-210419/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2506457/5000000) (δ := 7187/500000000) (ψ := -92959/500000) 284 157
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t32 : ((-372060152723/5000000000000 : ℚ) : ℝ) ≤ stT284 32 := by
  have hc : ((-210469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-372060152723/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-210469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c33 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((450053/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1126959/10000000) (δ := 14267/1000000000) (ψ := -92959/500000) 284 158
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t33 : ((97919302791/625000000000 : ℚ) : ℝ) ≤ stT284 33 := by
  have hc : ((450003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97919302791/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((450003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c34 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-13744/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3307313/5000000) (δ := 14243/1000000000) (ψ := -92959/500000) 284 159
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t34 : ((-188587577997/1250000000000 : ℚ) : ℝ) ≤ stT284 34 := by
  have hc : ((-219929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188587577997/1250000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-219929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c35 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-23401/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -263761/625000) (δ := 7173/500000000) (ψ := -92959/500000) 284 161
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t35 : ((-39588727089/2000000000000 : ℚ) : ℝ) ≤ stT284 35 := by
  have hc : ((-23421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39588727089/2000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-23421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c36 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((999571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183/25000) (δ := 7119/500000000) (ψ := -92959/500000) 284 162
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t36 : ((832892166843/5000000000000 : ℚ) : ℝ) ≤ stT284 36 := by
  have hc : ((999471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((832892166843/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((999471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c37 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((10843/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3818527/10000000) (δ := 223/15625000) (ψ := -92959/500000) 284 163
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t37 : ((8892336501/1250000000000 : ℚ) : ℝ) ≤ stT284 37 := by
  have hc : ((5409/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8892336501/1250000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((5409/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c38 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-948097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3522493/5000000) (δ := 14379/1000000000) (ψ := -92959/500000) 284 164
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t38 : ((-307635879271/2000000000000 : ℚ) : ℝ) ≤ stT284 38 := by
  have hc : ((-948197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307635879271/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-948197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c39 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-717731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -370521/625000) (δ := 1421/100000000) (ψ := -92959/500000) 284 166
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t39 : ((-574724929671/5000000000000 : ℚ) : ℝ) ≤ stT284 39 := by
  have hc : ((-717831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-574724929671/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-717831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c40 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((106331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3660661/10000000) (δ := 143/10000000) (ψ := -92959/500000) 284 167
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t40 : ((83982935439/5000000000000 : ℚ) : ℝ) ≤ stT284 40 := by
  have hc : ((106231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83982935439/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((106231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c41 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((741997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1836879/10000000) (δ := 2879/200000000) (ψ := -92959/500000) 284 168
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t41 : ((1158647995089/10000000000000 : ℚ) : ℝ) ≤ stT284 41 := by
  have hc : ((741897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1158647995089/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((741897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c42 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((492431/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -217773/5000000) (δ := 893/62500000) (ψ := -92959/500000) 284 169
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t42 : ((759760131573/5000000000000 : ℚ) : ℝ) ≤ stT284 42 := by
  have hc : ((492381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((759760131573/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((492381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c43 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((60921/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281573/5000000) (δ := 7111/500000000) (ψ := -92959/500000) 284 170
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t43 : ((74315264023/500000000000 : ℚ) : ℝ) ≤ stT284 43 := by
  have hc : ((243659/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74315264023/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((243659/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c44 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((445537/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9201/78125) (δ := 14329/1000000000) (ψ := -92959/500000) 284 171
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t44 : ((167899149943/1250000000000 : ℚ) : ℝ) ≤ stT284 44 := by
  have hc : ((445487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167899149943/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((445487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c45 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((841803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 356363/2500000) (δ := 14367/1000000000) (ψ := -92959/500000) 284 172
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t45 : ((1254735920833/10000000000000 : ℚ) : ℝ) ≤ stT284 45 := by
  have hc : ((841703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1254735920833/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((841703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c46 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((863311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330627/2500000) (δ := 14259/1000000000) (ψ := -92959/500000) 284 173
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t46 : ((1272734699409/10000000000000 : ℚ) : ℝ) ≤ stT284 46 := by
  have hc : ((863211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1272734699409/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((863211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c47 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((93813/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 442009/5000000) (δ := 14251/1000000000) (ψ := -92959/500000) 284 174
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t47 : ((136825652147/1000000000000 : ℚ) : ℝ) ≤ stT284 47 := by
  have hc : ((93803/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136825652147/1000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((93803/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c48 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((998771/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123969/10000000) (δ := 7179/500000000) (ψ := -92959/500000) 284 175
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t48 : ((11531654037/80000000000 : ℚ) : ℝ) ≤ stT284 48 := by
  have hc : ((998671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11531654037/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((998671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c49 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((929499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -944363/10000000) (δ := 7169/500000000) (ψ := -92959/500000) 284 176
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t49 : ((1327712458829/10000000000000 : ℚ) : ℝ) ≤ stT284 49 := by
  have hc : ((929399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1327712458829/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((929399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c50 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((603163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1154169/5000000) (δ := 14231/1000000000) (ψ := -92959/500000) 284 177
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t50 : ((852859534419/10000000000000 : ℚ) : ℝ) ≤ stT284 50 := by
  have hc : ((603063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((852859534419/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((603063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c51 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-2357/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -791291/2000000) (δ := 14279/1000000000) (ψ := -92959/500000) 284 178
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t51 : ((-3328467937/2000000000000 : ℚ) : ℝ) ≤ stT284 51 := by
  have hc : ((-2377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3328467937/2000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-2377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c52 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-703443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5877567/10000000) (δ := 14387/1000000000) (ψ := -92959/500000) 284 179
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t52 : ((-975638958793/10000000000000 : ℚ) : ℝ) ≤ stT284 52 := by
  have hc : ((-703543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-975638958793/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-703543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c53 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-996563/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1529331/2000000) (δ := 14387/1000000000) (ψ := -92959/500000) 284 179
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t53 : ((-684511138389/5000000000000 : ℚ) : ℝ) ≤ stT284 53 := by
  have hc : ((-996663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-684511138389/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-996663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c54 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-490999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2605041/5000000) (δ := 14309/1000000000) (ψ := -92959/500000) 284 180
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t54 : ((-167075317493/2500000000000 : ℚ) : ℝ) ≤ stT284 54 := by
  have hc : ((-491099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167075317493/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-491099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c55 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((530173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126499/500000) (δ := 7101/500000000) (ψ := -92959/500000) 284 181
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t55 : ((714749903127/10000000000000 : ℚ) : ℝ) ≤ stT284 55 := by
  have hc : ((530073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((714749903127/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((530073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c56 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((39527/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24053/625000) (δ := 3577/250000000) (ψ := -92959/500000) 284 182
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t56 : ((26407411019/200000000000 : ℚ) : ℝ) ≤ stT284 56 := by
  have hc : ((39523/40000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26407411019/200000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((39523/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c57 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((19959/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220381/625000) (δ := 3597/250000000) (ψ := -92959/500000) 284 183
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t57 : ((13209888769/625000000000 : ℚ) : ℝ) ≤ stT284 57 := by
  have hc : ((39893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13209888769/625000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((39893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c58 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-185191/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6885881/10000000) (δ := 357/25000000) (ψ := -92959/500000) 284 184
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t58 : ((-48638816343/400000000000 : ℚ) : ℝ) ≤ stT284 58 := by
  have hc : ((-185211/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48638816343/400000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-185211/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c59 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-505241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5251143/10000000) (δ := 357/25000000) (ψ := -92959/500000) 284 184
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t59 : ((-65789839449/1000000000000 : ℚ) : ℝ) ≤ stT284 59 := by
  have hc : ((-505341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65789839449/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-505341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c60 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((830669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1476221/10000000) (δ := 1423/100000000) (ψ := -92959/500000) 284 185
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t60 : ((536129797793/5000000000000 : ℚ) : ℝ) ≤ stT284 60 := by
  have hc : ((830569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((536129797793/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((830569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c61 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((135417/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2495939/10000000) (δ := 14337/1000000000) (ψ := -92959/500000) 284 186
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t61 : ((338577313/4882812500 : ℚ) : ℝ) ≤ stT284 61 := by
  have hc : ((8462/15625 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338577313/4882812500 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((8462/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c62 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-887911/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1664737/2500000) (δ := 14359/1000000000) (ψ := -92959/500000) 284 187
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t62 : ((-563887873011/5000000000000 : ℚ) : ℝ) ≤ stT284 62 := by
  have hc : ((-888011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563887873011/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-888011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c63 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-304809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587667/1250000) (δ := 14359/1000000000) (ψ := -92959/500000) 284 187
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t63 : ((-192074680369/5000000000000 : ℚ) : ℝ) ≤ stT284 63 := by
  have hc : ((-304909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192074680369/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-304909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c64 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((24939/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 87333/5000000) (δ := 3563/250000000) (ψ := -92959/500000) 284 188
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t64 : ((49873/400000 : ℚ) : ℝ) ≤ stT284 64 := by
  have hc : ((49873/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49873/400000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((49873/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c65 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-237051/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -905063/2000000) (δ := 7129/500000000) (ψ := -92959/500000) 284 189
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t65 : ((-73537442137/2500000000000 : ℚ) : ℝ) ≤ stT284 65 := by
  have hc : ((-237151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73537442137/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-237151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c66 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-816341/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 631461/1000000) (δ := 7129/500000000) (ψ := -92959/500000) 284 189
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t66 : ((-200993894703/2000000000000 : ℚ) : ℝ) ≤ stT284 66 := by
  have hc : ((-816441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200993894703/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-816441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c67 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((871069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 320889/2500000) (δ := 7183/500000000) (ψ := -92959/500000) 284 190
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t67 : ((532028800743/5000000000000 : ℚ) : ℝ) ≤ stT284 67 := by
  have hc : ((870969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((532028800743/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((870969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c68 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((8521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3905687/10000000) (δ := 1433/100000000) (ψ := -92959/500000) 284 191
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t68 : ((5105980719/5000000000000 : ℚ) : ℝ) ≤ stT284 68 := by
  have hc : ((8421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5105980719/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((8421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c69 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-848417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6459461/10000000) (δ := 1433/100000000) (ψ := -92959/500000) 284 191
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t69 : ((-1021494827103/10000000000000 : ℚ) : ℝ) ≤ stT284 69 := by
  have hc : ((-848517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1021494827103/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-848517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c70 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((926049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38699/400000) (δ := 14223/1000000000) (ψ := -92959/500000) 284 192
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t70 : ((276680042843/2500000000000 : ℚ) : ℝ) ≤ stT284 70 := by
  have hc : ((925949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276680042843/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((925949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c71 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-292627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2334711/5000000) (δ := 14287/1000000000) (ψ := -92959/500000) 284 193
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t71 : ((-173701567257/5000000000000 : ℚ) : ℝ) ≤ stT284 71 := by
  have hc : ((-292727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173701567257/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-292727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c72 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-127147/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5260851/10000000) (δ := 14287/1000000000) (ψ := -92959/500000) 284 193
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t72 : ((-2341777001/39062500000 : ℚ) : ℝ) ≤ stT284 72 := by
  have hc : ((-31793/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2341777001/39062500000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-31793/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c73 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((965991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -653869/10000000) (δ := 7197/500000000) (ψ := -92959/500000) 284 194
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t73 : ((1130489451201/10000000000000 : ℚ) : ℝ) ≤ stT284 73 := by
  have hc : ((965891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1130489451201/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((965891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c74 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-35827/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6701857/10000000) (δ := 14301/1000000000) (ψ := -92959/500000) 284 195
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t74 : ((-41652713387/400000000000 : ℚ) : ℝ) ≤ stT284 74 := by
  have hc : ((-35831/40000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41652713387/400000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-35831/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c75 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((425377/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22098/78125) (δ := 14301/1000000000) (ψ := -92959/500000) 284 195
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t75 : ((4910673519/100000000000 : ℚ) : ℝ) ≤ stT284 75 := by
  have hc : ((425277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4910673519/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((425277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c76 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((44921/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3475327/10000000) (δ := 14209/1000000000) (ψ := -92959/500000) 284 196
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t76 : ((804675217/39062500000 : ℚ) : ℝ) ≤ stT284 76 := by
  have hc : ((2806/15625 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((804675217/39062500000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((2806/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c77 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-170693/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725733/1250000) (δ := 14209/1000000000) (ψ := -92959/500000) 284 196
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t77 : ((-48637814277/625000000000 : ℚ) : ℝ) ≤ stT284 77 := by
  have hc : ((-85359/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48637814277/625000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-85359/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c78 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((956431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148137/2000000) (δ := 3579/250000000) (ψ := -92959/500000) 284 197
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t78 : ((1082831595687/10000000000000 : ℚ) : ℝ) ≤ stT284 78 := by
  have hc : ((956331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1082831595687/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((956331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c79 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-491921/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7403959/10000000) (δ := 719/50000000) (ψ := -92959/500000) 284 198
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t79 : ((-17297208389/156250000000 : ℚ) : ℝ) ≤ stT284 79 := by
  have hc : ((-491971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17297208389/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-491971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c80 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((102399/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1526989/10000000) (δ := 719/50000000) (ψ := -92959/500000) 284 198
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t80 : ((228942971509/2500000000000 : ℚ) : ℝ) ≤ stT284 80 := by
  have hc : ((204773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228942971509/2500000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((204773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c81 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-271331/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5360999/10000000) (δ := 14273/1000000000) (ψ := -92959/500000) 284 199
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t81 : ((-37691835709/625000000000 : ℚ) : ℝ) ≤ stT284 81 := by
  have hc : ((-271381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37691835709/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-271381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c82 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((57113/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837693/2500000) (δ := 14273/1000000000) (ψ := -92959/500000) 284 199
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t82 : ((49252449/1953125000 : ℚ) : ℝ) ≤ stT284 82 := by
  have hc : ((3568/15625 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49252449/1953125000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((3568/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c83 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((70339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3750997/10000000) (δ := 14237/1000000000) (ψ := -92959/500000) 284 200
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t83 : ((38548638219/5000000000000 : ℚ) : ℝ) ≤ stT284 83 := by
  have hc : ((70239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38548638219/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((70239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c84 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-324073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4752069/10000000) (δ := 14283/500000000) (ψ := -92959/500000) 284 200
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t84 : ((-35370191857/1000000000000 : ℚ) : ℝ) ≤ stT284 84 := by
  have hc : ((-324173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35370191857/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-324173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c85 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((104439/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1276717/5000000) (δ := 2869/200000000) (ψ := -92959/500000) 284 201
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t85 : ((28314569297/500000000000 : ℚ) : ℝ) ≤ stT284 85 := by
  have hc : ((104419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28314569297/500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((104419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c86 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-666493/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2875363/5000000) (δ := 2869/200000000) (ψ := -92959/500000) 284 201
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t86 : ((-89850737063/1250000000000 : ℚ) : ℝ) ≤ stT284 86 := by
  have hc : ((-666593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89850737063/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-666593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c87 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((7651/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1748999/10000000) (δ := 14351/1000000000) (ψ := -92959/500000) 284 202
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t87 : ((10252071/125000000 : ℚ) : ℝ) ≤ stT284 87 := by
  have hc : ((153/200 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10252071/125000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((153/200 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c88 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-827901/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3182689/5000000) (δ := 14351/1000000000) (ψ := -92959/500000) 284 202
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t88 : ((-220663094501/2500000000000 : ℚ) : ℝ) ≤ stT284 88 := by
  have hc : ((-828001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220663094501/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-828001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c89 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((863829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65997/500000) (δ := 3561/250000000) (ψ := -92959/500000) 284 203
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t89 : ((915550148813/10000000000000 : ℚ) : ℝ) ≤ stT284 89 := by
  have hc : ((863729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((915550148813/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((863729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c90 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-439663/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6613103/10000000) (δ := 3561/250000000) (ψ := -92959/500000) 284 203
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t90 : ((-463498395309/5000000000000 : ℚ) : ℝ) ≤ stT284 90 := by
  have hc : ((-439713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463498395309/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-439713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c91 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((175537/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1249467/10000000) (δ := 28537/1000000000) (ψ := -92959/500000) 284 204
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t91 : ((45997915707/500000000000 : ℚ) : ℝ) ≤ stT284 91 := by
  have hc : ((175517/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45997915707/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((175517/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c92 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-26843/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6510159/10000000) (δ := 7133/500000000) (ψ := -92959/500000) 284 204
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t92 : ((-223912360637/2500000000000 : ℚ) : ℝ) ≤ stT284 92 := by
  have hc : ((-214769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223912360637/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-214769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c93 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((5127/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -304413/2000000) (δ := 14373/1000000000) (ψ := -92959/500000) 284 205
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t93 : ((42526397461/500000000000 : ℚ) : ℝ) ≤ stT284 93 := by
  have hc : ((41011/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42526397461/500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((41011/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c94 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-756433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3035799/5000000) (δ := 14373/1000000000) (ψ := -92959/500000) 284 205
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t94 : ((-390152389963/5000000000000 : ℚ) : ℝ) ≤ stT284 94 := by
  have hc : ((-756533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390152389963/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-756533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c95 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((660561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84923/400000) (δ := 14323/1000000000) (ψ := -92959/500000) 284 206
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t95 : ((338809227929/5000000000000 : ℚ) : ℝ) ≤ stT284 95 := by
  have hc : ((660461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338809227929/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((660461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c96 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-262971/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1327887/2500000) (δ := 14323/1000000000) (ψ := -92959/500000) 284 206
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t96 : ((-268444756041/5000000000000 : ℚ) : ℝ) ≤ stT284 96 := by
  have hc : ((-263021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268444756041/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-263021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c97 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((347839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3038827/10000000) (δ := 2843/200000000) (ψ := -92959/500000) 284 207
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t97 : ((176537701347/5000000000000 : ℚ) : ℝ) ≤ stT284 97 := by
  have hc : ((347739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176537701347/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((347739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c98 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-63091/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530411/1250000) (δ := 2843/200000000) (ψ := -92959/500000) 284 207
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t98 : ((-63782070573/5000000000000 : ℚ) : ℝ) ≤ stT284 98 := by
  have hc : ((-63141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63782070573/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-63141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c99 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-131411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4256471/10000000) (δ := 2859/200000000) (ψ := -92959/500000) 284 208
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t99 : ((-66086776209/5000000000000 : ℚ) : ℝ) ≤ stT284 99 := by
  have hc : ((-131511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66086776209/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-131511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c100 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((203469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1439621/5000000) (δ := 2859/200000000) (ψ := -92959/500000) 284 208
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t100 : ((203418796581/5000000000000 : ℚ) : ℝ) ≤ stT284 100 := by
  have hc : ((203419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203418796581/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((203419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c101 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-670423/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2881969/5000000) (δ := 14401/1000000000) (ψ := -92959/500000) 284 209
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t101 : ((-333597932437/5000000000000 : ℚ) : ℝ) ≤ stT284 101 := by
  have hc : ((-670523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333597932437/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-670523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c102 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((220291/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246239/2000000) (δ := 14401/1000000000) (ψ := -92959/500000) 284 209
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t102 : ((109047859551/1250000000000 : ℚ) : ℝ) ≤ stT284 102 := by
  have hc : ((110133/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109047859551/1250000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((110133/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c103 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-496307/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7549937/10000000) (δ := 7147/500000000) (ψ := -92959/500000) 284 210
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t103 : ((-48907544281/500000000000 : ℚ) : ℝ) ≤ stT284 103 := by
  have hc : ((-496357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48907544281/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-496357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c104 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((481077/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172497/2500000) (δ := 7147/500000000) (ψ := -92959/500000) 284 210
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t104 : ((23584272783/250000000000 : ℚ) : ℝ) ≤ stT284 104 := by
  have hc : ((481027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23584272783/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((481027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c105 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-764939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6104357/10000000) (δ := 7147/500000000) (ψ := -92959/500000) 284 210
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t105 : ((-746602325139/10000000000000 : ℚ) : ℝ) ≤ stT284 105 := by
  have hc : ((-765039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-746602325139/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-765039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c106 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((408951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2873729/10000000) (δ := 1777/125000000) (ψ := -92959/500000) 284 211
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t106 : ((79422168707/2000000000000 : ℚ) : ℝ) ≤ stT284 106 := by
  have hc : ((408851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79422168707/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((408851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c107 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((53559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3793029/10000000) (δ := 1777/125000000) (ψ := -92959/500000) 284 211
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t107 : ((3230046239/625000000000 : ℚ) : ℝ) ≤ stT284 107 := by
  have hc : ((53459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3230046239/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((53459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c108 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-262747/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -531023/1000000) (δ := 3581/250000000) (ψ := -92959/500000) 284 212
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t108 : ((-252876676047/5000000000000 : ℚ) : ℝ) ≤ stT284 108 := by
  have hc : ((-262797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252876676047/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-262797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c109 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((880717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 308389/2500000) (δ := 3581/250000000) (ψ := -92959/500000) 284 212
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t109 : ((421738929321/5000000000000 : ℚ) : ℝ) ≤ stT284 109 := by
  have hc : ((880617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421738929321/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((880617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c110 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-998513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7717631/10000000) (δ := 3581/250000000) (ψ := -92959/500000) 284 212
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t110 : ((-952140546819/10000000000000 : ℚ) : ℝ) ≤ stT284 110 := by
  have hc : ((-998613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-952140546819/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-998613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c111 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((1013/1250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195613/1250000) (δ := 3593/250000000) (ψ := -92959/500000) 284 213
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t111 : ((7691019171/100000000000 : ℚ) : ℝ) ≤ stT284 111 := by
  have hc : ((8103/10000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7691019171/100000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((8103/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c112 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-343203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2401401/5000000) (δ := 3593/250000000) (ψ := -92959/500000) 284 213
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t112 : ((-20274445271/625000000000 : ℚ) : ℝ) ≤ stT284 112 := by
  have hc : ((-343303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20274445271/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-343303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c113 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-131819/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4593971/10000000) (δ := 2853/200000000) (ψ := -92959/500000) 284 214
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t113 : ((-124051937549/5000000000000 : ℚ) : ℝ) ≤ stT284 113 := by
  have hc : ((-131869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124051937549/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-131869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c114 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((15743/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332311/2000000) (δ := 2853/200000000) (ψ := -92959/500000) 284 214
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t114 : ((2948556897/40000000000 : ℚ) : ℝ) ≤ stT284 114 := by
  have hc : ((15741/20000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2948556897/40000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((15741/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c115 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-499997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7845481/10000000) (δ := 2849/200000000) (ψ := -92959/500000) 284 215
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t115 : ((-93259265547/1000000000000 : ℚ) : ℝ) ≤ stT284 115 := by
  have hc : ((-500047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93259265547/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-500047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c116 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((389/500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1698301/10000000) (δ := 2849/200000000) (ψ := -92959/500000) 284 215
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t116 : ((1805653701/25000000000 : ℚ) : ℝ) ≤ stT284 116 := by
  have hc : ((7779/10000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1805653701/25000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((7779/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c117 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-186583/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4396197/10000000) (δ := 2849/200000000) (ψ := -92959/500000) 284 215
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t117 : ((-172588620183/10000000000000 : ℚ) : ℝ) ≤ stT284 117 := by
  have hc : ((-186683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172588620183/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-186683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c118 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-10229/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5269169/10000000) (δ := 897/62500000) (ψ := -92959/500000) 284 216
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t118 : ((-376736113/8000000000 : ℚ) : ℝ) ≤ stT284 118 := by
  have hc : ((-10231/20000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376736113/8000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-10231/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c119 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((958543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 722379/10000000) (δ := 897/62500000) (ψ := -92959/500000) 284 216
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t119 : ((439301390607/5000000000000 : ℚ) : ℝ) ≤ stT284 119 := by
  have hc : ((958443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439301390607/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((958443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c120 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-177763/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104123/156250) (δ := 897/62500000) (ψ := -92959/500000) 284 216
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t120 : ((-162292944993/2000000000000 : ℚ) : ℝ) ≤ stT284 120 := by
  have hc : ((-177783/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162292944993/2000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-177783/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c121 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((76269/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -393993/1250000) (δ := 1793/125000000) (ψ := -92959/500000) 284 217
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t121 : ((1732816449/62500000000 : ℚ) : ℝ) ≤ stT284 121 := by
  have hc : ((19061/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1732816449/62500000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((19061/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c122 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((1897/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2691711/10000000) (δ := 1793/125000000) (ψ := -92959/500000) 284 217
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t122 : ((8585500431/200000000000 : ℚ) : ℝ) ≤ stT284 122 := by
  have hc : ((9483/20000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8585500431/200000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((9483/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c123 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-60503/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7220309/10000000) (δ := 3559/250000000) (ψ := -92959/500000) 284 218
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t123 : ((-21823750179/250000000000 : ℚ) : ℝ) ≤ stT284 123 := by
  have hc : ((-242037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21823750179/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-242037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c124 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((207941/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1471297/10000000) (δ := 3559/250000000) (ψ := -92959/500000) 284 218
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t124 : ((23339246727/312500000000 : ℚ) : ℝ) ≤ stT284 124 := by
  have hc : ((51979/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23339246727/312500000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((51979/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c125 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-121529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 846313/2000000) (δ := 3559/250000000) (ψ := -92959/500000) 284 218
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t125 : ((-27197095803/2500000000000 : ℚ) : ℝ) ≤ stT284 125 := by
  have hc : ((-121629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27197095803/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-121629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c126 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-343297/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181843/312500) (δ := 7137/500000000) (ψ := -92959/500000) 284 219
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t126 : ((-305877885237/5000000000000 : ℚ) : ℝ) ≤ stT284 126 := by
  have hc : ((-343347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305877885237/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-343347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c127 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((199319/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41271/2000000) (δ := 7137/500000000) (ψ := -92959/500000) 284 219
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t127 : ((44212290861/500000000000 : ℚ) : ℝ) ≤ stT284 127 := by
  have hc : ((199299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44212290861/500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((199299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c128 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-108621/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5362317/10000000) (δ := 7137/500000000) (ψ := -92959/500000) 284 219
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t128 : ((-24006510411/500000000000 : ℚ) : ℝ) ≤ stT284 128 := by
  have hc : ((-108641/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24006510411/500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-108641/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c129 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-174881/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1205071/2500000) (δ := 14381/1000000000) (ψ := -92959/500000) 284 220
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t129 : ((-154018173881/5000000000000 : ℚ) : ℝ) ≤ stT284 129 := by
  have hc : ((-174931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154018173881/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-174931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c130 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((96511/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10349/156250) (δ := 14381/1000000000) (ψ := -92959/500000) 284 220
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t130 : ((42318487029/500000000000 : ℚ) : ℝ) ≤ stT284 130 := by
  have hc : ((96501/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42318487029/500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((96501/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c131 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-191147/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1220599/2000000) (δ := 14381/1000000000) (ψ := -92959/500000) 284 220
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t131 : ((-8351396613/125000000000 : ℚ) : ℝ) ≤ stT284 131 := by
  have hc : ((-47793/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8351396613/125000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-47793/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c132 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-55627/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4205703/10000000) (δ := 2863/200000000) (ψ := -92959/500000) 284 221
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t132 : ((-48460648353/5000000000000 : ℚ) : ℝ) ≤ stT284 132 := by
  have hc : ((-55677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48460648353/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-55677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c133 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((895553/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1152809/10000000) (δ := 2863/200000000) (ψ := -92959/500000) 284 221
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t133 : ((776455355377/10000000000000 : ℚ) : ℝ) ≤ stT284 133 := by
  have hc : ((895453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((776455355377/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((895453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c134 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-850887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6471171/10000000) (δ := 3561/125000000) (ψ := -92959/500000) 284 221
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t134 : ((-735141288703/10000000000000 : ℚ) : ℝ) ≤ stT284 134 := by
  have hc : ((-850987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-735141288703/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-850987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c135 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-2479/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1978989/5000000) (δ := 111/7812500) (ψ := -92959/500000) 284 222
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t135 : ((-2150796837/2000000000000 : ℚ) : ℝ) ≤ stT284 135 := by
  have hc : ((-2499/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2150796837/2000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-2499/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c136 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((174279/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1281893/10000000) (δ := 111/7812500) (ψ := -92959/500000) 284 222
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t136 : ((37356424607/500000000000 : ℚ) : ℝ) ≤ stT284 136 := by
  have hc : ((174259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37356424607/500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((174259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c137 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-213363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202607/312500) (δ := 111/7812500) (ψ := -92959/500000) 284 222
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t137 : ((-22788718113/312500000000 : ℚ) : ℝ) ≤ stT284 137 := by
  have hc : ((-53347/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22788718113/312500000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-53347/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c138 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-53547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2030461/5000000) (δ := 14303/1000000000) (ψ := -92959/500000) 284 223
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t138 : ((-45667384279/10000000000000 : ℚ) : ℝ) ≤ stT284 138 := by
  have hc : ((-53647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45667384279/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-53647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c139 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((182109/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1065491/10000000) (δ := 14303/1000000000) (ψ := -92959/500000) 284 223
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t139 : ((38611426183/500000000000 : ℚ) : ℝ) ≤ stT284 139 := by
  have hc : ((182089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38611426183/500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((182089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c140 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-38893/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3077563/5000000) (δ := 14303/1000000000) (ψ := -92959/500000) 284 223
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t140 : ((-3287483919/50000000000 : ℚ) : ℝ) ≤ stT284 140 := by
  have hc : ((-19449/25000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3287483919/50000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-19449/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c141 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-227001/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1124871/2500000) (δ := 14393/1000000000) (ψ := -92959/500000) 284 224
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t141 : ((-23906695169/1250000000000 : ℚ) : ℝ) ≤ stT284 141 := by
  have hc : ((-227101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23906695169/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-227101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c142 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((30581/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129557/2500000) (δ := 14393/1000000000) (ψ := -92959/500000) 284 224
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t142 : ((205282973763/2500000000000 : ℚ) : ℝ) ≤ stT284 142 := by
  have hc : ((244623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205282973763/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((244623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c143 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-117747/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1375181/2500000) (δ := 14393/1000000000) (ψ := -92959/500000) 284 224
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t143 : ((-98481829381/2000000000000 : ℚ) : ℝ) ≤ stT284 143 := by
  have hc : ((-117767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98481829381/2000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-117767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c144 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-254067/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5259533/10000000) (δ := 7143/500000000) (ψ := -92959/500000) 284 225
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t144 : ((-105882168039/2500000000000 : ℚ) : ℝ) ≤ stT284 144 := by
  have hc : ((-254117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105882168039/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-254117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c145 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((990439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172989/5000000) (δ := 7143/500000000) (ψ := -92959/500000) 284 225
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t145 : ((411215491953/5000000000000 : ℚ) : ℝ) ≤ stT284 145 := by
  have hc : ((990339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411215491953/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((990339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c146 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-12017/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4533781/10000000) (δ := 7143/500000000) (ψ := -92959/500000) 284 225
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t146 : ((-2487369833/125000000000 : ℚ) : ℝ) ≤ stT284 146 := by
  have hc : ((-6011/25000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2487369833/125000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-6011/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c147 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-51211/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6327793/10000000) (δ := 889/62500000) (ψ := -92959/500000) 284 226
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t147 : ((-168973287903/2500000000000 : ℚ) : ℝ) ≤ stT284 147 := by
  have hc : ((-204869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168973287903/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-204869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c148 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((411057/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -757103/5000000) (δ := 889/62500000) (ψ := -92959/500000) 284 226
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t148 : ((168922643979/2500000000000 : ℚ) : ℝ) ≤ stT284 148 := by
  have hc : ((411007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168922643979/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((411007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c149 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((260939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653401/2000000) (δ := 889/62500000) (ψ := -92959/500000) 284 226
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t149 : ((213687394809/10000000000000 : ℚ) : ℝ) ≤ stT284 149 := by
  have hc : ((260839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213687394809/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((260839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c150 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-498949/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7691839/10000000) (δ := 14331/1000000000) (ψ := -92959/500000) 284 227
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t150 : ((-407431186503/5000000000000 : ℚ) : ℝ) ≤ stT284 150 := by
  have hc : ((-498999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-407431186503/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-498999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c151 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((371967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2974173/10000000) (δ := 14331/1000000000) (ψ := -92959/500000) 284 227
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t151 : ((75655225549/2500000000000 : ℚ) : ℝ) ≤ stT284 151 := by
  have hc : ((371867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75655225549/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((371867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c152 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((12101/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428081/2500000) (δ := 14331/1000000000) (ψ := -92959/500000) 284 227
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t152 : ((157023015237/2500000000000 : ℚ) : ℝ) ≤ stT284 152 := by
  have hc : ((193591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157023015237/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((193591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c153 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-414253/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3184039/5000000) (δ := 14331/1000000000) (ψ := -92959/500000) 284 227
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t153 : ((-334944503259/5000000000000 : ℚ) : ℝ) ≤ stT284 153 := by
  have hc : ((-414303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334944503259/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-414303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c154 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-309801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4714449/10000000) (δ := 2873/200000000) (ψ := -92959/500000) 284 228
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t154 : ((-249725353523/10000000000000 : ℚ) : ℝ) ≤ stT284 154 := by
  have hc : ((-309901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249725353523/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-309901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c155 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((249717/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59487/5000000) (δ := 2873/200000000) (ψ := -92959/500000) 284 228
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t155 : ((50139339637/625000000000 : ℚ) : ℝ) ≤ stT284 155 := by
  have hc : ((62423/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50139339637/625000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((62423/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c156 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-206493/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 889393/2000000) (δ := 2873/200000000) (ψ := -92959/500000) 284 228
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t156 : ((-165406826113/10000000000000 : ℚ) : ℝ) ≤ stT284 156 := by
  have hc : ((-206593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165406826113/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-206593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c157 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-899621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84053/125000) (δ := 14257/1000000000) (ψ := -92959/500000) 284 229
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t157 : ((-718055633727/10000000000000 : ℚ) : ℝ) ≤ stT284 157 := by
  have hc : ((-899721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-718055633727/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-899721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c158 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((63211/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -554077/2500000) (δ := 14257/1000000000) (ψ := -92959/500000) 284 229
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t158 : ((50279997957/1000000000000 : ℚ) : ℝ) ≤ stT284 158 := by
  have hc : ((63201/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50279997957/1000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((63201/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c159 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((308729/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 282903/1250000) (δ := 14257/1000000000) (ψ := -92959/500000) 284 229
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t159 : ((244798189629/5000000000000 : ℚ) : ℝ) ≤ stT284 159 := by
  have hc : ((308679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244798189629/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((308679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c160 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-897937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83933/125000) (δ := 14257/1000000000) (ψ := -92959/500000) 284 229
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t160 : ((-70996111109/1000000000000 : ℚ) : ℝ) ≤ stT284 160 := by
  have hc : ((-898037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70996111109/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-898037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c161 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-254249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1142417/2500000) (δ := 14253/1000000000) (ψ := -92959/500000) 284 230
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t161 : ((-200455244739/10000000000000 : ℚ) : ℝ) ≤ stT284 161 := by
  have hc : ((-254349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200455244739/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-254349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c162 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((997597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43337/2500000) (δ := 14253/1000000000) (ψ := -92959/500000) 284 230
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t162 : ((391853728989/5000000000000 : ℚ) : ℝ) ≤ stT284 162 := by
  have hc : ((997497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391853728989/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((997497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c163 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-21473/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4195921/10000000) (δ := 14253/1000000000) (ψ := -92959/500000) 284 230
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t163 : ((-16834628673/2000000000000 : ℚ) : ℝ) ≤ stT284 163 := by
  have hc : ((-21493/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16834628673/2000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-21493/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c164 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-962757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -358477/500000) (δ := 359/25000000) (ψ := -92959/500000) 284 231
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t164 : ((-751865182733/10000000000000 : ℚ) : ℝ) ≤ stT284 164 := by
  have hc : ((-962857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751865182733/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-962857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c165 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((20817/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57069/200000) (δ := 359/25000000) (ψ := -92959/500000) 284 231
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t165 : ((2025262547/62500000000 : ℚ) : ℝ) ≤ stT284 165 := by
  have hc : ((5203/12500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2025262547/62500000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((5203/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c166 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((26231/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1436583/10000000) (δ := 359/25000000) (ψ := -92959/500000) 284 231
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t166 : ((3257082429/50000000000 : ℚ) : ℝ) ≤ stT284 166 := by
  have hc : ((209823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3257082429/50000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((209823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c167 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-651507/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2850457/5000000) (δ := 359/25000000) (ψ := -92959/500000) 284 231
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t167 : ((-7878580237/156250000000 : ℚ) : ℝ) ≤ stT284 167 := by
  have hc : ((-651607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7878580237/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-651607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c168 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-67171/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5768279/10000000) (δ := 28/1953125) (ψ := -92959/500000) 284 232
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t168 : ((-51831283577/1000000000000 : ℚ) : ℝ) ≤ stT284 168 := by
  have hc : ((-67181/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51831283577/1000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-67181/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c169 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((162563/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1554571/10000000) (δ := 28/1953125) (ψ := -92959/500000) 284 232
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t169 : ((12503295189/200000000000 : ℚ) : ℝ) ≤ stT284 169 := by
  have hc : ((162543/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12503295189/200000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((162543/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c170 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((49437/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329277/1250000) (δ := 28/1953125) (ψ := -92959/500000) 284 232
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t170 : ((9477182407/250000000000 : ℚ) : ℝ) ≤ stT284 170 := by
  have hc : ((49427/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9477182407/250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((49427/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c171 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-456091/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6798437/10000000) (δ := 28/1953125) (ψ := -92959/500000) 284 232
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t171 : ((-4360251819/62500000000 : ℚ) : ℝ) ≤ stT284 171 := by
  have hc : ((-456141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4360251819/62500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-456141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c172 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-165347/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4769587/10000000) (δ := 14229/1000000000) (ψ := -92959/500000) 284 233
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t172 : ((-126114054721/5000000000000 : ℚ) : ℝ) ≤ stT284 172 := by
  have hc : ((-165397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126114054721/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-165397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c173 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((483007/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326823/5000000) (δ := 14229/1000000000) (ψ := -92959/500000) 284 233
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t173 : ((73436992549/1000000000000 : ℚ) : ℝ) ≤ stT284 173 := by
  have hc : ((482957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73436992549/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((482957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c174 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((48531/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3438581/10000000) (δ := 14229/1000000000) (ψ := -92959/500000) 284 233
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t174 : ((9193075397/625000000000 : ℚ) : ℝ) ≤ stT284 174 := by
  have hc : ((24253/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9193075397/625000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((24253/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c175 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-198081/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3753689/5000000) (δ := 14229/1000000000) (ψ := -92959/500000) 284 233
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t175 : ((-149750290829/2000000000000 : ℚ) : ℝ) ≤ stT284 175 := by
  have hc : ((-198101/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149750290829/2000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-198101/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c176 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-91079/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -831001/2000000) (δ := 7141/500000000) (ψ := -92959/500000) 284 234
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t176 : ((-68728815441/10000000000000 : ℚ) : ℝ) ≤ stT284 176 := by
  have hc : ((-91179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68728815441/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-91179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c177 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((4993/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132287/10000000) (δ := 7141/500000000) (ψ := -92959/500000) 284 234
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t177 : ((750518531/10000000000 : ℚ) : ℝ) ≤ stT284 177 := by
  have hc : ((1997/2000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((750518531/10000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((1997/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c178 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((2371/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3867711/10000000) (δ := 7141/500000000) (ψ := -92959/500000) 284 234
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t178 : ((1769642691/1000000000000 : ℚ) : ℝ) ≤ stT284 178 := by
  have hc : ((2361/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1769642691/1000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((2361/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c179 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-499997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245167/312500) (δ := 7141/500000000) (ψ := -92959/500000) 284 234
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t179 : ((-93438282373/1250000000000 : ℚ) : ℝ) ≤ stT284 179 := by
  have hc : ((-500047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93438282373/1250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-500047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c180 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((7913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3907209/10000000) (δ := 14389/1000000000) (ψ := -92959/500000) 284 235
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t180 : ((1164691723/2000000000000 : ℚ) : ℝ) ≤ stT284 180 := by
  have hc : ((7813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1164691723/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((7813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c181 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((199989/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26333/10000000) (δ := 14389/1000000000) (ψ := -92959/500000) 284 235
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t181 : ((74317878943/1000000000000 : ℚ) : ℝ) ≤ stT284 181 := by
  have hc : ((199969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74317878943/1000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((199969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c182 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-4463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3938149/10000000) (δ := 14389/1000000000) (ψ := -92959/500000) 284 235
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t182 : ((-2705859/8000000000 : ℚ) : ℝ) ≤ stT284 182 := by
  have hc : ((-4563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2705859/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-4563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c183 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-249987/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3914297/5000000) (δ := 14389/1000000000) (ψ := -92959/500000) 284 235
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t183 : ((-23101796333/312500000000 : ℚ) : ℝ) ≤ stT284 183 := by
  have hc : ((-62503/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23101796333/312500000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-62503/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c184 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-33259/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2005077/5000000) (δ := 14307/1000000000) (ψ := -92959/500000) 284 236
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t184 : ((-2459258839/1000000000000 : ℚ) : ℝ) ≤ stT284 184 := by
  have hc : ((-33359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2459258839/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-33359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c185 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((62369/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161883/10000000) (δ := 14307/1000000000) (ψ := -92959/500000) 284 236
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t185 : ((91699933757/1250000000000 : ℚ) : ℝ) ≤ stT284 185 := by
  have hc : ((249451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91699933757/1250000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((249451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c186 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((26093/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 733117/2000000) (δ := 14307/1000000000) (ψ := -92959/500000) 284 236
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t186 : ((955698499/125000000000 : ℚ) : ℝ) ≤ stT284 186 := by
  have hc : ((6517/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((955698499/125000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((6517/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c187 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-988387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1494521/2000000) (δ := 14307/1000000000) (ψ := -92959/500000) 284 236
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t187 : ((-722853853951/10000000000000 : ℚ) : ℝ) ≤ stT284 187 := by
  have hc : ((-988487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-722853853951/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-988487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c188 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-103589/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -889743/2000000) (δ := 14203/1000000000) (ψ := -92959/500000) 284 237
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t188 : ((-3023460547/200000000000 : ℚ) : ℝ) ≤ stT284 188 := by
  have hc : ((-103639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3023460547/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-103639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c189 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((96301/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341047/5000000) (δ := 14203/1000000000) (ψ := -92959/500000) 284 237
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t189 : ((2188790721/31250000000 : ℚ) : ℝ) ≤ stT284 189 := by
  have hc : ((96291/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2188790721/31250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((96291/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c190 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((67633/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23942/78125) (δ := 14203/1000000000) (ψ := -92959/500000) 284 237
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t190 : ((12262902197/500000000000 : ℚ) : ℝ) ≤ stT284 190 := by
  have hc : ((67613/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12262902197/500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((67613/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c191 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-455533/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135833/200000) (δ := 14203/1000000000) (ψ := -92959/500000) 284 237
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t191 : ((-13185938769/200000000000 : ℚ) : ℝ) ≤ stT284 191 := by
  have hc : ((-455583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13185938769/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-455583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c192 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-24527/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1302191/2500000) (δ := 1431/100000000) (ψ := -92959/500000) 284 238
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t192 : ((-553264063/15625000000 : ℚ) : ℝ) ≤ stT284 192 := by
  have hc : ((-6133/12500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553264063/15625000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-6133/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c193 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((51293/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190057/1250000) (δ := 1431/100000000) (ψ := -92959/500000) 284 238
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t193 : ((29533577561/500000000000 : ℚ) : ℝ) ≤ stT284 193 := by
  have hc : ((205147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29533577561/500000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((205147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c194 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((326397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 268603/1250000) (δ := 1431/100000000) (ψ := -92959/500000) 284 238
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t194 : ((117151719713/2500000000000 : ℚ) : ℝ) ≤ stT284 194 := by
  have hc : ((326347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117151719713/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((326347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c195 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-680827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2899609/5000000) (δ := 1431/100000000) (ψ := -92959/500000) 284 238
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t195 : ((-97524407721/2000000000000 : ℚ) : ℝ) ≤ stT284 195 := by
  have hc : ((-680927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97524407721/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-680927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c196 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-403783/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251081/400000) (δ := 7193/500000000) (ψ := -92959/500000) 284 239
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t196 : ((-144226129119/2500000000000 : ℚ) : ℝ) ≤ stT284 196 := by
  have hc : ((-403833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144226129119/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-403833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c197 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((242031/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -665941/2500000) (δ := 7193/500000000) (ψ := -92959/500000) 284 239
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t197 : ((17240420307/500000000000 : ℚ) : ℝ) ≤ stT284 197 := by
  have hc : ((241981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17240420307/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((241981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c198 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((931431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 931179/10000000) (δ := 7193/500000000) (ψ := -92959/500000) 284 239
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t198 : ((661868070439/10000000000000 : ℚ) : ℝ) ≤ stT284 198 := by
  have hc : ((931331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((661868070439/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((931331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c199 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-57581/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4508017/10000000) (δ := 7193/500000000) (ψ := -92959/500000) 284 239
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t199 : ((-10208964123/625000000000 : ℚ) : ℝ) ≤ stT284 199 := by
  have hc : ((-28803/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10208964123/625000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-28803/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c200 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-124547/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7641071/10000000) (δ := 7139/500000000) (ψ := -92959/500000) 284 240
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t200 : ((-176153788733/2500000000000 : ℚ) : ℝ) ≤ stT284 200 := by
  have hc : ((-249119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176153788733/2500000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-249119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c201 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-69099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32799/80000) (δ := 7139/500000000) (ψ := -92959/500000) 284 240
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t201 : ((-24404618927/5000000000000 : ℚ) : ℝ) ≤ stT284 201 := by
  have hc : ((-69199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24404618927/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-69199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c202 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((486771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288179/5000000) (δ := 7139/500000000) (ψ := -92959/500000) 284 240
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t202 : ((342455435437/5000000000000 : ℚ) : ℝ) ≤ stT284 202 := by
  have hc : ((486721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342455435437/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((486721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c203 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((38837/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 585967/2000000) (δ := 7139/500000000) (ψ := -92959/500000) 284 240
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t203 : ((13625597937/500000000000 : ℚ) : ℝ) ≤ stT284 203 := by
  have hc : ((38827/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13625597937/500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((38827/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c204 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-839691/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 256751/400000) (δ := 7139/500000000) (ψ := -92959/500000) 284 240
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t204 : ((-587972110531/10000000000000 : ℚ) : ℝ) ≤ stT284 204 := by
  have hc : ((-839791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587972110531/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-839791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c205 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-686103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727161/1250000) (δ := 1779/125000000) (ψ := -92959/500000) 284 241
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t205 : ((-479265447493/10000000000000 : ℚ) : ℝ) ≤ stT284 205 := by
  have hc : ((-686203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-479265447493/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-686203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c206 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((146453/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1181143/5000000) (δ := 1779/125000000) (ψ := -92959/500000) 284 241
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t206 : ((25505304931/625000000000 : ℚ) : ℝ) ≤ stT284 206 := by
  have hc : ((36607/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25505304931/625000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((36607/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c207 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((454403/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26899/250000) (δ := 1779/125000000) (ψ := -92959/500000) 284 241
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t207 : ((39474642993/625000000000 : ℚ) : ℝ) ≤ stT284 207 := by
  have hc : ((454353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39474642993/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((454353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c208 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-56573/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4497663/10000000) (δ := 1779/125000000) (ψ := -92959/500000) 284 241
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t208 : ((-153295683/9765625000 : ℚ) : ℝ) ≤ stT284 208 := by
  have hc : ((-28299/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153295683/9765625000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-28299/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c209 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-15622/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3902499/5000000) (δ := 14339/1000000000) (ψ := -92959/500000) 284 242
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t209 : ((-34582568111/500000000000 : ℚ) : ℝ) ≤ stT284 209 := by
  have hc : ((-249977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34582568111/500000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-249977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c210 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-194341/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -883191/2000000) (δ := 14339/1000000000) (ψ := -92959/500000) 284 242
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t210 : ((-67088561553/5000000000000 : ℚ) : ℝ) ≤ stT284 210 := by
  have hc : ((-194441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67088561553/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-194441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c211 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((457111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1043029/10000000) (δ := 14339/1000000000) (ψ := -92959/500000) 284 242
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t211 : ((78663397527/1250000000000 : ℚ) : ℝ) ≤ stT284 211 := by
  have hc : ((457061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78663397527/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((457061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c212 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((30069/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1156961/5000000) (δ := 14339/1000000000) (ψ := -92959/500000) 284 242
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t212 : ((645250479/15625000000 : ℚ) : ℝ) ≤ stT284 212 := by
  have hc : ((1879/3125 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((645250479/15625000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((1879/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c213 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-637499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5655111/10000000) (δ := 14339/1000000000) (ψ := -92959/500000) 284 242
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t213 : ((-436875821211/10000000000000 : ℚ) : ℝ) ≤ stT284 213 := by
  have hc : ((-637599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436875821211/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-637599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c214 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-112519/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1681821/2500000) (δ := 14357/1000000000) (ψ := -92959/500000) 284 243
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t214 : ((-76924957959/1250000000000 : ℚ) : ℝ) ≤ stT284 214 := by
  have hc : ((-225063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76924957959/1250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-225063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c215 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((202481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213579/625000) (δ := 14357/1000000000) (ψ := -92959/500000) 284 243
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t215 : ((69011313857/5000000000000 : ℚ) : ℝ) ≤ stT284 215 := by
  have hc : ((202381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69011313857/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((202381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c216 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((499399/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6129/500000) (δ := 14357/1000000000) (ψ := -92959/500000) 284 243
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t216 : ((339763551137/5000000000000 : ℚ) : ℝ) ≤ stT284 216 := by
  have hc : ((499349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339763551137/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((499349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c217 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((303211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3156839/10000000) (δ := 14357/1000000000) (ψ := -92959/500000) 284 243
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t217 : ((51441270921/2500000000000 : ℚ) : ℝ) ≤ stT284 217 := by
  have hc : ((303111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51441270921/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((303111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c218 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-840219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3210603/5000000) (δ := 14357/1000000000) (ψ := -92959/500000) 284 243
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t218 : ((-284568147117/5000000000000 : ℚ) : ℝ) ≤ stT284 218 := by
  have hc : ((-840319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284568147117/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-840319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c219 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-747389/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60373/100000) (δ := 57/4000000) (ψ := -92959/500000) 284 244
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t219 : ((-252553360941/5000000000000 : ℚ) : ℝ) ≤ stT284 219 := by
  have hc : ((-747489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252553360941/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-747489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c220 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((434717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1401341/5000000) (δ := 57/4000000) (ψ := -92959/500000) 284 244
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t220 : ((293018346783/10000000000000 : ℚ) : ℝ) ≤ stT284 220 := by
  have hc : ((434617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293018346783/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((434617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c221 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((986101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41731/1000000) (δ := 57/4000000) (ψ := -92959/500000) 284 244
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t221 : ((20726727021/312500000000 : ℚ) : ℝ) ≤ stT284 221 := by
  have hc : ((986001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20726727021/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((986001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c222 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((60713/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 905669/2500000) (δ := 57/4000000) (ψ := -92959/500000) 284 244
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t222 : ((10178584107/1250000000000 : ℚ) : ℝ) ≤ stT284 222 := by
  have hc : ((60663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10178584107/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((60663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c223 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-914667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68137/100000) (δ := 57/4000000) (ψ := -92959/500000) 284 244
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t223 : ((-12251474431/200000000000 : ℚ) : ℝ) ≤ stT284 223 := by
  have hc : ((-914767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12251474431/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-914767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c224 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-656529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571751/1000000) (δ := 713/50000000) (ψ := -92959/500000) 284 245
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t224 : ((-219364646433/5000000000000 : ℚ) : ℝ) ≤ stT284 224 := by
  have hc : ((-656629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219364646433/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-656629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c225 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((5217/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1277443/5000000) (δ := 713/50000000) (ψ := -92959/500000) 284 245
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t225 : ((54333279/1562500000 : ℚ) : ℝ) ≤ stT284 225 := by
  have hc : ((326/625 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54333279/1562500000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((326/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c226 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((971939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148411/2500000) (δ := 28543/1000000000) (ψ := -92959/500000) 284 245
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t226 : ((64645758441/1000000000000 : ℚ) : ℝ) ≤ stT284 226 := by
  have hc : ((971839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64645758441/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((971839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c227 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((79381/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 372833/1000000) (δ := 713/50000000) (ψ := -92959/500000) 284 245
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t227 : ((52620623163/10000000000000 : ℚ) : ℝ) ≤ stT284 227 := by
  have hc : ((79281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52620623163/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((79281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c228 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-184063/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3424603/5000000) (δ := 713/50000000) (ψ := -92959/500000) 284 245
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t228 : ((-121912096161/2000000000000 : ℚ) : ℝ) ≤ stT284 228 := by
  have hc : ((-184083/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121912096161/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-184083/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c229 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-666727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5751513/10000000) (δ := 449/31250000) (ψ := -92959/500000) 284 246
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t229 : ((-440651951313/10000000000000 : ℚ) : ℝ) ≤ stT284 229 := by
  have hc : ((-666827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-440651951313/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-666827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c230 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((486137/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265783/1000000) (δ := 449/31250000) (ψ := -92959/500000) 284 246
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t230 : ((16024153853/500000000000 : ℚ) : ℝ) ≤ stT284 230 := by
  have hc : ((486037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16024153853/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((486037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c231 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((492879/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 211217/5000000) (δ := 449/31250000) (ψ := -92959/500000) 284 246
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t231 : ((324257333379/5000000000000 : ℚ) : ℝ) ≤ stT284 231 := by
  have hc : ((492829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324257333379/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((492829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c232 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((43541/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69787/200000) (δ := 449/31250000) (ψ := -92959/500000) 284 246
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t232 : ((1785602907/156250000000 : ℚ) : ℝ) ≤ stT284 232 := by
  have hc : ((10879/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1785602907/156250000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((10879/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c233 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-432827/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6543131/10000000) (δ := 449/31250000) (ψ := -92959/500000) 284 246
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t233 : ((-141793622997/2500000000000 : ℚ) : ℝ) ≤ stT284 233 := by
  have hc : ((-432877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141793622997/2500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-432877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c234 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-385003/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1531029/2500000) (δ := 1791/125000000) (ψ := -92959/500000) 284 247
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t234 : ((-251717232213/5000000000000 : ℚ) : ℝ) ≤ stT284 234 := by
  have hc : ((-385053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251717232213/5000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-385053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c235 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((326161/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387049/1250000) (δ := 1791/125000000) (ψ := -92959/500000) 284 247
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t235 : ((26587340001/1250000000000 : ℚ) : ℝ) ≤ stT284 235 := by
  have hc : ((326061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26587340001/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((326061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c236 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((249867/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81519/10000000) (δ := 1791/125000000) (ψ := -92959/500000) 284 247
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t236 : ((1270571491/19531250000 : ℚ) : ℝ) ≤ stT284 236 := by
  have hc : ((124921/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1270571491/19531250000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((124921/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c237 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((391781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1460287/5000000) (δ := 1791/125000000) (ψ := -92959/500000) 284 247
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t237 : ((254423835489/10000000000000 : ℚ) : ℝ) ≤ stT284 237 := by
  have hc : ((391681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254423835489/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((391681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c238 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-712613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5910029/10000000) (δ := 1791/125000000) (ψ := -92959/500000) 284 247
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t238 : ((-115495854363/2500000000000 : ℚ) : ℝ) ≤ stT284 238 := by
  have hc : ((-712713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115495854363/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-712713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c239 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-2862/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272839/400000) (δ := 14221/1000000000) (ψ := -92959/500000) 284 248
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t239 : ((-29623652059/500000000000 : ℚ) : ℝ) ≤ stT284 239 := by
  have hc : ((-45797/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29623652059/500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-45797/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c240 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((3527/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3856441/10000000) (δ := 14221/1000000000) (ψ := -92959/500000) 284 248
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t240 : ((4537198413/2500000000000 : ℚ) : ℝ) ≤ stT284 240 := by
  have hc : ((7029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4537198413/2500000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((7029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c241 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((187059/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -904261/10000000) (δ := 14221/1000000000) (ψ := -92959/500000) 284 248
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t241 : ((30120573521/500000000000 : ℚ) : ℝ) ≤ stT284 241 := by
  have hc : ((187039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30120573521/500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((187039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c242 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((68639/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2035707/10000000) (δ := 14221/1000000000) (ψ := -92959/500000) 284 248
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t242 : ((5514546037/125000000000 : ℚ) : ℝ) ≤ stT284 242 := by
  have hc : ((68629/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5514546037/125000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((68629/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c243 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-10071/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2481767/5000000) (δ := 14221/1000000000) (ψ := -92959/500000) 284 248
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t243 : ((-12924320647/500000000000 : ℚ) : ℝ) ≤ stT284 243 := by
  have hc : ((-20147/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12924320647/500000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-20147/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c244 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-249987/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7828601/10000000) (δ := 14289/1000000000) (ψ := -92959/500000) 284 249
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t244 : ((-8002696611/125000000000 : ℚ) : ℝ) ≤ stT284 244 := by
  have hc : ((-62503/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8002696611/125000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-62503/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c245 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-97147/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4924737/10000000) (δ := 14257/500000000) (ψ := -92959/500000) 284 249
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t245 : ((-15520238961/625000000000 : ℚ) : ℝ) ≤ stT284 245 := by
  have hc : ((-24293/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15520238961/625000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-24293/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c246 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((687277/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1016329/5000000) (δ := 14289/1000000000) (ψ := -92959/500000) 284 249
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t246 : ((54765945369/1250000000000 : ℚ) : ℝ) ≤ stT284 246 := by
  have hc : ((687177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54765945369/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((687177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c247 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((188613/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84767/1000000) (δ := 14289/1000000000) (ψ := -92959/500000) 284 249
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t247 : ((29999677103/500000000000 : ℚ) : ℝ) ≤ stT284 247 := by
  have hc : ((188593/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29999677103/500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((188593/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c248 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((16831/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1858177/5000000) (δ := 14289/1000000000) (ψ := -92959/500000) 284 249
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t248 : ((2134997/400000000 : ℚ) : ℝ) ≤ stT284 248 := by
  have hc : ((16811/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2134997/400000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((16811/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c249 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-174333/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1314693/2000000) (δ := 14289/1000000000) (ψ := -92959/500000) 284 249
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t249 : ((-4419674197/80000000000 : ℚ) : ℝ) ≤ stT284 249 := by
  have hc : ((-174353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4419674197/80000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-174353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c250 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-810323/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6288747/10000000) (δ := 3599/250000000) (ψ := -92959/500000) 284 250
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t250 : ((-64069611111/1250000000000 : ℚ) : ℝ) ≤ stT284 250 := by
  have hc : ((-810423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64069611111/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-810423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c251 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((93951/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3454427/10000000) (δ := 3599/250000000) (ψ := -92959/500000) 284 250
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t251 : ((29634873897/2500000000000 : ℚ) : ℝ) ≤ stT284 251 := by
  have hc : ((93901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29634873897/2500000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((93901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c252 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((242069/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157849/2500000) (δ := 3599/250000000) (ψ := -92959/500000) 284 250
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t252 : ((1905914967/31250000000 : ℚ) : ℝ) ≤ stT284 252 := by
  have hc : ((60511/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1905914967/31250000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((60511/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c253 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((643147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272561/1250000) (δ := 3599/250000000) (ψ := -92959/500000) 284 250
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t253 : ((202139895309/5000000000000 : ℚ) : ℝ) ≤ stT284 253 := by
  have hc : ((643047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202139895309/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((643047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c254 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-102333/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311331/625000) (δ := 3599/250000000) (ψ := -92959/500000) 284 250
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t254 : ((-125439729/4882812500 : ℚ) : ℝ) ≤ stT284 254 := by
  have hc : ((-51179/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125439729/4882812500 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-51179/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c255 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-19989/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7771099/10000000) (δ := 3599/250000000) (ψ := -92959/500000) 284 250
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t255 : ((-500754559/8000000000 : ℚ) : ℝ) ≤ stT284 255 := by
  have hc : ((-19991/20000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500754559/8000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-19991/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c256 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-59093/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1289499/2500000) (δ := 14299/1000000000) (ψ := -92959/500000) 284 251
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t256 : ((-73881993211/2500000000000 : ℚ) : ℝ) ≤ stT284 256 := by
  have hc : ((-118211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73881993211/2500000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-118211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c257 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((115359/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238999/1000000) (δ := 14299/1000000000) (ψ := -92959/500000) 284 251
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t257 : ((35973196049/1000000000000 : ℚ) : ℝ) ≤ stT284 257 := by
  have hc : ((115339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35973196049/1000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((115339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c258 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((989227/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73459/2000000) (δ := 14299/1000000000) (ψ := -92959/500000) 284 251
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t258 : ((153950693661/2500000000000 : ℚ) : ℝ) ≤ stT284 258 := by
  have hc : ((989127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153950693661/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((989127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c259 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((319521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311393/1000000) (δ := 14299/1000000000) (ψ := -92959/500000) 284 251
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t259 : ((198478307349/10000000000000 : ℚ) : ℝ) ≤ stT284 259 := by
  have hc : ((319421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198478307349/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((319421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c260 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-695559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2924993/5000000) (δ := 14299/1000000000) (ψ := -92959/500000) 284 251
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t260 : ((-215714812333/5000000000000 : ℚ) : ℝ) ≤ stT284 260 := by
  have hc : ((-695659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215714812333/5000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-695659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c261 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-958637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7132429/10000000) (δ := 14211/1000000000) (ψ := -92959/500000) 284 252
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t261 : ((-118688764389/2000000000000 : ℚ) : ℝ) ≤ stT284 261 := by
  have hc : ((-958737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118688764389/2000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-958737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c262 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-48719/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2208659/5000000) (δ := 42611/1000000000) (ψ := -92959/500000) 284 252
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t262 : ((-3764273679/312500000000 : ℚ) : ℝ) ≤ stT284 262 := by
  have hc : ((-6093/31250 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3764273679/312500000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-6093/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c263 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((774401/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1712573/10000000) (δ := 14211/1000000000) (ψ := -92959/500000) 284 252
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t263 : ((238727064213/5000000000000 : ℚ) : ℝ) ≤ stT284 263 := by
  have hc : ((774301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238727064213/5000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((774301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c264 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((923849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245487/2500000) (δ := 42611/1000000000) (ψ := -92959/500000) 284 252
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t264 : ((568527788293/10000000000000 : ℚ) : ℝ) ≤ stT284 264 := by
  have hc : ((923749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568527788293/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((923749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c265 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((104109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 733249/2000000) (δ := 14211/1000000000) (ψ := -92959/500000) 284 252
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t265 : ((12778441731/2000000000000 : ℚ) : ℝ) ≤ stT284 265 := by
  have hc : ((104009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12778441731/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((104009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c266 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-82227/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317023/500000) (δ := 14211/1000000000) (ψ := -92959/500000) 284 252
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t266 : ((-2521139709/50000000000 : ℚ) : ℝ) ≤ stT284 266 := by
  have hc : ((-82237/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2521139709/50000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-82237/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c267 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-111993/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670337/1000000) (δ := 7159/500000000) (ψ := -92959/500000) 284 253
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t267 : ((-137092715901/2500000000000 : ℚ) : ℝ) ≤ stT284 267 := by
  have hc : ((-224011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137092715901/2500000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-224011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c268 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-9771/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4049177/10000000) (δ := 7159/500000000) (ψ := -92959/500000) 284 253
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t268 : ((-186900399/62500000000 : ℚ) : ℝ) ≤ stT284 268 := by
  have hc : ((-9791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186900399/62500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-9791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c269 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((423111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1404853/10000000) (δ := 7159/500000000) (ψ := -92959/500000) 284 253
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t269 : ((25794452231/500000000000 : ℚ) : ℝ) ≤ stT284 269 := by
  have hc : ((423061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25794452231/500000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((423061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c270 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((220363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1229673/10000000) (δ := 7159/500000000) (ψ := -92959/500000) 284 253
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t270 : ((3352332501/62500000000 : ℚ) : ℝ) ≤ stT284 270 := by
  have hc : ((110169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3352332501/62500000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((110169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c271 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((29003/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 481809/1250000) (δ := 7159/500000000) (ψ := -92959/500000) 284 253
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t271 : ((548665649/312500000000 : ℚ) : ℝ) ≤ stT284 271 := by
  have hc : ((28903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548665649/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((28903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c272 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-170109/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 808693/1250000) (δ := 7159/500000000) (ψ := -92959/500000) 284 253
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t272 : ((-5157800893/100000000000 : ℚ) : ℝ) ≤ stT284 272 := by
  have hc : ((-170129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5157800893/100000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-170129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c273 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-220769/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6632933/10000000) (δ := 7189/500000000) (ψ := -92959/500000) 284 254
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t273 : ((-16703838879/312500000000 : ℚ) : ℝ) ≤ stT284 273 := by
  have hc : ((-110397/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16703838879/312500000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-110397/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c274 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-8789/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4036889/10000000) (δ := 7189/500000000) (ψ := -92959/500000) 284 254
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t274 : ((-5321719507/2000000000000 : ℚ) : ℝ) ≤ stT284 274 := by
  have hc : ((-8809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5321719507/2000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-8809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c275 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((52273/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145043/1000000) (δ := 7189/500000000) (ψ := -92959/500000) 284 254
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t275 : ((63036000237/1250000000000 : ℚ) : ℝ) ≤ stT284 275 := by
  have hc : ((209067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63036000237/1250000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((209067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c276 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((450073/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140841/1250000) (δ := 7189/500000000) (ψ := -92959/500000) 284 254
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t276 : ((270881894367/5000000000000 : ℚ) : ℝ) ≤ stT284 276 := by
  have hc : ((450023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270881894367/5000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((450023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c277 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((23207/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 738917/2000000) (δ := 7189/500000000) (ψ := -92959/500000) 284 254
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t277 : ((6964348031/1250000000000 : ℚ) : ℝ) ≤ stT284 277 := by
  have hc : ((11591/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6964348031/1250000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((11591/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c278 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-160379/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6253141/10000000) (δ := 7189/500000000) (ψ := -92959/500000) 284 254
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t278 : ((-96201064639/2000000000000 : ℚ) : ℝ) ≤ stT284 278 := by
  have hc : ((-160399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96201064639/2000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-160399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c279 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-928889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -863187/1250000) (δ := 14271/1000000000) (ψ := -92959/500000) 284 255
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t279 : ((-111234355893/2000000000000 : ℚ) : ℝ) ≤ stT284 279 := by
  have hc : ((-928989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111234355893/2000000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-928989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c280 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-87191/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4365187/10000000) (δ := 14271/1000000000) (ψ := -92959/500000) 284 255
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t280 : ((-10427306043/1000000000000 : ℚ) : ℝ) ≤ stT284 280 := by
  have hc : ((-87241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10427306043/1000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-87241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c281 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((742759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1834037/10000000) (δ := 14271/1000000000) (ψ := -92959/500000) 284 255
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t281 : ((443032483791/10000000000000 : ℚ) : ℝ) ≤ stT284 281 := by
  have hc : ((742659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((443032483791/10000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((742659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c282 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((962353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 688167/10000000) (δ := 14271/1000000000) (ψ := -92959/500000) 284 255
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t282 : ((573013001223/10000000000000 : ℚ) : ℝ) ≤ stT284 282 := by
  have hc : ((962253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((573013001223/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((962253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c283 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((286169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128057/400000) (δ := 14271/1000000000) (ψ := -92959/500000) 284 255
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t283 : ((85025142111/5000000000000 : ℚ) : ℝ) ≤ stT284 283 := by
  have hc : ((286069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85025142111/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((286069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c284 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-163253/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5705879/10000000) (δ := 14271/1000000000) (ψ := -92959/500000) 284 255
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t284 : ((-48443847849/1250000000000 : ℚ) : ℝ) ≤ stT284 284 := by
  have hc : ((-81639/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48443847849/1250000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-81639/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c285 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-247589/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1501301/2000000) (δ := 14239/1000000000) (ψ := -92959/500000) 284 256
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t285 : ((-73336952643/1250000000000 : ℚ) : ℝ) ≤ stT284 285 := by
  have hc : ((-123807/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73336952643/1250000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-123807/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c286 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-423259/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1254897/2500000) (δ := 14239/1000000000) (ψ := -92959/500000) 284 256
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t286 : ((-250337680367/10000000000000 : ℚ) : ℝ) ≤ stT284 286 := by
  have hc : ((-423359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250337680367/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-423359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c287 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((526293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -635351/2500000) (δ := 14239/1000000000) (ψ := -92959/500000) 284 256
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t287 : ((310601730233/10000000000000 : ℚ) : ℝ) ≤ stT284 287 := by
  have hc : ((526193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310601730233/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((526193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c288 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((999587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35941/5000000) (δ := 14239/1000000000) (ψ := -92959/500000) 284 256
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t288 : ((117790542437/2000000000000 : ℚ) : ℝ) ≤ stT284 288 := by
  have hc : ((999487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117790542437/2000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((999487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c289 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((14427/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3733/15625) (δ := 14239/1000000000) (ψ := -92959/500000) 284 256
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t289 : ((3393998303/100000000000 : ℚ) : ℝ) ≤ stT284 289 := by
  have hc : ((28849/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3393998303/100000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((28849/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c290 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-71553/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4841673/10000000) (δ := 14239/1000000000) (ψ := -92959/500000) 284 256
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t290 : ((-42029168633/2000000000000 : ℚ) : ℝ) ≤ stT284 290 := by
  have hc : ((-71573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42029168633/2000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-71573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c291 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-243569/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3642853/5000000) (δ := 14239/1000000000) (ψ := -92959/500000) 284 256
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t291 : ((-71398741167/1250000000000 : ℚ) : ℝ) ≤ stT284 291 := by
  have hc : ((-121797/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71398741167/1250000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-121797/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c292 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-45859/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5986531/10000000) (δ := 14347/1000000000) (ψ := -92959/500000) 284 257
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t292 : ((-53681238983/1250000000000 : ℚ) : ℝ) ≤ stT284 292 := by
  have hc : ((-183461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53681238983/1250000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-183461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c293 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((146593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3559183/10000000) (δ := 14347/1000000000) (ψ := -92959/500000) 284 257
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t293 : ((42791044779/5000000000000 : ℚ) : ℝ) ≤ stT284 293 := by
  have hc : ((146493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42791044779/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((146493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c294 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((224449/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570071/5000000) (δ := 14347/1000000000) (ψ := -92959/500000) 284 257
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t294 : ((16360818183/312500000000 : ℚ) : ℝ) ≤ stT284 294 := by
  have hc : ((28053/31250 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16360818183/312500000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((28053/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c295 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((109197/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 635367/5000000) (δ := 14347/1000000000) (ψ := -92959/500000) 284 257
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t295 : ((63569617959/1250000000000 : ℚ) : ℝ) ≤ stT284 295 := by
  have hc : ((218369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63569617959/1250000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((218369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c296 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((20249/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 734689/2000000) (δ := 14347/1000000000) (ψ := -92959/500000) 284 257
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t296 : ((5878931751/1000000000000 : ℚ) : ℝ) ≤ stT284 296 := by
  have hc : ((20229/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5878931751/1000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((20229/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c297 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-188877/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3034031/5000000) (δ := 14347/1000000000) (ψ := -92959/500000) 284 257
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t297 : ((-54806042809/1250000000000 : ℚ) : ℝ) ≤ stT284 297 := by
  have hc : ((-94451/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54806042809/1250000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-94451/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c298 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-971281/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7253379/10000000) (δ := 14349/1000000000) (ψ := -92959/500000) 284 258
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t298 : ((-112541288517/2000000000000 : ℚ) : ℝ) ≤ stT284 298 := by
  have hc : ((-971381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112541288517/2000000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-971381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c299 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-370109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -609351/1250000) (δ := 14349/1000000000) (ψ := -92959/500000) 284 258
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t299 : ((-42819483567/2000000000000 : ℚ) : ℝ) ≤ stT284 299 := by
  have hc : ((-370209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42819483567/2000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-370209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c300 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((134723/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2504189/10000000) (δ := 14349/1000000000) (ψ := -92959/500000) 284 258
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t300 : ((777678903/25000000000 : ℚ) : ℝ) ≤ stT284 300 := by
  have hc : ((67349/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((777678903/25000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((67349/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c301 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((624/625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141451/10000000) (δ := 14349/1000000000) (ψ := -92959/500000) 284 258
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t301 : ((575410137/10000000000 : ℚ) : ℝ) ≤ stT284 301 := by
  have hc : ((9983/10000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((575410137/10000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((9983/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c302 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((632987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2213477/10000000) (δ := 14349/1000000000) (ψ := -92959/500000) 284 258
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t302 : ((72837066169/2000000000000 : ℚ) : ℝ) ≤ stT284 302 := by
  have hc : ((632887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72837066169/2000000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((632887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c303 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-250737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912119/2000000) (δ := 14349/1000000000) (ψ := -92959/500000) 284 258
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t303 : ((-28820418789/2000000000000 : ℚ) : ℝ) ≤ stT284 303 := by
  have hc : ((-250837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28820418789/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-250837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c304 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-928069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3449987/5000000) (δ := 14349/1000000000) (ψ := -92959/500000) 284 258
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t304 : ((-26617102413/500000000000 : ℚ) : ℝ) ≤ stT284 304 := by
  have hc : ((-928169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26617102413/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-928169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c305 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-425987/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6476349/10000000) (δ := 7121/500000000) (ψ := -92959/500000) 284 259
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t305 : ((-243948360163/5000000000000 : ℚ) : ℝ) ≤ stT284 305 := by
  have hc : ((-426037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243948360163/5000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-426037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c306 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-11247/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -830447/2000000) (δ := 7121/500000000) (ψ := -92959/500000) 284 259
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t306 : ((-6436628289/1250000000000 : ℚ) : ℝ) ≤ stT284 306 := by
  have hc : ((-22519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6436628289/1250000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-22519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c307 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((74229/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1835789/10000000) (δ := 7121/500000000) (ψ := -92959/500000) 284 259
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t307 : ((4235900987/100000000000 : ℚ) : ℝ) ≤ stT284 307 := by
  have hc : ((74219/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4235900987/100000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((74219/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c308 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((196429/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 473131/10000000) (δ := 7121/500000000) (ψ := -92959/500000) 284 259
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t308 : ((55957120509/1000000000000 : ℚ) : ℝ) ≤ stT284 308 := by
  have hc : ((196409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55957120509/1000000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((196409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c309 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((222403/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693649/2500000) (δ := 7121/500000000) (ψ := -92959/500000) 284 259
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t309 : ((1581152183/62500000000 : ℚ) : ℝ) ≤ stT284 309 := by
  have hc : ((222353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1581152183/62500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((222353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c310 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-22047/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2534303/5000000) (δ := 7121/500000000) (ψ := -92959/500000) 284 259
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t310 : ((-1565587253/62500000000 : ℚ) : ℝ) ≤ stT284 310 := by
  have hc : ((-5513/12500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1565587253/62500000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-5513/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c311 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-980171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7355303/10000000) (δ := 7121/500000000) (ψ := -92959/500000) 284 259
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t311 : ((-69482588751/1250000000000 : ℚ) : ℝ) ≤ stT284 311 := by
  have hc : ((-980271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69482588751/1250000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-980271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c312 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-756909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3036709/5000000) (δ := 3567/250000000) (ψ := -92959/500000) 284 260
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t312 : ((-428572318251/10000000000000 : ℚ) : ℝ) ≤ stT284 312 := by
  have hc : ((-757009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428572318251/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-757009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c313 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((1569/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1900709/5000000) (δ := 3567/250000000) (ψ := -92959/500000) 284 260
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t313 : ((7080673791/2500000000000 : ℚ) : ℝ) ≤ stT284 313 := by
  have hc : ((12527/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7080673791/2500000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((12527/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c314 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((816967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76833/500000) (δ := 3567/250000000) (ψ := -92959/500000) 284 260
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t314 : ((115246046961/2500000000000 : ℚ) : ℝ) ≤ stT284 314 := by
  have hc : ((816867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115246046961/2500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((816867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c315 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((239677/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720927/10000000) (δ := 3567/250000000) (ψ := -92959/500000) 284 260
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t315 : ((8439285267/156250000000 : ℚ) : ℝ) ≤ stT284 315 := by
  have hc : ((59913/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8439285267/156250000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((59913/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c316 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((373017/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2971343/10000000) (δ := 3567/250000000) (ψ := -92959/500000) 284 260
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t316 : ((209781847931/10000000000000 : ℚ) : ℝ) ≤ stT284 316 := by
  have hc : ((372917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209781847931/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((372917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c317 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-492569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303647/2500000) (δ := 3567/250000000) (ψ := -92959/500000) 284 260
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t317 : ((-34588812483/1250000000000 : ℚ) : ℝ) ≤ stT284 317 := by
  have hc : ((-492669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34588812483/1250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-492669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c318 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-61689/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1862701/2500000) (δ := 3567/250000000) (ψ := -92959/500000) 284 260
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t318 : ((-138388121713/2500000000000 : ℚ) : ℝ) ≤ stT284 318 := by
  have hc : ((-246781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138388121713/2500000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-246781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c319 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-372443/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6027901/10000000) (δ := 23/1600000) (ψ := -92959/500000) 284 261
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t319 : ((-208556223249/5000000000000 : ℚ) : ℝ) ≤ stT284 319 := by
  have hc : ((-372493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208556223249/5000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-372493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c320 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((303/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3805743/10000000) (δ := 23/1600000) (ψ := -92959/500000) 284 261
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t320 : ((169032463/62500000000 : ℚ) : ℝ) ≤ stT284 320 := by
  have hc : ((2419/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169032463/62500000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((2419/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c321 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((804383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1590401/10000000) (δ := 23/1600000) (ψ := -92959/500000) 284 261
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t321 : ((89781307007/2000000000000 : ℚ) : ℝ) ≤ stT284 321 := by
  have hc : ((804283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89781307007/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((804283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c322 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((969603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 617983/10000000) (δ := 23/1600000) (ψ := -92959/500000) 284 261
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t322 : ((270141346417/5000000000000 : ℚ) : ℝ) ≤ stT284 322 := by
  have hc : ((969503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270141346417/5000000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((969503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c323 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((42863/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2819551/10000000) (δ := 23/1600000) (ψ := -92959/500000) 284 261
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t323 : ((11922004571/500000000000 : ℚ) : ℝ) ≤ stT284 323 := by
  have hc : ((42853/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11922004571/500000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((42853/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c324 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-210671/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5014303/10000000) (δ := 23/1600000) (ψ := -92959/500000) 284 261
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t324 : ((-29266828969/1250000000000 : ℚ) : ℝ) ≤ stT284 324 := by
  have hc : ((-210721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29266828969/1250000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-210721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c325 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-966211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7202239/10000000) (δ := 23/1600000) (ψ := -92959/500000) 284 261
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t325 : ((-536013678011/10000000000000 : ℚ) : ℝ) ≤ stT284 325 := by
  have hc : ((-966311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536013678011/10000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-966311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c326 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-818611/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6324463/10000000) (δ := 179/12500000) (ψ := -92959/500000) 284 262
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t326 : ((-453442268639/10000000000000 : ℚ) : ℝ) ≤ stT284 326 := by
  have hc : ((-818711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453442268639/10000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-818711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c327 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-22259/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33199/80000) (δ := 179/12500000) (ψ := -92959/500000) 284 262
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t327 : ((-1540387071/312500000000 : ℚ) : ℝ) ≤ stT284 327 := by
  have hc : ((-5571/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1540387071/312500000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-5571/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c328 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((140377/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198189/1000000) (δ := 179/12500000) (ψ := -92959/500000) 284 262
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t328 : ((77499100049/2000000000000 : ℚ) : ℝ) ≤ stT284 328 := by
  have hc : ((140357/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77499100049/2000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((140357/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c329 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((498713/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179421/10000000) (δ := 179/12500000) (ψ := -92959/500000) 284 262
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t329 : ((274921389171/5000000000000 : ℚ) : ℝ) ≤ stT284 329 := by
  have hc : ((498663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274921389171/5000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((498663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c330 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((1859/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11671/50000) (δ := 179/12500000) (ψ := -92959/500000) 284 262
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t330 : ((16370754459/500000000000 : ℚ) : ℝ) ≤ stT284 330 := by
  have hc : ((29739/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16370754459/500000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((29739/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c331 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-220359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4482447/10000000) (δ := 179/12500000) (ψ := -92959/500000) 284 262
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t331 : ((-2423505787/200000000000 : ℚ) : ℝ) ≤ stT284 331 := by
  have hc : ((-220459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2423505787/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-220459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c332 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-881437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6624233/10000000) (δ := 179/12500000) (ψ := -92959/500000) 284 262
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t332 : ((-241903449707/5000000000000 : ℚ) : ℝ) ≤ stT284 332 := by
  have hc : ((-881537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241903449707/5000000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-881537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c333 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-935109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1389681/2000000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t333 : ((-512491726373/10000000000000 : ℚ) : ℝ) ≤ stT284 333 := by
  have hc : ((-935209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512491726373/10000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-935209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c334 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-349457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -481947/1000000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t334 : ((-23908650129/1250000000000 : ℚ) : ℝ) ≤ stT284 334 := by
  have hc : ((-349557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23908650129/1250000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-349557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c335 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((236219/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1348427/5000000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t335 : ((64516411251/2500000000000 : ℚ) : ℝ) ≤ stT284 335 := by
  have hc : ((236169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64516411251/2500000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((236169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c336 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((973151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145157/2500000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t336 : ((66355266843/1250000000000 : ℚ) : ℝ) ≤ stT284 336 := by
  have hc : ((973051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66355266843/1250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((973051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c337 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((16373/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30587/200000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t337 : ((4458920157/100000000000 : ℚ) : ℝ) ≤ stT284 337 := by
  have hc : ((16371/20000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4458920157/100000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((16371/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c338 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((58661/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3633009/10000000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t338 : ((3985020501/625000000000 : ℚ) : ℝ) ≤ stT284 338 := by
  have hc : ((58611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3985020501/625000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((58611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c339 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-330229/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2865281/5000000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t339 : ((-89691556077/2500000000000 : ℚ) : ℝ) ≤ stT284 339 := by
  have hc : ((-330279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89691556077/2500000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-330279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c340 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-999917/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7821867/10000000) (δ := 14213/1000000000) (ψ := -92959/500000) 284 263
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t340 : ((-542336219559/10000000000000 : ℚ) : ℝ) ≤ stT284 340 := by
  have hc : ((-1000017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-542336219559/10000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-1000017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c341 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-681339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -725121/1250000) (δ := 14297/1000000000) (ψ := -92959/500000) 284 264
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t341 : ((-369020343109/10000000000000 : ℚ) : ℝ) ≤ stT284 341 := by
  have hc : ((-681439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369020343109/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-681439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c342 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((40977/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1191/3200) (δ := 14297/1000000000) (ψ := -92959/500000) 284 264
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t342 : ((11065392063/2500000000000 : ℚ) : ℝ) ≤ stT284 342 := by
  have hc : ((40927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11065392063/2500000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((40927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c343 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((158053/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206111/1250000) (δ := 14297/1000000000) (ψ := -92959/500000) 284 264
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t343 : ((85329760317/2000000000000 : ℚ) : ℝ) ≤ stT284 343 := by
  have hc : ((158033/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85329760317/2000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((158033/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c344 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((19721/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26129/625000) (δ := 14297/1000000000) (ψ := -92959/500000) 284 264
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t344 : ((10631755197/200000000000 : ℚ) : ℝ) ≤ stT284 344 := by
  have hc : ((19719/20000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10631755197/200000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((19719/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c345 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((273667/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 619763/2500000) (δ := 14297/1000000000) (ψ := -92959/500000) 284 264
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t345 : ((147310194077/5000000000000 : ℚ) : ℝ) ≤ stT284 345 := by
  have hc : ((273617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147310194077/5000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((273617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c346 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-240427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 906801/2000000) (δ := 14297/1000000000) (ψ := -92959/500000) 284 264
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t346 : ((-32327069327/2500000000000 : ℚ) : ℝ) ≤ stT284 346 := by
  have hc : ((-240527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32327069327/2500000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-240527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c347 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-873541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316613/2000000) (δ := 14297/1000000000) (ψ := -92959/500000) 284 264
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t347 : ((-468995824389/10000000000000 : ℚ) : ℝ) ≤ stT284 347 := by
  have hc : ((-873641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468995824389/10000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-873641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c348 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-952669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1770433/2500000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t348 : ((-510738491833/10000000000000 : ℚ) : ℝ) ≤ stT284 348 := by
  have hc : ((-952769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-510738491833/10000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-952769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c349 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-17289/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5044387/10000000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t349 : ((-1157091923/50000000000 : ℚ) : ℝ) ≤ stT284 349 := by
  have hc : ((-17293/40000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1157091923/50000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-17293/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c350 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((357531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602587/2000000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t350 : ((95527366491/5000000000000 : ℚ) : ℝ) ≤ stT284 350 := by
  have hc : ((357431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95527366491/5000000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((357431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c351 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((461519/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493617/5000000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t351 : ((192432573/3906250000 : ℚ) : ℝ) ≤ stT284 351 := by
  have hc : ((461469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192432573/3906250000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((461469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c352 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((457949/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 206529/2000000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t352 : ((244060624899/5000000000000 : ℚ) : ℝ) ≤ stT284 352 := by
  have hc : ((457899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244060624899/5000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((457899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c353 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((344831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 761711/2500000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t353 : ((91740847913/5000000000000 : ℚ) : ℝ) ≤ stT284 353 := by
  have hc : ((344731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91740847913/5000000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((344731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c354 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-21809/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5055363/10000000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t354 : ((-1159403193/50000000000 : ℚ) : ℝ) ≤ stT284 354 := by
  have hc : ((-10907/25000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1159403193/50000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-10907/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c355 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-237439/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7058131/10000000) (δ := 14399/1000000000) (ψ := -92959/500000) 284 265
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t355 : ((-3150820767/62500000000 : ℚ) : ℝ) ≤ stT284 355 := by
  have hc : ((-29683/31250 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3150820767/62500000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-29683/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c356 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-44337/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3326301/5000000) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t356 : ((-11750607829/250000000000 : ℚ) : ℝ) ≤ stT284 356 := by
  have hc : ((-22171/25000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11750607829/250000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-22171/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c357 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-289423/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1165263/2500000) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t357 : ((-153232074411/10000000000000 : ℚ) : ℝ) ≤ stT284 357 := by
  have hc : ((-289523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153232074411/10000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-289523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c358 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((48011/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16719/62500) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t358 : ((6342324129/250000000000 : ℚ) : ℝ) ≤ stT284 358 := by
  have hc : ((48001/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6342324129/250000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((48001/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c359 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((480827/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347283/5000000) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t359 : ((253744004283/5000000000000 : ℚ) : ℝ) ≤ stT284 359 := by
  have hc : ((480777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253744004283/5000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((480777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c360 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((2724/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1280441/10000000) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t360 : ((11484068817/250000000000 : ℚ) : ℝ) ≤ stT284 360 := by
  have hc : ((43579/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11484068817/250000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((43579/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c361 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((133767/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 324991/1000000) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t361 : ((14075452571/1000000000000 : ℚ) : ℝ) ≤ stT284 361 := by
  have hc : ((133717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14075452571/1000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((133717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c362 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-246179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5213983/10000000) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t362 : ((-129415253881/5000000000000 : ℚ) : ℝ) ≤ stT284 362 := by
  have hc : ((-246229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129415253881/5000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-246229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c363 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-481543/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7172589/10000000) (δ := 3573/250000000) (ψ := -92959/500000) 284 266
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t363 : ((-3949544193/78125000000 : ℚ) : ℝ) ≤ stT284 363 := by
  have hc : ((-481593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3949544193/78125000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-481593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c364 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-174673/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1645541/2500000) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t364 : ((-91564113099/2000000000000 : ℚ) : ℝ) ≤ stT284 364 := by
  have hc : ((-174693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91564113099/2000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-174693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c365 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-69789/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4634279/10000000) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t365 : ((-570973799/39062500000 : ℚ) : ℝ) ≤ stT284 365 := by
  have hc : ((-34907/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-570973799/39062500000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-34907/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c366 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((474247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2691719/10000000) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t366 : ((61960107519/2500000000000 : ℚ) : ℝ) ≤ stT284 366 := by
  have hc : ((474147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61960107519/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((474147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c367 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((190961/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188621/2500000) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t367 : ((19934049459/400000000000 : ℚ) : ℝ) ≤ stT284 367 := by
  have hc : ((190941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19934049459/400000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((190941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c368 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((222779/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1177497/10000000) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t368 : ((29029635411/625000000000 : ℚ) : ℝ) ≤ stT284 368 := by
  have hc : ((111377/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29029635411/625000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((111377/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c369 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((161599/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97007/312500) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t369 : ((84099016871/5000000000000 : ℚ) : ℝ) ≤ stT284 369 := by
  have hc : ((161549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84099016871/5000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((161549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c370 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-425497/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 628221/1250000) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t370 : ((-55314416493/2500000000000 : ℚ) : ℝ) ≤ stT284 370 := by
  have hc : ((-425597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55314416493/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-425597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c371 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-467103/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3471029/5000000) (δ := 7109/500000000) (ψ := -92959/500000) 284 267
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t371 : ((-9701366351/200000000000 : ℚ) : ℝ) ≤ stT284 371 := by
  have hc : ((-467153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9701366351/200000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-467153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c372 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-921177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6854727/10000000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t372 : ((-119415003463/2500000000000 : ℚ) : ℝ) ≤ stT284 372 := by
  have hc : ((-921277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119415003463/2500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-921277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c373 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-397387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4948661/10000000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t373 : ((-205811216347/10000000000000 : ℚ) : ℝ) ≤ stT284 373 := by
  have hc : ((-397487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205811216347/10000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-397487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c374 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((2153/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1523889/5000000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t374 : ((8903721053/500000000000 : ℚ) : ℝ) ≤ stT284 374 := by
  have hc : ((17219/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8903721053/500000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((17219/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c375 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((895721/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -230373/2000000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t375 : ((462495997537/10000000000000 : ℚ) : ℝ) ≤ stT284 375 := by
  have hc : ((895621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462495997537/10000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((895621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c376 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((191327/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92367/1250000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t376 : ((9865893297/200000000000 : ℚ) : ℝ) ≤ stT284 376 := by
  have hc : ((191307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9865893297/200000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((191307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c377 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((497677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328087/1250000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t377 : ((128132546001/5000000000000 : ℚ) : ℝ) ≤ stT284 377 := by
  have hc : ((497577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128132546001/5000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((497577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c378 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-229339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2252743/5000000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t378 : ((-23602160491/2000000000000 : ℚ) : ℝ) ≤ stT284 378 := by
  have hc : ((-229439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23602160491/2000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-229439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c379 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-831473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6381377/10000000) (δ := 7163/500000000) (ψ := -92959/500000) 284 268
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t379 : ((-213575388309/5000000000000 : ℚ) : ℝ) ≤ stT284 379 := by
  have hc : ((-831573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213575388309/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-831573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c380 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-987339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7455737/10000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t380 : ((-50654633261/1000000000000 : ℚ) : ℝ) ≤ stT284 380 := by
  have hc : ((-987439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50654633261/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-987439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c381 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-9643/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2794893/5000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t381 : ((-19764254727/625000000000 : ℚ) : ℝ) ≤ stT284 381 := by
  have hc : ((-154313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19764254727/625000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-154313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c382 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((4953/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3728663/10000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t382 : ((2530974957/625000000000 : ℚ) : ℝ) ≤ stT284 382 := by
  have hc : ((19787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2530974957/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((19787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c383 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((732367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187251/1000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t383 : ((365401233/9765625000 : ℚ) : ℝ) ≤ stT284 383 := by
  have hc : ((732267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365401233/9765625000 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((732267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c384 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((249991/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10557/5000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t384 : ((6378007473/125000000000 : ℚ) : ℝ) ≤ stT284 384 := by
  have hc : ((124983/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6378007473/125000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((124983/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c385 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((745053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912727/5000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t385 : ((379663061591/10000000000000 : ℚ) : ℝ) ≤ stT284 385 := by
  have hc : ((744953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379663061591/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((744953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c386 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((25933/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1833597/5000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t386 : ((1648351161/312500000000 : ℚ) : ℝ) ≤ stT284 386 := by
  have hc : ((6477/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1648351161/312500000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((6477/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c387 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-589851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5504177/10000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t387 : ((-299889201879/10000000000000 : ℚ) : ℝ) ≤ stT284 387 := by
  have hc : ((-589951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299889201879/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-589951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c388 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-978651/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3668237/5000000) (δ := 1437/100000000) (ψ := -92959/500000) 284 269
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t388 : ((-248443217587/5000000000000 : ℚ) : ℝ) ≤ stT284 388 := by
  have hc : ((-978751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248443217587/5000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-978751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c389 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-432909/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6543949/10000000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t389 : ((-219519305139/5000000000000 : ℚ) : ℝ) ≤ stT284 389 := by
  have hc : ((-432959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219519305139/5000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-432959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c390 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-312327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -944219/2000000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t390 : ((-15820365999/1000000000000 : ℚ) : ℝ) ≤ stT284 390 := by
  have hc : ((-312427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15820365999/1000000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-312427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c391 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((199133/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2902927/10000000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t391 : ((100680453843/5000000000000 : ℚ) : ℝ) ≤ stT284 391 := by
  have hc : ((199083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100680453843/5000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((199083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c392 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((453277/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544687/5000000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t392 : ((57228520063/1250000000000 : ℚ) : ℝ) ≤ stT284 392 := by
  have hc : ((453227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57228520063/1250000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((453227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c393 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((958863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179891/2500000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t393 : ((483631696379/10000000000000 : ℚ) : ℝ) ≤ stT284 393 := by
  have hc : ((958763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((483631696379/10000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((958763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c394 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((266119/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2523887/10000000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t394 : ((8377714603/312500000000 : ℚ) : ℝ) ≤ stT284 394 := by
  have hc : ((266069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8377714603/312500000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((266069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c395 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-157977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 864719/2000000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t395 : ((-15907446587/2000000000000 : ℚ) : ℝ) ≤ stT284 395 := by
  have hc : ((-158077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15907446587/2000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-158077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c396 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-153731/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 611883/1000000) (δ := 14263/1000000000) (ψ := -92959/500000) 284 270
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t396 : ((-77262798769/2000000000000 : ℚ) : ℝ) ≤ stT284 396 := by
  have hc : ((-153751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77262798769/2000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-153751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c397 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-499877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7798513/10000000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t397 : ((-125453181161/2500000000000 : ℚ) : ℝ) ≤ stT284 397 := by
  have hc : ((-499927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125453181161/2500000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-499927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c398 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-740707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1202459/2000000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t398 : ((-74266642557/2000000000000 : ℚ) : ℝ) ≤ stT284 398 := by
  have hc : ((-740807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74266642557/2000000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-740807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c399 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-60577/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4230621/10000000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t399 : ((-30351513129/5000000000000 : ℚ) : ℝ) ≤ stT284 399 := by
  have hc : ((-60627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30351513129/5000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-60627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c400 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((277943/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122671/500000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t400 : ((277893/10000000 : ℚ) : ℝ) ≤ stT284 400 := by
  have hc : ((277893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277893/10000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((277893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c401 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((963169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -680621/10000000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t401 : ((30058346559/625000000000 : ℚ) : ℝ) ≤ stT284 401 := by
  have hc : ((963069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30058346559/625000000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((963069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c402 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((181367/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 217541/2000000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t402 : ((45223770819/1000000000000 : ℚ) : ℝ) ≤ stT284 402 := by
  have hc : ((181347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45223770819/1000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((181347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c403 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((416977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28517/100000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t403 : ((41532204879/2000000000000 : ℚ) : ℝ) ≤ stT284 403 := by
  have hc : ((416877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41532204879/2000000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((416877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c404 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-67579/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4611293/10000000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t404 : ((-8408568619/625000000000 : ℚ) : ℝ) ≤ stT284 404 := by
  have hc : ((-16901/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8408568619/625000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-16901/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c405 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-165633/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1273311/2000000) (δ := 14247/1000000000) (ψ := -92959/500000) 284 271
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t405 : ((-10289204789/250000000000 : ℚ) : ℝ) ≤ stT284 405 := by
  have hc : ((-165653/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10289204789/250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-165653/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c406 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-19889/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7590477/10000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t406 : ((-2467936043/50000000000 : ℚ) : ℝ) ≤ stT284 406 := by
  have hc : ((-19891/20000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2467936043/50000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-19891/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c407 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-346901/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5843877/10000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t407 : ((-85988682791/2500000000000 : ℚ) : ℝ) ≤ stT284 407 := by
  have hc : ((-346951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85988682791/2500000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-346951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c408 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-34881/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4101537/10000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t408 : ((-8646714947/2500000000000 : ℚ) : ℝ) ≤ stT284 408 := by
  have hc : ((-34931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8646714947/2500000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-34931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c409 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((585433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2363457/10000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t409 : ((72357109461/2500000000000 : ℚ) : ℝ) ≤ stT284 409 := by
  have hc : ((585333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72357109461/2500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((585333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c410 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((242113/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -629637/10000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t410 : ((1868102313/39062500000 : ℚ) : ℝ) ≤ stT284 410 := by
  have hc : ((30261/31250 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1868102313/39062500000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((30261/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c411 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((904753/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549997/5000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t411 : ((446231852739/10000000000000 : ℚ) : ℝ) ≤ stT284 411 := by
  have hc : ((904653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446231852739/10000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((904653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c412 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((13329/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565073/2000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t412 : ((6565178881/312500000000 : ℚ) : ℝ) ≤ stT284 412 := by
  have hc : ((106607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6565178881/312500000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((106607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c413 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-122647/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4546547/10000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t413 : ((-15093816849/1250000000000 : ℚ) : ℝ) ≤ stT284 413 := by
  have hc : ((-122697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15093816849/1250000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-122697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c414 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-80439/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6263611/10000000) (δ := 7177/500000000) (ψ := -92959/500000) 284 272
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t414 : ((-19769295913/500000000000 : ℚ) : ℝ) ≤ stT284 414 := by
  have hc : ((-80449/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19769295913/500000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-80449/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c415 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-499399/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7731407/10000000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t415 : ((-245170024569/5000000000000 : ℚ) : ℝ) ≤ stT284 415 := by
  have hc : ((-499449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245170024569/5000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-499449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c416 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-743483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120453/200000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t416 : ((-364572052653/10000000000000 : ℚ) : ℝ) ≤ stT284 416 := by
  have hc : ((-743583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364572052653/10000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-743583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c417 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-155743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215897/500000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t417 : ((-76316784629/10000000000000 : ℚ) : ℝ) ≤ stT284 417 := by
  have hc : ((-155843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76316784629/10000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-155843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c418 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((7816/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -654337/2500000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t418 : ((12230907513/500000000000 : ℚ) : ℝ) ≤ stT284 418 := by
  have hc : ((125031/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12230907513/500000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((125031/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c419 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((932933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -920803/10000000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t419 : ((455717838323/10000000000000 : ℚ) : ℝ) ≤ stT284 419 := by
  have hc : ((932833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((455717838323/10000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((932833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c420 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((29773/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154339/2000000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t420 : ((2324193681/50000000000 : ℚ) : ℝ) ≤ stT284 420 := by
  have hc : ((238159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2324193681/50000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((238159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c421 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((553647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1230073/5000000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t421 : ((26978220139/1000000000000 : ℚ) : ℝ) ≤ stT284 421 := by
  have hc : ((553547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26978220139/1000000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((553547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c422 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-43471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4144621/10000000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t422 : ((-21185718153/5000000000000 : ℚ) : ℝ) ≤ stT284 422 := by
  have hc : ((-43521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21185718153/5000000000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-43521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c423 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-344179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5825049/10000000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t423 : ((-167369991693/5000000000000 : ℚ) : ℝ) ≤ stT284 423 := by
  have hc : ((-344229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167369991693/5000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-344229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c424 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-990081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1875393/2500000) (δ := 14341/1000000000) (ψ := -92959/500000) 284 273
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t424 : ((-480874471383/10000000000000 : ℚ) : ℝ) ≤ stT284 424 := by
  have hc : ((-990181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-480874471383/10000000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-990181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c425 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-863789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1633461/2500000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t425 : ((-26190522813/625000000000 : ℚ) : ℝ) ≤ stT284 425 := by
  have hc : ((-863889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26190522813/625000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-863889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c426 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-366537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2432601/5000000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t426 : ((-88818179887/5000000000000 : ℚ) : ℝ) ≤ stT284 426 := by
  have hc : ((-366637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88818179887/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-366637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c427 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((286537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -640093/2000000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t427 : ((138616316721/10000000000000 : ℚ) : ℝ) ≤ stT284 427 := by
  have hc : ((286437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138616316721/10000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((286437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c428 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((102033/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192463/1250000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t428 : ((12328361261/312500000000 : ℚ) : ℝ) ≤ stT284 428 := by
  have hc : ((204041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12328361261/312500000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((204041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c429 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((9989/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58647/5000000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t429 : ((301390397/6250000000 : ℚ) : ℝ) ≤ stT284 429 := by
  have hc : ((2497/2500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301390397/6250000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((2497/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c430 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((759563/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1770387/10000000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t430 : ((183122478023/5000000000000 : ℚ) : ℝ) ≤ stT284 430 := by
  have hc : ((759463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183122478023/5000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((759463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c431 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((25197/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136783/400000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t431 : ((24261891027/2500000000000 : ℚ) : ℝ) ≤ stT284 431 := by
  have hc : ((50369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24261891027/2500000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((50369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c432 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-87929/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1013/2000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t432 : ((-21157275287/1000000000000 : ℚ) : ℝ) ≤ stT284 432 := by
  have hc : ((-87949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21157275287/1000000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-87949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c433 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-56033/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3353331/5000000) (δ := 7117/500000000) (ψ := -92959/500000) 284 274
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t433 : ((-10772312949/250000000000 : ℚ) : ℝ) ≤ stT284 433 := by
  have hc : ((-224157/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10772312949/250000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-224157/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c434 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-490407/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7363473/10000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t434 : ((-14714200457/312500000000 : ℚ) : ℝ) ≤ stT284 434 := by
  have hc : ((-490457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14714200457/312500000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-490457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c435 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-660111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44761/78125) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t435 : ((-39568425863/1250000000000 : ℚ) : ℝ) ≤ stT284 435 := by
  have hc : ((-660211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39568425863/1250000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-660211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c436 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-8599/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2049553/5000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t436 : ((-4124167911/1250000000000 : ℚ) : ℝ) ≤ stT284 436 := by
  have hc : ((-17223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4124167911/1250000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-17223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c437 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((549503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2472567/10000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t437 : ((65703654173/2500000000000 : ℚ) : ℝ) ≤ stT284 437 := by
  have hc : ((549403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65703654173/2500000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((549403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c438 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((942801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -849649/10000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t438 : ((225219753209/5000000000000 : ℚ) : ℝ) ≤ stT284 438 := by
  have hc : ((942701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225219753209/5000000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((942701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c439 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((476501/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 384753/5000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t439 : ((227397198123/5000000000000 : ℚ) : ℝ) ≤ stT284 439 := by
  have hc : ((476451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227397198123/5000000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((476451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c440 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((115687/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2384969/10000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t440 : ((55142044577/2000000000000 : ℚ) : ℝ) ≤ stT284 440 := by
  have hc : ((115667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55142044577/2000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((115667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c441 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-3487/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199837/500000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t441 : ((-3332860809/2500000000000 : ℚ) : ℝ) ≤ stT284 441 := by
  have hc : ((-6999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3332860809/2500000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-6999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c442 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-124379/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 560489/1000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t442 : ((-14792658287/500000000000 : ℚ) : ℝ) ≤ stT284 442 := by
  have hc : ((-124399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14792658287/500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-124399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c443 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-966947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7209419/10000000) (δ := 3569/250000000) (ψ := -92959/500000) 284 275
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t443 : ((-91891707081/2000000000000 : ℚ) : ℝ) ≤ stT284 443 := by
  have hc : ((-967047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91891707081/2000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-967047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c444 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-23193/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1724409/2500000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t444 : ((-22016194389/500000000000 : ℚ) : ℝ) ≤ stT284 444 := by
  have hc : ((-46391/50000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22016194389/500000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-46391/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c445 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-522127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5300349/10000000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t445 : ((-123779810221/5000000000000 : ℚ) : ℝ) ≤ stT284 445 := by
  have hc : ((-522227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123779810221/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-522227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c446 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((88037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -926653/2500000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t446 : ((41639312681/10000000000000 : ℚ) : ℝ) ≤ stT284 446 := by
  have hc : ((87937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41639312681/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((87937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c447 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((132507/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132281/625000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t447 : ((62664098721/2000000000000 : ℚ) : ℝ) ≤ stT284 447 := by
  have hc : ((132487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62664098721/2000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((132487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c448 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((122203/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529859/10000000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t448 : ((23091805071/500000000000 : ℚ) : ℝ) ≤ stT284 448 := by
  have hc : ((244381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23091805071/500000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((244381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c449 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((912573/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1053157/10000000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t449 : ((430622470417/10000000000000 : ℚ) : ℝ) ≤ stT284 449 := by
  have hc : ((912473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430622470417/10000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((912473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c450 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((494899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316347/5000000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t450 : ((58312556949/2500000000000 : ℚ) : ℝ) ≤ stT284 450 := by
  have hc : ((494799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58312556949/2500000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((494799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c451 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-56233/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 263047/625000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t451 : ((-13251325803/2500000000000 : ℚ) : ℝ) ≤ stT284 451 := by
  have hc : ((-56283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13251325803/2500000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-56283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c452 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-168887/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289063/500000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t452 : ((-4965601077/156250000000 : ℚ) : ℝ) ≤ stT284 452 := by
  have hc : ((-10557/15625 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4965601077/156250000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-10557/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c453 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-489889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183759/250000) (δ := 14383/1000000000) (ψ := -92959/500000) 284 276
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t453 : ((-230193429699/5000000000000 : ℚ) : ℝ) ≤ stT284 453 := by
  have hc : ((-489939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230193429699/5000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-489939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c454 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-911133/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3396027/5000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t454 : ((-106915879123/2500000000000 : ℚ) : ℝ) ≤ stT284 454 := by
  have hc : ((-911233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106915879123/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-911233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c455 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-497869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5229841/10000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t455 : ((-29181481369/1250000000000 : ℚ) : ℝ) ≤ stT284 455 := by
  have hc : ((-497969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29181481369/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-497969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c456 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((4087/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3671107/10000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t456 : ((478009059/100000000000 : ℚ) : ℝ) ≤ stT284 456 := by
  have hc : ((4083/40000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478009059/100000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((4083/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c457 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((82841/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -528963/2500000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t457 : ((3874551573/125000000000 : ℚ) : ℝ) ≤ stT284 457 := by
  have hc : ((165657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3874551573/125000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((165657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c458 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((487333/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281967/5000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t458 : ((227692240127/5000000000000 : ℚ) : ℝ) ≤ stT284 458 := by
  have hc : ((487283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227692240127/5000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((487283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c459 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((184687/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 984647/10000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t459 : ((2154879223/50000000000 : ℚ) : ℝ) ≤ stT284 459 := by
  have hc : ((184667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2154879223/50000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((184667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c460 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((530251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2529749/10000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t460 : ((61795991013/2500000000000 : ℚ) : ℝ) ≤ stT284 460 := by
  have hc : ((530151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61795991013/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((530151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c461 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-11561/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 814317/2000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t461 : ((-5393816007/2000000000000 : ℚ) : ℝ) ≤ stT284 461 := by
  have hc : ((-11581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5393816007/2000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-11581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c462 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-311749/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5610013/10000000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t462 : ((-145062302157/5000000000000 : ℚ) : ℝ) ≤ stT284 462 := by
  have hc : ((-311799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145062302157/5000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-311799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c463 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-240019/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285807/400000) (δ := 14313/1000000000) (ψ := -92959/500000) 284 277
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t463 : ((-1394475607/31250000000 : ℚ) : ℝ) ≤ stT284 463 := by
  have hc : ((-60011/62500 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1394475607/31250000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-60011/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c464 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-946299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7030963/10000000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t464 : ((-439355325361/10000000000000 : ℚ) : ℝ) ≤ stT284 464 := by
  have hc : ((-946399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439355325361/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-946399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c465 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-294639/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1375601/2500000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t465 : ((-136658782171/5000000000000 : ℚ) : ℝ) ≤ stT284 465 := by
  have hc : ((-294689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136658782171/5000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-294689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c466 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-803/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1988591/5000000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t466 : ((-186918147/200000000000 : ℚ) : ℝ) ≤ stT284 466 := by
  have hc : ((-807/40000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186918147/200000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-807/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c467 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((111057/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1227613/5000000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t467 : ((6422713191/250000000000 : ℚ) : ℝ) ≤ stT284 467 := by
  have hc : ((111037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6422713191/250000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((111037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c468 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((930649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117067/1250000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t468 : ((1720585101/40000000000 : ℚ) : ℝ) ≤ stT284 468 := by
  have hc : ((930549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1720585101/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((930549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c469 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((121663/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 578959/10000000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t469 : ((112345939857/2500000000000 : ℚ) : ℝ) ≤ stT284 469 := by
  have hc : ((243301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112345939857/2500000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((243301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c470 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((670083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 522797/2500000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t470 : ((61807941699/2000000000000 : ℚ) : ℝ) ≤ stT284 470 := by
  have hc : ((669983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61807941699/2000000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((669983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c471 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((4073/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1800111/5000000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t471 : ((600094929/100000000000 : ℚ) : ℝ) ≤ stT284 471 := by
  have hc : ((32559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((600094929/100000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((32559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c472 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-454337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5106061/10000000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t472 : ((-408538863/19531250000 : ℚ) : ℝ) ≤ stT284 472 := by
  have hc : ((-454437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408538863/19531250000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-454437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c473 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-878487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1321741/2000000) (δ := 7103/500000000) (ψ := -92959/500000) 284 278
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t473 : ((-403975181187/10000000000000 : ℚ) : ℝ) ≤ stT284 473 := by
  have hc : ((-878587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403975181187/10000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-878587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c474 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-994833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3799869/5000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t474 : ((-114247161457/2500000000000 : ℚ) : ℝ) ≤ stT284 474 := by
  have hc : ((-994933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114247161457/2500000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-994933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c475 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-95587/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6103413/10000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t475 : ((-5483013723/156250000000 : ℚ) : ℝ) ≤ stT284 475 := by
  have hc : ((-191199/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5483013723/156250000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-191199/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c476 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-269927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4610283/10000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t476 : ((-2475337509/200000000000 : ℚ) : ℝ) ≤ stT284 476 := by
  have hc : ((-270027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2475337509/200000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-270027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c477 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((63423/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3120277/10000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t477 : ((7257551201/500000000000 : ℚ) : ℝ) ≤ stT284 477 := by
  have hc : ((63403/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7257551201/500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((63403/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c478 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((49629/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -408331/2500000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t478 : ((90787599999/2500000000000 : ℚ) : ℝ) ≤ stT284 478 := by
  have hc : ((198491/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90787599999/2500000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((198491/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c479 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((998211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74783/5000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t479 : ((456047895121/10000000000000 : ℚ) : ℝ) ≤ stT284 479 := by
  have hc : ((998111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((456047895121/10000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((998111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c480 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((861549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 133121/1000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t480 : ((78639094863/2000000000000 : ℚ) : ℝ) ≤ stT284 480 := by
  have hc : ((861449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78639094863/2000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((861449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c481 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((86503/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2808791/10000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t481 : ((985819717/50000000000 : ℚ) : ℝ) ≤ stT284 481 := by
  have hc : ((86483/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((985819717/50000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((86483/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c482 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-142077/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428339/1000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t482 : ((-1011873709/156250000000 : ℚ) : ℝ) ≤ stT284 482 := by
  have hc : ((-142177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1011873709/156250000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-142177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c483 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-333863/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150973/2000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t483 : ((-18991969701/625000000000 : ℚ) : ℝ) ≤ stT284 483 := by
  have hc : ((-333913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18991969701/625000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-333913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c484 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-968353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3611679/5000000) (δ := 2861/200000000) (ψ := -92959/500000) 284 279
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t484 : ((-220103218669/5000000000000 : ℚ) : ℝ) ≤ stT284 484 := by
  have hc : ((-968453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220103218669/5000000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-968453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c485 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-236193/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7019237/10000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t485 : ((-53630580393/1250000000000 : ℚ) : ℝ) ≤ stT284 485 := by
  have hc : ((-118109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53630580393/1250000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-118109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c486 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-60671/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5556779/10000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t486 : ((-2752550841/100000000000 : ℚ) : ℝ) ≤ stT284 486 := by
  have hc : ((-60681/100000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2752550841/100000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-60681/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c487 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-68101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2048687/5000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t487 : ((-3863109243/1250000000000 : ℚ) : ℝ) ≤ stT284 487 := by
  have hc : ((-68201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3863109243/1250000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-68201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c488 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((246013/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2640951/10000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t488 : ((55671019457/2500000000000 : ℚ) : ℝ) ≤ stT284 488 := by
  have hc : ((245963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55671019457/2500000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((245963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c489 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((444639/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1187581/10000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t489 : ((40209962927/1000000000000 : ℚ) : ℝ) ≤ stT284 489 := by
  have hc : ((444589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40209962927/1000000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((444589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c490 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((994477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131439/5000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t490 : ((449212792881/10000000000000 : ℚ) : ℝ) ≤ stT284 490 := by
  have hc : ((994377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449212792881/10000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((994377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c491 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((24217/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 855213/5000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t491 : ((87420418323/2500000000000 : ℚ) : ℝ) ≤ stT284 491 := by
  have hc : ((193711/250000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87420418323/2500000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((193711/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c492 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((60783/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 197187/625000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t492 : ((13697013171/1000000000000 : ℚ) : ℝ) ≤ stT284 492 := by
  have hc : ((60763/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13697013171/1000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((60763/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c493 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-264643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143643/312500) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t493 : ((-59617211427/5000000000000 : ℚ) : ℝ) ≤ stT284 493 := by
  have hc : ((-264743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59617211427/5000000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-264743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c494 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-746863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150883/250000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t494 : ((-168037543443/5000000000000 : ℚ) : ℝ) ≤ stT284 494 := by
  have hc : ((-746963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168037543443/5000000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-746963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c495 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-494147/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3735541/5000000) (δ := 14391/1000000000) (ψ := -92959/500000) 284 280
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t495 : ((-222125242999/5000000000000 : ℚ) : ℝ) ≤ stT284 495 := by
  have hc : ((-494197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222125242999/5000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-494197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c496 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-182617/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6803959/10000000) (δ := 3571/250000000) (ψ := -92959/500000) 284 281
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t496 : ((-41003284959/1000000000000 : ℚ) : ℝ) ≤ stT284 496 := by
  have hc : ((-182637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41003284959/1000000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-182637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c497 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-109401/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1343487/2500000) (δ := 3571/250000000) (ψ := -92959/500000) 284 281
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t497 : ((-24541051301/1000000000000 : ℚ) : ℝ) ≤ stT284 497 := by
  have hc : ((-109421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24541051301/1000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-109421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c498 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-7943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123339/312500) (δ := 3571/250000000) (ψ := -92959/500000) 284 281
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t498 : ((-3604156773/10000000000000 : ℚ) : ℝ) ≤ stT284 498 := by
  have hc : ((-8043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3604156773/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-8043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c499 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((532677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -630647/2500000) (δ := 3571/250000000) (ψ := -92959/500000) 284 281
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t499 : ((238413952397/10000000000000 : ℚ) : ℝ) ≤ stT284 499 := by
  have hc : ((532577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238413952397/10000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((532577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_c500 :
    |Real.cos (((284 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((904553/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68823/625000) (δ := 3571/250000000) (ψ := -92959/500000) 284 281
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st284_t500 : ((404483139489/10000000000000 : ℚ) : ℝ) ≤ stT284 500 := by
  have hc : ((904453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((284 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st284_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404483139489/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((904453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st284_p1 : ((982667/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT284 (i+1) := by
  rw [Finset.sum_range_one]
  exact st284_t1

theorem st284_p2 : ((665506789239/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT284 (i+1))
      = (∑ i ∈ Finset.range 1, stT284 (i+1)) + stT284 2 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 1
    simpa using h
  have hprev := st284_p1
  have hstep := st284_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p3 : ((3092878306059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT284 (i+1))
      = (∑ i ∈ Finset.range 2, stT284 (i+1)) + stT284 3 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 2
    simpa using h
  have hprev := st284_p2
  have hstep := st284_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p4 : ((1254667938417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT284 (i+1))
      = (∑ i ∈ Finset.range 3, stT284 (i+1)) + stT284 4 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 3
    simpa using h
  have hprev := st284_p3
  have hstep := st284_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p5 : ((993429648511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT284 (i+1))
      = (∑ i ∈ Finset.range 4, stT284 (i+1)) + stT284 5 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 4
    simpa using h
  have hprev := st284_p4
  have hstep := st284_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p6 : ((3022664068949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT284 (i+1))
      = (∑ i ∈ Finset.range 5, stT284 (i+1)) + stT284 6 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 5
    simpa using h
  have hprev := st284_p5
  have hstep := st284_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p7 : ((4903613354659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT284 (i+1))
      = (∑ i ∈ Finset.range 6, stT284 (i+1)) + stT284 7 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 6
    simpa using h
  have hprev := st284_p6
  have hstep := st284_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p8 : ((6656763961237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT284 (i+1))
      = (∑ i ∈ Finset.range 7, stT284 (i+1)) + stT284 8 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 7
    simpa using h
  have hprev := st284_p7
  have hstep := st284_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p9 : ((1431796360497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT284 (i+1))
      = (∑ i ∈ Finset.range 8, stT284 (i+1)) + stT284 9 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 8
    simpa using h
  have hprev := st284_p8
  have hstep := st284_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p10 : ((6967534836529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT284 (i+1))
      = (∑ i ∈ Finset.range 9, stT284 (i+1)) + stT284 10 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 9
    simpa using h
  have hprev := st284_p9
  have hstep := st284_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p11 : ((5672356436461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT284 (i+1))
      = (∑ i ∈ Finset.range 10, stT284 (i+1)) + stT284 11 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 10
    simpa using h
  have hprev := st284_p10
  have hstep := st284_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p12 : ((4843155688349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT284 (i+1))
      = (∑ i ∈ Finset.range 11, stT284 (i+1)) + stT284 12 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 11
    simpa using h
  have hprev := st284_p11
  have hstep := st284_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p13 : ((6196956508349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT284 (i+1))
      = (∑ i ∈ Finset.range 12, stT284 (i+1)) + stT284 13 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 12
    simpa using h
  have hprev := st284_p12
  have hstep := st284_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p14 : ((11332343115259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT284 (i+1))
      = (∑ i ∈ Finset.range 13, stT284 (i+1)) + stT284 14 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 13
    simpa using h
  have hprev := st284_p13
  have hstep := st284_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p15 : ((8972410333237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT284 (i+1))
      = (∑ i ∈ Finset.range 14, stT284 (i+1)) + stT284 15 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 14
    simpa using h
  have hprev := st284_p14
  have hstep := st284_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p16 : ((3747466121123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT284 (i+1))
      = (∑ i ∈ Finset.range 15, stT284 (i+1)) + stT284 16 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 15
    simpa using h
  have hprev := st284_p15
  have hstep := st284_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p17 : ((953556372139/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT284 (i+1))
      = (∑ i ∈ Finset.range 16, stT284 (i+1)) + stT284 17 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 16
    simpa using h
  have hprev := st284_p16
  have hstep := st284_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p18 : ((4228702416319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT284 (i+1))
      = (∑ i ∈ Finset.range 17, stT284 (i+1)) + stT284 18 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 17
    simpa using h
  have hprev := st284_p17
  have hstep := st284_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p19 : ((10146792223397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT284 (i+1))
      = (∑ i ∈ Finset.range 18, stT284 (i+1)) + stT284 19 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 18
    simpa using h
  have hprev := st284_p18
  have hstep := st284_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p20 : ((8085043612541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT284 (i+1))
      = (∑ i ∈ Finset.range 19, stT284 (i+1)) + stT284 20 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 19
    simpa using h
  have hprev := st284_p19
  have hstep := st284_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p21 : ((6715263668093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT284 (i+1))
      = (∑ i ∈ Finset.range 20, stT284 (i+1)) + stT284 21 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 20
    simpa using h
  have hprev := st284_p20
  have hstep := st284_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p22 : ((6644338157957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT284 (i+1))
      = (∑ i ∈ Finset.range 21, stT284 (i+1)) + stT284 22 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 21
    simpa using h
  have hprev := st284_p21
  have hstep := st284_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p23 : ((6695768234717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT284 (i+1))
      = (∑ i ∈ Finset.range 22, stT284 (i+1)) + stT284 23 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 22
    simpa using h
  have hprev := st284_p22
  have hstep := st284_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p24 : ((5799107778893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT284 (i+1))
      = (∑ i ∈ Finset.range 23, stT284 (i+1)) + stT284 24 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 23
    simpa using h
  have hprev := st284_p23
  have hstep := st284_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p25 : ((954844197257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT284 (i+1))
      = (∑ i ∈ Finset.range 24, stT284 (i+1)) + stT284 25 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 24
    simpa using h
  have hprev := st284_p24
  have hstep := st284_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p26 : ((51020886829/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT284 (i+1))
      = (∑ i ∈ Finset.range 25, stT284 (i+1)) + stT284 26 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 25
    simpa using h
  have hprev := st284_p25
  have hstep := st284_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p27 : ((324347957941/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT284 (i+1))
      = (∑ i ∈ Finset.range 26, stT284 (i+1)) + stT284 27 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 26
    simpa using h
  have hprev := st284_p26
  have hstep := st284_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p28 : ((2016711375527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT284 (i+1))
      = (∑ i ∈ Finset.range 27, stT284 (i+1)) + stT284 28 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 27
    simpa using h
  have hprev := st284_p27
  have hstep := st284_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p29 : ((170001972687/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT284 (i+1))
      = (∑ i ∈ Finset.range 28, stT284 (i+1)) + stT284 29 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 28
    simpa using h
  have hprev := st284_p28
  have hstep := st284_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p30 : ((4407095906513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT284 (i+1))
      = (∑ i ∈ Finset.range 29, stT284 (i+1)) + stT284 30 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 29
    simpa using h
  have hprev := st284_p29
  have hstep := st284_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p31 : ((222700350741/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT284 (i+1))
      = (∑ i ∈ Finset.range 30, stT284 (i+1)) + stT284 31 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 30
    simpa using h
  have hprev := st284_p30
  have hstep := st284_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p32 : ((1854943354687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT284 (i+1))
      = (∑ i ∈ Finset.range 31, stT284 (i+1)) + stT284 32 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 31
    simpa using h
  have hprev := st284_p31
  have hstep := st284_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p33 : ((527659555403/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT284 (i+1))
      = (∑ i ∈ Finset.range 32, stT284 (i+1)) + stT284 33 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 32
    simpa using h
  have hprev := st284_p32
  have hstep := st284_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p34 : ((1883947465027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT284 (i+1))
      = (∑ i ∈ Finset.range 33, stT284 (i+1)) + stT284 34 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 33
    simpa using h
  have hprev := st284_p33
  have hstep := st284_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p35 : ((3569951294609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT284 (i+1))
      = (∑ i ∈ Finset.range 34, stT284 (i+1)) + stT284 35 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 34
    simpa using h
  have hprev := st284_p34
  have hstep := st284_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p36 : ((1047147125659/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT284 (i+1))
      = (∑ i ∈ Finset.range 35, stT284 (i+1)) + stT284 36 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 35
    simpa using h
  have hprev := st284_p35
  have hstep := st284_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p37 : ((5306874320303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT284 (i+1))
      = (∑ i ∈ Finset.range 36, stT284 (i+1)) + stT284 37 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 36
    simpa using h
  have hprev := st284_p36
  have hstep := st284_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p38 : ((942173730987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT284 (i+1))
      = (∑ i ∈ Finset.range 37, stT284 (i+1)) + stT284 38 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 37
    simpa using h
  have hprev := st284_p37
  have hstep := st284_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p39 : ((1309622532303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT284 (i+1))
      = (∑ i ∈ Finset.range 38, stT284 (i+1)) + stT284 39 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 38
    simpa using h
  have hprev := st284_p38
  have hstep := st284_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p40 : ((696802733871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT284 (i+1))
      = (∑ i ∈ Finset.range 39, stT284 (i+1)) + stT284 40 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 39
    simpa using h
  have hprev := st284_p39
  have hstep := st284_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p41 : ((3945858930573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT284 (i+1))
      = (∑ i ∈ Finset.range 40, stT284 (i+1)) + stT284 41 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 40
    simpa using h
  have hprev := st284_p40
  have hstep := st284_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p42 : ((5465379193719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT284 (i+1))
      = (∑ i ∈ Finset.range 41, stT284 (i+1)) + stT284 42 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 41
    simpa using h
  have hprev := st284_p41
  have hstep := st284_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p43 : ((6951684474179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT284 (i+1))
      = (∑ i ∈ Finset.range 42, stT284 (i+1)) + stT284 43 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 42
    simpa using h
  have hprev := st284_p42
  have hstep := st284_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p44 : ((8294877673723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT284 (i+1))
      = (∑ i ∈ Finset.range 43, stT284 (i+1)) + stT284 44 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 43
    simpa using h
  have hprev := st284_p43
  have hstep := st284_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p45 : ((2387403398639/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT284 (i+1))
      = (∑ i ∈ Finset.range 44, stT284 (i+1)) + stT284 45 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 44
    simpa using h
  have hprev := st284_p44
  have hstep := st284_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p46 : ((2164469658793/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT284 (i+1))
      = (∑ i ∈ Finset.range 45, stT284 (i+1)) + stT284 46 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 45
    simpa using h
  have hprev := st284_p45
  have hstep := st284_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p47 : ((2438120963087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT284 (i+1))
      = (∑ i ∈ Finset.range 46, stT284 (i+1)) + stT284 47 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 46
    simpa using h
  have hprev := st284_p46
  have hstep := st284_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p48 : ((681603078503/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT284 (i+1))
      = (∑ i ∈ Finset.range 47, stT284 (i+1)) + stT284 48 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 47
    simpa using h
  have hprev := st284_p47
  have hstep := st284_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p49 : ((14959774028889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT284 (i+1))
      = (∑ i ∈ Finset.range 48, stT284 (i+1)) + stT284 49 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 48
    simpa using h
  have hprev := st284_p48
  have hstep := st284_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p50 : ((3953158390827/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT284 (i+1))
      = (∑ i ∈ Finset.range 49, stT284 (i+1)) + stT284 50 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 49
    simpa using h
  have hprev := st284_p49
  have hstep := st284_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p51 : ((15795991223623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT284 (i+1))
      = (∑ i ∈ Finset.range 50, stT284 (i+1)) + stT284 51 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 50
    simpa using h
  have hprev := st284_p50
  have hstep := st284_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p52 : ((1482035226483/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT284 (i+1))
      = (∑ i ∈ Finset.range 51, stT284 (i+1)) + stT284 52 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 51
    simpa using h
  have hprev := st284_p51
  have hstep := st284_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p53 : ((3362832497013/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT284 (i+1))
      = (∑ i ∈ Finset.range 52, stT284 (i+1)) + stT284 53 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 52
    simpa using h
  have hprev := st284_p52
  have hstep := st284_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p54 : ((4993370593/3906250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT284 (i+1))
      = (∑ i ∈ Finset.range 53, stT284 (i+1)) + stT284 54 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 53
    simpa using h
  have hprev := st284_p53
  have hstep := st284_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p55 : ((13497778621207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT284 (i+1))
      = (∑ i ∈ Finset.range 54, stT284 (i+1)) + stT284 55 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 54
    simpa using h
  have hprev := st284_p54
  have hstep := st284_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p56 : ((14818149172157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT284 (i+1))
      = (∑ i ∈ Finset.range 55, stT284 (i+1)) + stT284 56 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 55
    simpa using h
  have hprev := st284_p55
  have hstep := st284_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p57 : ((15029507392461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT284 (i+1))
      = (∑ i ∈ Finset.range 56, stT284 (i+1)) + stT284 57 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 56
    simpa using h
  have hprev := st284_p56
  have hstep := st284_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p58 : ((6906768491943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT284 (i+1))
      = (∑ i ∈ Finset.range 57, stT284 (i+1)) + stT284 58 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 57
    simpa using h
  have hprev := st284_p57
  have hstep := st284_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p59 : ((3288909647349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT284 (i+1))
      = (∑ i ∈ Finset.range 58, stT284 (i+1)) + stT284 59 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 58
    simpa using h
  have hprev := st284_p58
  have hstep := st284_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p60 : ((7113949092491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT284 (i+1))
      = (∑ i ∈ Finset.range 59, stT284 (i+1)) + stT284 60 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 59
    simpa using h
  have hprev := st284_p59
  have hstep := st284_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p61 : ((7460652261003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT284 (i+1))
      = (∑ i ∈ Finset.range 60, stT284 (i+1)) + stT284 61 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 60
    simpa using h
  have hprev := st284_p60
  have hstep := st284_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p62 : ((862095548499/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT284 (i+1))
      = (∑ i ∈ Finset.range 61, stT284 (i+1)) + stT284 62 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 61
    simpa using h
  have hprev := st284_p61
  have hstep := st284_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p63 : ((6704689707623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT284 (i+1))
      = (∑ i ∈ Finset.range 62, stT284 (i+1)) + stT284 63 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 62
    simpa using h
  have hprev := st284_p62
  have hstep := st284_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p64 : ((7328102207623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT284 (i+1))
      = (∑ i ∈ Finset.range 63, stT284 (i+1)) + stT284 64 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 63
    simpa using h
  have hprev := st284_p63
  have hstep := st284_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p65 : ((7181027323349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT284 (i+1))
      = (∑ i ∈ Finset.range 64, stT284 (i+1)) + stT284 65 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 64
    simpa using h
  have hprev := st284_p64
  have hstep := st284_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p66 : ((13357085173183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT284 (i+1))
      = (∑ i ∈ Finset.range 65, stT284 (i+1)) + stT284 66 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 65
    simpa using h
  have hprev := st284_p65
  have hstep := st284_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p67 : ((14421142774669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT284 (i+1))
      = (∑ i ∈ Finset.range 66, stT284 (i+1)) + stT284 67 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 66
    simpa using h
  have hprev := st284_p66
  have hstep := st284_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p68 : ((14431354736107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT284 (i+1))
      = (∑ i ∈ Finset.range 67, stT284 (i+1)) + stT284 68 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 67
    simpa using h
  have hprev := st284_p67
  have hstep := st284_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p69 : ((3352464977251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT284 (i+1))
      = (∑ i ∈ Finset.range 68, stT284 (i+1)) + stT284 69 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 68
    simpa using h
  have hprev := st284_p68
  have hstep := st284_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p70 : ((1814572510047/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT284 (i+1))
      = (∑ i ∈ Finset.range 69, stT284 (i+1)) + stT284 70 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 69
    simpa using h
  have hprev := st284_p69
  have hstep := st284_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p71 : ((7084588472931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT284 (i+1))
      = (∑ i ∈ Finset.range 70, stT284 (i+1)) + stT284 71 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 70
    simpa using h
  have hprev := st284_p70
  have hstep := st284_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p72 : ((6784841016803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT284 (i+1))
      = (∑ i ∈ Finset.range 71, stT284 (i+1)) + stT284 72 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 71
    simpa using h
  have hprev := st284_p71
  have hstep := st284_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p73 : ((14700171484807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT284 (i+1))
      = (∑ i ∈ Finset.range 72, stT284 (i+1)) + stT284 73 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 72
    simpa using h
  have hprev := st284_p72
  have hstep := st284_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p74 : ((3414713412533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT284 (i+1))
      = (∑ i ∈ Finset.range 73, stT284 (i+1)) + stT284 74 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 73
    simpa using h
  have hprev := st284_p73
  have hstep := st284_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p75 : ((884370062627/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT284 (i+1))
      = (∑ i ∈ Finset.range 74, stT284 (i+1)) + stT284 75 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 74
    simpa using h
  have hprev := st284_p74
  have hstep := st284_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p76 : ((897244866099/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT284 (i+1))
      = (∑ i ∈ Finset.range 75, stT284 (i+1)) + stT284 76 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 75
    simpa using h
  have hprev := st284_p75
  have hstep := st284_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p77 : ((424303525911/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT284 (i+1))
      = (∑ i ∈ Finset.range 76, stT284 (i+1)) + stT284 77 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 76
    simpa using h
  have hprev := st284_p76
  have hstep := st284_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p78 : ((14660544424839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT284 (i+1))
      = (∑ i ∈ Finset.range 77, stT284 (i+1)) + stT284 78 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 77
    simpa using h
  have hprev := st284_p77
  have hstep := st284_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p79 : ((13553523087943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT284 (i+1))
      = (∑ i ∈ Finset.range 78, stT284 (i+1)) + stT284 79 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 78
    simpa using h
  have hprev := st284_p78
  have hstep := st284_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p80 : ((14469294973979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT284 (i+1))
      = (∑ i ∈ Finset.range 79, stT284 (i+1)) + stT284 80 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 79
    simpa using h
  have hprev := st284_p79
  have hstep := st284_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p81 : ((2773245120527/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT284 (i+1))
      = (∑ i ∈ Finset.range 80, stT284 (i+1)) + stT284 81 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 80
    simpa using h
  have hprev := st284_p80
  have hstep := st284_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p82 : ((2823679628303/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT284 (i+1))
      = (∑ i ∈ Finset.range 81, stT284 (i+1)) + stT284 82 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 81
    simpa using h
  have hprev := st284_p81
  have hstep := st284_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p83 : ((14195495417953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT284 (i+1))
      = (∑ i ∈ Finset.range 82, stT284 (i+1)) + stT284 83 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 82
    simpa using h
  have hprev := st284_p82
  have hstep := st284_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p84 : ((13841793499383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT284 (i+1))
      = (∑ i ∈ Finset.range 83, stT284 (i+1)) + stT284 84 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 83
    simpa using h
  have hprev := st284_p83
  have hstep := st284_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p85 : ((14408084885323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT284 (i+1))
      = (∑ i ∈ Finset.range 84, stT284 (i+1)) + stT284 85 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 84
    simpa using h
  have hprev := st284_p84
  have hstep := st284_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p86 : ((13689278988819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT284 (i+1))
      = (∑ i ∈ Finset.range 85, stT284 (i+1)) + stT284 86 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 85
    simpa using h
  have hprev := st284_p85
  have hstep := st284_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p87 : ((14509444668819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT284 (i+1))
      = (∑ i ∈ Finset.range 86, stT284 (i+1)) + stT284 87 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 86
    simpa using h
  have hprev := st284_p86
  have hstep := st284_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p88 : ((2725358458163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT284 (i+1))
      = (∑ i ∈ Finset.range 87, stT284 (i+1)) + stT284 88 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 87
    simpa using h
  have hprev := st284_p87
  have hstep := st284_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p89 : ((3635585609907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT284 (i+1))
      = (∑ i ∈ Finset.range 88, stT284 (i+1)) + stT284 89 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 88
    simpa using h
  have hprev := st284_p88
  have hstep := st284_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p90 : ((1361534564901/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT284 (i+1))
      = (∑ i ∈ Finset.range 89, stT284 (i+1)) + stT284 90 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 89
    simpa using h
  have hprev := st284_p89
  have hstep := st284_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p91 : ((290706079263/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT284 (i+1))
      = (∑ i ∈ Finset.range 90, stT284 (i+1)) + stT284 91 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 90
    simpa using h
  have hprev := st284_p90
  have hstep := st284_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p92 : ((6819827260301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT284 (i+1))
      = (∑ i ∈ Finset.range 91, stT284 (i+1)) + stT284 92 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 91
    simpa using h
  have hprev := st284_p91
  have hstep := st284_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p93 : ((7245091234911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT284 (i+1))
      = (∑ i ∈ Finset.range 92, stT284 (i+1)) + stT284 93 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 92
    simpa using h
  have hprev := st284_p92
  have hstep := st284_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p94 : ((1713734711237/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT284 (i+1))
      = (∑ i ∈ Finset.range 93, stT284 (i+1)) + stT284 94 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 93
    simpa using h
  have hprev := st284_p93
  have hstep := st284_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p95 : ((7193748072877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT284 (i+1))
      = (∑ i ∈ Finset.range 94, stT284 (i+1)) + stT284 95 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 94
    simpa using h
  have hprev := st284_p94
  have hstep := st284_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p96 : ((1731325829209/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT284 (i+1))
      = (∑ i ∈ Finset.range 95, stT284 (i+1)) + stT284 96 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 95
    simpa using h
  have hprev := st284_p95
  have hstep := st284_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p97 : ((7101841018183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT284 (i+1))
      = (∑ i ∈ Finset.range 96, stT284 (i+1)) + stT284 97 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 96
    simpa using h
  have hprev := st284_p96
  have hstep := st284_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p98 : ((703805894761/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT284 (i+1))
      = (∑ i ∈ Finset.range 97, stT284 (i+1)) + stT284 98 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 97
    simpa using h
  have hprev := st284_p97
  have hstep := st284_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p99 : ((6971972171401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT284 (i+1))
      = (∑ i ∈ Finset.range 98, stT284 (i+1)) + stT284 99 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 98
    simpa using h
  have hprev := st284_p98
  have hstep := st284_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p100 : ((3587695483991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT284 (i+1))
      = (∑ i ∈ Finset.range 99, stT284 (i+1)) + stT284 100 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 99
    simpa using h
  have hprev := st284_p99
  have hstep := st284_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p101 : ((1368358607109/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT284 (i+1))
      = (∑ i ∈ Finset.range 100, stT284 (i+1)) + stT284 101 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 100
    simpa using h
  have hprev := st284_p100
  have hstep := st284_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p102 : ((7277984473749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT284 (i+1))
      = (∑ i ∈ Finset.range 101, stT284 (i+1)) + stT284 102 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 101
    simpa using h
  have hprev := st284_p101
  have hstep := st284_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p103 : ((6788909030939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT284 (i+1))
      = (∑ i ∈ Finset.range 102, stT284 (i+1)) + stT284 103 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 102
    simpa using h
  have hprev := st284_p102
  have hstep := st284_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p104 : ((7260594486599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT284 (i+1))
      = (∑ i ∈ Finset.range 103, stT284 (i+1)) + stT284 104 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 103
    simpa using h
  have hprev := st284_p103
  have hstep := st284_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p105 : ((13774586648059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT284 (i+1))
      = (∑ i ∈ Finset.range 104, stT284 (i+1)) + stT284 105 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 104
    simpa using h
  have hprev := st284_p104
  have hstep := st284_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p106 : ((7085848745797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT284 (i+1))
      = (∑ i ∈ Finset.range 105, stT284 (i+1)) + stT284 106 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 105
    simpa using h
  have hprev := st284_p105
  have hstep := st284_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p107 : ((7111689115709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT284 (i+1))
      = (∑ i ∈ Finset.range 106, stT284 (i+1)) + stT284 107 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 106
    simpa using h
  have hprev := st284_p106
  have hstep := st284_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p108 : ((3429406219831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT284 (i+1))
      = (∑ i ∈ Finset.range 107, stT284 (i+1)) + stT284 108 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 107
    simpa using h
  have hprev := st284_p107
  have hstep := st284_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p109 : ((7280551368983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT284 (i+1))
      = (∑ i ∈ Finset.range 108, stT284 (i+1)) + stT284 109 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 108
    simpa using h
  have hprev := st284_p108
  have hstep := st284_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p110 : ((13608962191147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT284 (i+1))
      = (∑ i ∈ Finset.range 109, stT284 (i+1)) + stT284 110 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 109
    simpa using h
  have hprev := st284_p109
  have hstep := st284_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p111 : ((14378064108247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT284 (i+1))
      = (∑ i ∈ Finset.range 110, stT284 (i+1)) + stT284 111 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 110
    simpa using h
  have hprev := st284_p110
  have hstep := st284_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p112 : ((14053672983911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT284 (i+1))
      = (∑ i ∈ Finset.range 111, stT284 (i+1)) + stT284 112 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 111
    simpa using h
  have hprev := st284_p111
  have hstep := st284_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p113 : ((13805569108813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT284 (i+1))
      = (∑ i ∈ Finset.range 112, stT284 (i+1)) + stT284 113 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 112
    simpa using h
  have hprev := st284_p112
  have hstep := st284_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p114 : ((14542708333063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT284 (i+1))
      = (∑ i ∈ Finset.range 113, stT284 (i+1)) + stT284 114 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 113
    simpa using h
  have hprev := st284_p113
  have hstep := st284_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p115 : ((13610115677593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT284 (i+1))
      = (∑ i ∈ Finset.range 114, stT284 (i+1)) + stT284 115 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 114
    simpa using h
  have hprev := st284_p114
  have hstep := st284_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p116 : ((14332377157993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT284 (i+1))
      = (∑ i ∈ Finset.range 115, stT284 (i+1)) + stT284 116 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 115
    simpa using h
  have hprev := st284_p115
  have hstep := st284_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p117 : ((1415978853781/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT284 (i+1))
      = (∑ i ∈ Finset.range 116, stT284 (i+1)) + stT284 117 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 116
    simpa using h
  have hprev := st284_p116
  have hstep := st284_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p118 : ((171110854957/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT284 (i+1))
      = (∑ i ∈ Finset.range 117, stT284 (i+1)) + stT284 118 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 117
    simpa using h
  have hprev := st284_p117
  have hstep := st284_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p119 : ((7283735588887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT284 (i+1))
      = (∑ i ∈ Finset.range 118, stT284 (i+1)) + stT284 119 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 118
    simpa using h
  have hprev := st284_p118
  have hstep := st284_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p120 : ((13756006452809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT284 (i+1))
      = (∑ i ∈ Finset.range 119, stT284 (i+1)) + stT284 120 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 119
    simpa using h
  have hprev := st284_p119
  have hstep := st284_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p121 : ((14033257084649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT284 (i+1))
      = (∑ i ∈ Finset.range 120, stT284 (i+1)) + stT284 121 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 120
    simpa using h
  have hprev := st284_p120
  have hstep := st284_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p122 : ((14462532106199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT284 (i+1))
      = (∑ i ∈ Finset.range 121, stT284 (i+1)) + stT284 122 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 121
    simpa using h
  have hprev := st284_p121
  have hstep := st284_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p123 : ((13589582099039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT284 (i+1))
      = (∑ i ∈ Finset.range 122, stT284 (i+1)) + stT284 123 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 122
    simpa using h
  have hprev := st284_p122
  have hstep := st284_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p124 : ((14336437994303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT284 (i+1))
      = (∑ i ∈ Finset.range 123, stT284 (i+1)) + stT284 124 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 123
    simpa using h
  have hprev := st284_p123
  have hstep := st284_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p125 : ((14227649611091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT284 (i+1))
      = (∑ i ∈ Finset.range 124, stT284 (i+1)) + stT284 125 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 124
    simpa using h
  have hprev := st284_p124
  have hstep := st284_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p126 : ((13615893840617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT284 (i+1))
      = (∑ i ∈ Finset.range 125, stT284 (i+1)) + stT284 126 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 125
    simpa using h
  have hprev := st284_p125
  have hstep := st284_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p127 : ((14500139657837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT284 (i+1))
      = (∑ i ∈ Finset.range 126, stT284 (i+1)) + stT284 127 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 126
    simpa using h
  have hprev := st284_p126
  have hstep := st284_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p128 : ((14020009449617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT284 (i+1))
      = (∑ i ∈ Finset.range 127, stT284 (i+1)) + stT284 128 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 127
    simpa using h
  have hprev := st284_p127
  have hstep := st284_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p129 : ((2742394620371/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT284 (i+1))
      = (∑ i ∈ Finset.range 128, stT284 (i+1)) + stT284 129 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 128
    simpa using h
  have hprev := st284_p128
  have hstep := st284_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p130 : ((2911668568487/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT284 (i+1))
      = (∑ i ∈ Finset.range 129, stT284 (i+1)) + stT284 130 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 129
    simpa using h
  have hprev := st284_p129
  have hstep := st284_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p131 : ((2778046222679/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT284 (i+1))
      = (∑ i ∈ Finset.range 130, stT284 (i+1)) + stT284 131 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 130
    simpa using h
  have hprev := st284_p130
  have hstep := st284_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p132 : ((13793309816689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT284 (i+1))
      = (∑ i ∈ Finset.range 131, stT284 (i+1)) + stT284 132 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 131
    simpa using h
  have hprev := st284_p131
  have hstep := st284_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p133 : ((7284882586033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT284 (i+1))
      = (∑ i ∈ Finset.range 132, stT284 (i+1)) + stT284 133 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 132
    simpa using h
  have hprev := st284_p132
  have hstep := st284_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p134 : ((13834623883363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT284 (i+1))
      = (∑ i ∈ Finset.range 133, stT284 (i+1)) + stT284 134 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 133
    simpa using h
  have hprev := st284_p133
  have hstep := st284_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p135 : ((6911934949589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT284 (i+1))
      = (∑ i ∈ Finset.range 134, stT284 (i+1)) + stT284 135 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 134
    simpa using h
  have hprev := st284_p134
  have hstep := st284_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p136 : ((7285499195659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT284 (i+1))
      = (∑ i ∈ Finset.range 135, stT284 (i+1)) + stT284 136 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 135
    simpa using h
  have hprev := st284_p135
  have hstep := st284_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p137 : ((6920879705851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT284 (i+1))
      = (∑ i ∈ Finset.range 136, stT284 (i+1)) + stT284 137 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 136
    simpa using h
  have hprev := st284_p136
  have hstep := st284_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p138 : ((13796092027423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT284 (i+1))
      = (∑ i ∈ Finset.range 137, stT284 (i+1)) + stT284 138 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 137
    simpa using h
  have hprev := st284_p137
  have hstep := st284_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p139 : ((14568320551083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT284 (i+1))
      = (∑ i ∈ Finset.range 138, stT284 (i+1)) + stT284 139 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 138
    simpa using h
  have hprev := st284_p138
  have hstep := st284_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p140 : ((13910823767283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT284 (i+1))
      = (∑ i ∈ Finset.range 139, stT284 (i+1)) + stT284 140 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 139
    simpa using h
  have hprev := st284_p139
  have hstep := st284_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p141 : ((13719570205931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT284 (i+1))
      = (∑ i ∈ Finset.range 140, stT284 (i+1)) + stT284 141 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 140
    simpa using h
  have hprev := st284_p140
  have hstep := st284_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p142 : ((14540702100983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT284 (i+1))
      = (∑ i ∈ Finset.range 141, stT284 (i+1)) + stT284 142 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 141
    simpa using h
  have hprev := st284_p141
  have hstep := st284_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p143 : ((7024146477039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT284 (i+1))
      = (∑ i ∈ Finset.range 142, stT284 (i+1)) + stT284 143 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 142
    simpa using h
  have hprev := st284_p142
  have hstep := st284_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p144 : ((6812382140961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT284 (i+1))
      = (∑ i ∈ Finset.range 143, stT284 (i+1)) + stT284 144 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 143
    simpa using h
  have hprev := st284_p143
  have hstep := st284_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p145 : ((3611798816457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT284 (i+1))
      = (∑ i ∈ Finset.range 144, stT284 (i+1)) + stT284 145 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 144
    simpa using h
  have hprev := st284_p144
  have hstep := st284_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p146 : ((3562051419797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT284 (i+1))
      = (∑ i ∈ Finset.range 145, stT284 (i+1)) + stT284 146 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 145
    simpa using h
  have hprev := st284_p145
  have hstep := st284_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p147 : ((1696539065947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT284 (i+1))
      = (∑ i ∈ Finset.range 146, stT284 (i+1)) + stT284 147 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 146
    simpa using h
  have hprev := st284_p146
  have hstep := st284_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p148 : ((3562000775873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT284 (i+1))
      = (∑ i ∈ Finset.range 147, stT284 (i+1)) + stT284 148 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 147
    simpa using h
  have hprev := st284_p147
  have hstep := st284_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p149 : ((14461690498301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT284 (i+1))
      = (∑ i ∈ Finset.range 148, stT284 (i+1)) + stT284 149 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 148
    simpa using h
  have hprev := st284_p148
  have hstep := st284_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p150 : ((2729365625059/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT284 (i+1))
      = (∑ i ∈ Finset.range 149, stT284 (i+1)) + stT284 150 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 149
    simpa using h
  have hprev := st284_p149
  have hstep := st284_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p151 : ((13949449027491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT284 (i+1))
      = (∑ i ∈ Finset.range 150, stT284 (i+1)) + stT284 151 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 150
    simpa using h
  have hprev := st284_p150
  have hstep := st284_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p152 : ((14577541088439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT284 (i+1))
      = (∑ i ∈ Finset.range 151, stT284 (i+1)) + stT284 152 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 151
    simpa using h
  have hprev := st284_p151
  have hstep := st284_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p153 : ((13907652081921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT284 (i+1))
      = (∑ i ∈ Finset.range 152, stT284 (i+1)) + stT284 153 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 152
    simpa using h
  have hprev := st284_p152
  have hstep := st284_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p154 : ((6828963364199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT284 (i+1))
      = (∑ i ∈ Finset.range 153, stT284 (i+1)) + stT284 154 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 153
    simpa using h
  have hprev := st284_p153
  have hstep := st284_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p155 : ((1446015616259/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT284 (i+1))
      = (∑ i ∈ Finset.range 154, stT284 (i+1)) + stT284 155 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 154
    simpa using h
  have hprev := st284_p154
  have hstep := st284_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p156 : ((14294749336477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT284 (i+1))
      = (∑ i ∈ Finset.range 155, stT284 (i+1)) + stT284 156 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 155
    simpa using h
  have hprev := st284_p155
  have hstep := st284_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p157 : ((54306774811/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT284 (i+1))
      = (∑ i ∈ Finset.range 156, stT284 (i+1)) + stT284 157 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 156
    simpa using h
  have hprev := st284_p156
  have hstep := st284_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p158 : ((175993671029/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT284 (i+1))
      = (∑ i ∈ Finset.range 157, stT284 (i+1)) + stT284 158 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 157
    simpa using h
  have hprev := st284_p157
  have hstep := st284_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p159 : ((7284545030789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT284 (i+1))
      = (∑ i ∈ Finset.range 158, stT284 (i+1)) + stT284 159 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 158
    simpa using h
  have hprev := st284_p158
  have hstep := st284_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p160 : ((1732391118811/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT284 (i+1))
      = (∑ i ∈ Finset.range 159, stT284 (i+1)) + stT284 160 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 159
    simpa using h
  have hprev := st284_p159
  have hstep := st284_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p161 : ((13658673705749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT284 (i+1))
      = (∑ i ∈ Finset.range 160, stT284 (i+1)) + stT284 161 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 160
    simpa using h
  have hprev := st284_p160
  have hstep := st284_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p162 : ((14442381163727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT284 (i+1))
      = (∑ i ∈ Finset.range 161, stT284 (i+1)) + stT284 162 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 161
    simpa using h
  have hprev := st284_p161
  have hstep := st284_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p163 : ((7179104010181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT284 (i+1))
      = (∑ i ∈ Finset.range 162, stT284 (i+1)) + stT284 163 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 162
    simpa using h
  have hprev := st284_p162
  have hstep := st284_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p164 : ((13606342837629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT284 (i+1))
      = (∑ i ∈ Finset.range 163, stT284 (i+1)) + stT284 164 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 163
    simpa using h
  have hprev := st284_p163
  have hstep := st284_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p165 : ((13930384845149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT284 (i+1))
      = (∑ i ∈ Finset.range 164, stT284 (i+1)) + stT284 165 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 164
    simpa using h
  have hprev := st284_p164
  have hstep := st284_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p166 : ((14581801330949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT284 (i+1))
      = (∑ i ∈ Finset.range 165, stT284 (i+1)) + stT284 166 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 165
    simpa using h
  have hprev := st284_p165
  have hstep := st284_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p167 : ((14077572195781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT284 (i+1))
      = (∑ i ∈ Finset.range 166, stT284 (i+1)) + stT284 167 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 166
    simpa using h
  have hprev := st284_p166
  have hstep := st284_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p168 : ((13559259360011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT284 (i+1))
      = (∑ i ∈ Finset.range 167, stT284 (i+1)) + stT284 168 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 167
    simpa using h
  have hprev := st284_p167
  have hstep := st284_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p169 : ((14184424119461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT284 (i+1))
      = (∑ i ∈ Finset.range 168, stT284 (i+1)) + stT284 169 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 168
    simpa using h
  have hprev := st284_p168
  have hstep := st284_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p170 : ((14563511415741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT284 (i+1))
      = (∑ i ∈ Finset.range 169, stT284 (i+1)) + stT284 170 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 169
    simpa using h
  have hprev := st284_p169
  have hstep := st284_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p171 : ((13865871124701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT284 (i+1))
      = (∑ i ∈ Finset.range 170, stT284 (i+1)) + stT284 171 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 170
    simpa using h
  have hprev := st284_p170
  have hstep := st284_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p172 : ((13613643015259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT284 (i+1))
      = (∑ i ∈ Finset.range 171, stT284 (i+1)) + stT284 172 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 171
    simpa using h
  have hprev := st284_p171
  have hstep := st284_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p173 : ((14348012940749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT284 (i+1))
      = (∑ i ∈ Finset.range 172, stT284 (i+1)) + stT284 173 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 172
    simpa using h
  have hprev := st284_p172
  have hstep := st284_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p174 : ((14495102147101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT284 (i+1))
      = (∑ i ∈ Finset.range 173, stT284 (i+1)) + stT284 174 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 173
    simpa using h
  have hprev := st284_p173
  have hstep := st284_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p175 : ((3436587673239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT284 (i+1))
      = (∑ i ∈ Finset.range 174, stT284 (i+1)) + stT284 175 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 174
    simpa using h
  have hprev := st284_p174
  have hstep := st284_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p176 : ((2735524375503/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT284 (i+1))
      = (∑ i ∈ Finset.range 175, stT284 (i+1)) + stT284 176 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 175
    simpa using h
  have hprev := st284_p175
  have hstep := st284_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p177 : ((2885628081703/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT284 (i+1))
      = (∑ i ∈ Finset.range 176, stT284 (i+1)) + stT284 177 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 176
    simpa using h
  have hprev := st284_p176
  have hstep := st284_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p178 : ((577833473417/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT284 (i+1))
      = (∑ i ∈ Finset.range 177, stT284 (i+1)) + stT284 178 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 177
    simpa using h
  have hprev := st284_p177
  have hstep := st284_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p179 : ((13698330576441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT284 (i+1))
      = (∑ i ∈ Finset.range 178, stT284 (i+1)) + stT284 179 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 178
    simpa using h
  have hprev := st284_p178
  have hstep := st284_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p180 : ((856509627191/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT284 (i+1))
      = (∑ i ∈ Finset.range 179, stT284 (i+1)) + stT284 180 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 179
    simpa using h
  have hprev := st284_p179
  have hstep := st284_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p181 : ((7223666412243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT284 (i+1))
      = (∑ i ∈ Finset.range 180, stT284 (i+1)) + stT284 181 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 180
    simpa using h
  have hprev := st284_p180
  have hstep := st284_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p182 : ((112843363287/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT284 (i+1))
      = (∑ i ∈ Finset.range 181, stT284 (i+1)) + stT284 182 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 181
    simpa using h
  have hprev := st284_p181
  have hstep := st284_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p183 : ((85654331363/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT284 (i+1))
      = (∑ i ∈ Finset.range 182, stT284 (i+1)) + stT284 183 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 182
    simpa using h
  have hprev := st284_p182
  have hstep := st284_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p184 : ((1368010042969/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT284 (i+1))
      = (∑ i ∈ Finset.range 183, stT284 (i+1)) + stT284 184 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 183
    simpa using h
  have hprev := st284_p183
  have hstep := st284_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p185 : ((7206849949873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT284 (i+1))
      = (∑ i ∈ Finset.range 184, stT284 (i+1)) + stT284 185 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 184
    simpa using h
  have hprev := st284_p184
  have hstep := st284_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p186 : ((7245077889833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT284 (i+1))
      = (∑ i ∈ Finset.range 185, stT284 (i+1)) + stT284 186 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 185
    simpa using h
  have hprev := st284_p185
  have hstep := st284_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p187 : ((2753460385143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT284 (i+1))
      = (∑ i ∈ Finset.range 186, stT284 (i+1)) + stT284 187 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 186
    simpa using h
  have hprev := st284_p186
  have hstep := st284_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p188 : ((2723225779673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT284 (i+1))
      = (∑ i ∈ Finset.range 187, stT284 (i+1)) + stT284 188 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 187
    simpa using h
  have hprev := st284_p187
  have hstep := st284_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p189 : ((2863308385817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT284 (i+1))
      = (∑ i ∈ Finset.range 188, stT284 (i+1)) + stT284 189 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 188
    simpa using h
  have hprev := st284_p188
  have hstep := st284_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p190 : ((582471998921/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT284 (i+1))
      = (∑ i ∈ Finset.range 189, stT284 (i+1)) + stT284 190 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 189
    simpa using h
  have hprev := st284_p189
  have hstep := st284_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p191 : ((556100121383/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT284 (i+1))
      = (∑ i ∈ Finset.range 190, stT284 (i+1)) + stT284 191 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 190
    simpa using h
  have hprev := st284_p190
  have hstep := st284_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p192 : ((2709682806851/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT284 (i+1))
      = (∑ i ∈ Finset.range 191, stT284 (i+1)) + stT284 192 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 191
    simpa using h
  have hprev := st284_p191
  have hstep := st284_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p193 : ((565563423419/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT284 (i+1))
      = (∑ i ∈ Finset.range 192, stT284 (i+1)) + stT284 193 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 192
    simpa using h
  have hprev := st284_p192
  have hstep := st284_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p194 : ((14607692464327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT284 (i+1))
      = (∑ i ∈ Finset.range 193, stT284 (i+1)) + stT284 194 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 193
    simpa using h
  have hprev := st284_p193
  have hstep := st284_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p195 : ((7060035212861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT284 (i+1))
      = (∑ i ∈ Finset.range 194, stT284 (i+1)) + stT284 195 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 194
    simpa using h
  have hprev := st284_p194
  have hstep := st284_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p196 : ((6771582954623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT284 (i+1))
      = (∑ i ∈ Finset.range 195, stT284 (i+1)) + stT284 196 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 195
    simpa using h
  have hprev := st284_p195
  have hstep := st284_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p197 : ((6943987157693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT284 (i+1))
      = (∑ i ∈ Finset.range 196, stT284 (i+1)) + stT284 197 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 196
    simpa using h
  have hprev := st284_p196
  have hstep := st284_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p198 : ((581993695433/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT284 (i+1))
      = (∑ i ∈ Finset.range 197, stT284 (i+1)) + stT284 198 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 197
    simpa using h
  have hprev := st284_p197
  have hstep := st284_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p199 : ((14386498959857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT284 (i+1))
      = (∑ i ∈ Finset.range 198, stT284 (i+1)) + stT284 199 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 198
    simpa using h
  have hprev := st284_p198
  have hstep := st284_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p200 : ((547275352197/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT284 (i+1))
      = (∑ i ∈ Finset.range 199, stT284 (i+1)) + stT284 200 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 199
    simpa using h
  have hprev := st284_p199
  have hstep := st284_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p201 : ((13633074567071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT284 (i+1))
      = (∑ i ∈ Finset.range 200, stT284 (i+1)) + stT284 201 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 200
    simpa using h
  have hprev := st284_p200
  have hstep := st284_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p202 : ((2863597087589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT284 (i+1))
      = (∑ i ∈ Finset.range 201, stT284 (i+1)) + stT284 202 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 201
    simpa using h
  have hprev := st284_p201
  have hstep := st284_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p203 : ((2918099479337/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT284 (i+1))
      = (∑ i ∈ Finset.range 202, stT284 (i+1)) + stT284 203 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 202
    simpa using h
  have hprev := st284_p202
  have hstep := st284_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p204 : ((7001262643077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT284 (i+1))
      = (∑ i ∈ Finset.range 203, stT284 (i+1)) + stT284 204 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 203
    simpa using h
  have hprev := st284_p203
  have hstep := st284_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p205 : ((13523259838661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT284 (i+1))
      = (∑ i ∈ Finset.range 204, stT284 (i+1)) + stT284 205 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 204
    simpa using h
  have hprev := st284_p204
  have hstep := st284_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p206 : ((13931344717557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT284 (i+1))
      = (∑ i ∈ Finset.range 205, stT284 (i+1)) + stT284 206 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 205
    simpa using h
  have hprev := st284_p205
  have hstep := st284_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p207 : ((2912587801089/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT284 (i+1))
      = (∑ i ∈ Finset.range 206, stT284 (i+1)) + stT284 207 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 206
    simpa using h
  have hprev := st284_p206
  have hstep := st284_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p208 : ((14405964226053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT284 (i+1))
      = (∑ i ∈ Finset.range 207, stT284 (i+1)) + stT284 208 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 207
    simpa using h
  have hprev := st284_p207
  have hstep := st284_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p209 : ((13714312863833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT284 (i+1))
      = (∑ i ∈ Finset.range 208, stT284 (i+1)) + stT284 209 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 208
    simpa using h
  have hprev := st284_p208
  have hstep := st284_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p210 : ((13580135740727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT284 (i+1))
      = (∑ i ∈ Finset.range 209, stT284 (i+1)) + stT284 210 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 209
    simpa using h
  have hprev := st284_p209
  have hstep := st284_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p211 : ((14209442920943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT284 (i+1))
      = (∑ i ∈ Finset.range 210, stT284 (i+1)) + stT284 211 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 210
    simpa using h
  have hprev := st284_p210
  have hstep := st284_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p212 : ((14622403227503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT284 (i+1))
      = (∑ i ∈ Finset.range 211, stT284 (i+1)) + stT284 212 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 211
    simpa using h
  have hprev := st284_p211
  have hstep := st284_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p213 : ((3546381851573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT284 (i+1))
      = (∑ i ∈ Finset.range 212, stT284 (i+1)) + stT284 213 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 212
    simpa using h
  have hprev := st284_p212
  have hstep := st284_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p214 : ((678506387131/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT284 (i+1))
      = (∑ i ∈ Finset.range 213, stT284 (i+1)) + stT284 214 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 213
    simpa using h
  have hprev := st284_p213
  have hstep := st284_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p215 : ((6854075185167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT284 (i+1))
      = (∑ i ∈ Finset.range 214, stT284 (i+1)) + stT284 215 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 214
    simpa using h
  have hprev := st284_p214
  have hstep := st284_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p216 : ((449614921019/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT284 (i+1))
      = (∑ i ∈ Finset.range 215, stT284 (i+1)) + stT284 216 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 215
    simpa using h
  have hprev := st284_p215
  have hstep := st284_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p217 : ((3648360639073/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT284 (i+1))
      = (∑ i ∈ Finset.range 216, stT284 (i+1)) + stT284 217 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 216
    simpa using h
  have hprev := st284_p216
  have hstep := st284_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p218 : ((7012153131029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT284 (i+1))
      = (∑ i ∈ Finset.range 217, stT284 (i+1)) + stT284 218 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 217
    simpa using h
  have hprev := st284_p217
  have hstep := st284_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p219 : ((844949971261/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT284 (i+1))
      = (∑ i ∈ Finset.range 218, stT284 (i+1)) + stT284 219 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 218
    simpa using h
  have hprev := st284_p218
  have hstep := st284_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p220 : ((13812217886959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT284 (i+1))
      = (∑ i ∈ Finset.range 219, stT284 (i+1)) + stT284 220 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 219
    simpa using h
  have hprev := st284_p219
  have hstep := st284_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p221 : ((14475473151631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT284 (i+1))
      = (∑ i ∈ Finset.range 220, stT284 (i+1)) + stT284 221 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 220
    simpa using h
  have hprev := st284_p220
  have hstep := st284_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p222 : ((14556901824487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT284 (i+1))
      = (∑ i ∈ Finset.range 221, stT284 (i+1)) + stT284 222 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 221
    simpa using h
  have hprev := st284_p221
  have hstep := st284_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p223 : ((13944328102937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT284 (i+1))
      = (∑ i ∈ Finset.range 222, stT284 (i+1)) + stT284 223 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 222
    simpa using h
  have hprev := st284_p222
  have hstep := st284_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p224 : ((13505598810071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT284 (i+1))
      = (∑ i ∈ Finset.range 223, stT284 (i+1)) + stT284 224 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 223
    simpa using h
  have hprev := st284_p223
  have hstep := st284_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p225 : ((13853331795671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT284 (i+1))
      = (∑ i ∈ Finset.range 224, stT284 (i+1)) + stT284 225 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 224
    simpa using h
  have hprev := st284_p224
  have hstep := st284_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p226 : ((14499789380081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT284 (i+1))
      = (∑ i ∈ Finset.range 225, stT284 (i+1)) + stT284 226 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 225
    simpa using h
  have hprev := st284_p225
  have hstep := st284_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p227 : ((3638102500811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT284 (i+1))
      = (∑ i ∈ Finset.range 226, stT284 (i+1)) + stT284 227 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 226
    simpa using h
  have hprev := st284_p226
  have hstep := st284_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p228 : ((13942849522439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT284 (i+1))
      = (∑ i ∈ Finset.range 227, stT284 (i+1)) + stT284 228 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 227
    simpa using h
  have hprev := st284_p227
  have hstep := st284_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p229 : ((6751098785563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT284 (i+1))
      = (∑ i ∈ Finset.range 228, stT284 (i+1)) + stT284 229 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 228
    simpa using h
  have hprev := st284_p228
  have hstep := st284_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p230 : ((6911340324093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT284 (i+1))
      = (∑ i ∈ Finset.range 229, stT284 (i+1)) + stT284 230 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 229
    simpa using h
  have hprev := st284_p229
  have hstep := st284_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p231 : ((56528106699/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT284 (i+1))
      = (∑ i ∈ Finset.range 230, stT284 (i+1)) + stT284 231 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 230
    simpa using h
  have hprev := st284_p230
  have hstep := st284_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p232 : ((227898029703/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT284 (i+1))
      = (∑ i ∈ Finset.range 231, stT284 (i+1)) + stT284 232 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 231
    simpa using h
  have hprev := st284_p231
  have hstep := st284_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p233 : ((3504574852251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT284 (i+1))
      = (∑ i ∈ Finset.range 232, stT284 (i+1)) + stT284 233 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 232
    simpa using h
  have hprev := st284_p232
  have hstep := st284_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p234 : ((6757432472289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT284 (i+1))
      = (∑ i ∈ Finset.range 233, stT284 (i+1)) + stT284 234 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 233
    simpa using h
  have hprev := st284_p233
  have hstep := st284_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p235 : ((6863781832293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT284 (i+1))
      = (∑ i ∈ Finset.range 234, stT284 (i+1)) + stT284 235 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 234
    simpa using h
  have hprev := st284_p234
  have hstep := st284_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p236 : ((7189048133989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT284 (i+1))
      = (∑ i ∈ Finset.range 235, stT284 (i+1)) + stT284 236 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 235
    simpa using h
  have hprev := st284_p235
  have hstep := st284_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p237 : ((14632520103467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT284 (i+1))
      = (∑ i ∈ Finset.range 236, stT284 (i+1)) + stT284 237 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 236
    simpa using h
  have hprev := st284_p236
  have hstep := st284_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p238 : ((2834107337203/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT284 (i+1))
      = (∑ i ∈ Finset.range 237, stT284 (i+1)) + stT284 238 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 237
    simpa using h
  have hprev := st284_p237
  have hstep := st284_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p239 : ((2715612728967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT284 (i+1))
      = (∑ i ∈ Finset.range 238, stT284 (i+1)) + stT284 239 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 238
    simpa using h
  have hprev := st284_p238
  have hstep := st284_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p240 : ((13596212438487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT284 (i+1))
      = (∑ i ∈ Finset.range 239, stT284 (i+1)) + stT284 240 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 239
    simpa using h
  have hprev := st284_p239
  have hstep := st284_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p241 : ((14198623908907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT284 (i+1))
      = (∑ i ∈ Finset.range 240, stT284 (i+1)) + stT284 241 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 240
    simpa using h
  have hprev := st284_p240
  have hstep := st284_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p242 : ((14639787591867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT284 (i+1))
      = (∑ i ∈ Finset.range 241, stT284 (i+1)) + stT284 242 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 241
    simpa using h
  have hprev := st284_p241
  have hstep := st284_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p243 : ((14381301178927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT284 (i+1))
      = (∑ i ∈ Finset.range 242, stT284 (i+1)) + stT284 243 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 242
    simpa using h
  have hprev := st284_p242
  have hstep := st284_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p244 : ((13741085450047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT284 (i+1))
      = (∑ i ∈ Finset.range 243, stT284 (i+1)) + stT284 244 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 243
    simpa using h
  have hprev := st284_p243
  have hstep := st284_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p245 : ((13492761626671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT284 (i+1))
      = (∑ i ∈ Finset.range 244, stT284 (i+1)) + stT284 245 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 244
    simpa using h
  have hprev := st284_p244
  have hstep := st284_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p246 : ((13930889189623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT284 (i+1))
      = (∑ i ∈ Finset.range 245, stT284 (i+1)) + stT284 246 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 245
    simpa using h
  have hprev := st284_p245
  have hstep := st284_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p247 : ((14530882731683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT284 (i+1))
      = (∑ i ∈ Finset.range 246, stT284 (i+1)) + stT284 247 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 246
    simpa using h
  have hprev := st284_p246
  have hstep := st284_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p248 : ((14584257656683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT284 (i+1))
      = (∑ i ∈ Finset.range 247, stT284 (i+1)) + stT284 248 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 247
    simpa using h
  have hprev := st284_p247
  have hstep := st284_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p249 : ((7015899191029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT284 (i+1))
      = (∑ i ∈ Finset.range 248, stT284 (i+1)) + stT284 249 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 248
    simpa using h
  have hprev := st284_p248
  have hstep := st284_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p250 : ((1351924149317/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT284 (i+1))
      = (∑ i ∈ Finset.range 249, stT284 (i+1)) + stT284 250 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 249
    simpa using h
  have hprev := st284_p249
  have hstep := st284_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p251 : ((6818890494379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT284 (i+1))
      = (∑ i ∈ Finset.range 250, stT284 (i+1)) + stT284 251 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 250
    simpa using h
  have hprev := st284_p250
  have hstep := st284_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p252 : ((7123836889099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT284 (i+1))
      = (∑ i ∈ Finset.range 251, stT284 (i+1)) + stT284 252 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 251
    simpa using h
  have hprev := st284_p251
  have hstep := st284_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p253 : ((915747098051/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT284 (i+1))
      = (∑ i ∈ Finset.range 252, stT284 (i+1)) + stT284 253 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 252
    simpa using h
  have hprev := st284_p252
  have hstep := st284_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p254 : ((899690812739/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT284 (i+1))
      = (∑ i ∈ Finset.range 253, stT284 (i+1)) + stT284 254 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 253
    simpa using h
  have hprev := st284_p253
  have hstep := st284_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p255 : ((6884554902537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT284 (i+1))
      = (∑ i ∈ Finset.range 254, stT284 (i+1)) + stT284 255 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 254
    simpa using h
  have hprev := st284_p254
  have hstep := st284_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p256 : ((1347358183223/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT284 (i+1))
      = (∑ i ∈ Finset.range 255, stT284 (i+1)) + stT284 256 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 255
    simpa using h
  have hprev := st284_p255
  have hstep := st284_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p257 : ((172916422409/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT284 (i+1))
      = (∑ i ∈ Finset.range 256, stT284 (i+1)) + stT284 257 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 256
    simpa using h
  have hprev := st284_p256
  have hstep := st284_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p258 : ((3612279141841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT284 (i+1))
      = (∑ i ∈ Finset.range 257, stT284 (i+1)) + stT284 258 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 257
    simpa using h
  have hprev := st284_p257
  have hstep := st284_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p259 : ((14647594874713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT284 (i+1))
      = (∑ i ∈ Finset.range 258, stT284 (i+1)) + stT284 259 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 258
    simpa using h
  have hprev := st284_p258
  have hstep := st284_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p260 : ((14216165250047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT284 (i+1))
      = (∑ i ∈ Finset.range 259, stT284 (i+1)) + stT284 260 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 259
    simpa using h
  have hprev := st284_p259
  have hstep := st284_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p261 : ((6811360714051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT284 (i+1))
      = (∑ i ∈ Finset.range 260, stT284 (i+1)) + stT284 261 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 260
    simpa using h
  have hprev := st284_p260
  have hstep := st284_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p262 : ((6751132335187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT284 (i+1))
      = (∑ i ∈ Finset.range 261, stT284 (i+1)) + stT284 262 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 261
    simpa using h
  have hprev := st284_p261
  have hstep := st284_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p263 : ((34949296997/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT284 (i+1))
      = (∑ i ∈ Finset.range 262, stT284 (i+1)) + stT284 263 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 262
    simpa using h
  have hprev := st284_p262
  have hstep := st284_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p264 : ((14548246587093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT284 (i+1))
      = (∑ i ∈ Finset.range 263, stT284 (i+1)) + stT284 264 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 263
    simpa using h
  have hprev := st284_p263
  have hstep := st284_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p265 : ((3653034698937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT284 (i+1))
      = (∑ i ∈ Finset.range 264, stT284 (i+1)) + stT284 265 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 264
    simpa using h
  have hprev := st284_p264
  have hstep := st284_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p266 : ((3526977713487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT284 (i+1))
      = (∑ i ∈ Finset.range 265, stT284 (i+1)) + stT284 266 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 265
    simpa using h
  have hprev := st284_p265
  have hstep := st284_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p267 : ((1694942498793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT284 (i+1))
      = (∑ i ∈ Finset.range 266, stT284 (i+1)) + stT284 267 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 266
    simpa using h
  have hprev := st284_p266
  have hstep := st284_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p268 : ((1691204490813/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT284 (i+1))
      = (∑ i ∈ Finset.range 267, stT284 (i+1)) + stT284 268 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 267
    simpa using h
  have hprev := st284_p267
  have hstep := st284_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p269 : ((3511381242781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT284 (i+1))
      = (∑ i ∈ Finset.range 268, stT284 (i+1)) + stT284 269 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 268
    simpa using h
  have hprev := st284_p268
  have hstep := st284_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p270 : ((3645474542821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT284 (i+1))
      = (∑ i ∈ Finset.range 269, stT284 (i+1)) + stT284 270 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 269
    simpa using h
  have hprev := st284_p269
  have hstep := st284_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p271 : ((3649863868013/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT284 (i+1))
      = (∑ i ∈ Finset.range 270, stT284 (i+1)) + stT284 271 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 270
    simpa using h
  have hprev := st284_p270
  have hstep := st284_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p272 : ((440114855711/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT284 (i+1))
      = (∑ i ∈ Finset.range 271, stT284 (i+1)) + stT284 272 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 271
    simpa using h
  have hprev := st284_p271
  have hstep := st284_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p273 : ((3307898569/2441406250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT284 (i+1))
      = (∑ i ∈ Finset.range 272, stT284 (i+1)) + stT284 273 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 272
    simpa using h
  have hprev := st284_p272
  have hstep := st284_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p274 : ((13522543941089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT284 (i+1))
      = (∑ i ∈ Finset.range 273, stT284 (i+1)) + stT284 274 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 273
    simpa using h
  have hprev := st284_p273
  have hstep := st284_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p275 : ((2805366388597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT284 (i+1))
      = (∑ i ∈ Finset.range 274, stT284 (i+1)) + stT284 275 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 274
    simpa using h
  have hprev := st284_p274
  have hstep := st284_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p276 : ((14568595731719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT284 (i+1))
      = (∑ i ∈ Finset.range 275, stT284 (i+1)) + stT284 276 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 275
    simpa using h
  have hprev := st284_p275
  have hstep := st284_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p277 : ((14624310515967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT284 (i+1))
      = (∑ i ∈ Finset.range 276, stT284 (i+1)) + stT284 277 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 276
    simpa using h
  have hprev := st284_p276
  have hstep := st284_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p278 : ((3535826298193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT284 (i+1))
      = (∑ i ∈ Finset.range 277, stT284 (i+1)) + stT284 278 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 277
    simpa using h
  have hprev := st284_p277
  have hstep := st284_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p279 : ((13587133413307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT284 (i+1))
      = (∑ i ∈ Finset.range 278, stT284 (i+1)) + stT284 279 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 278
    simpa using h
  have hprev := st284_p278
  have hstep := st284_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p280 : ((13482860352877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT284 (i+1))
      = (∑ i ∈ Finset.range 279, stT284 (i+1)) + stT284 280 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 279
    simpa using h
  have hprev := st284_p279
  have hstep := st284_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p281 : ((3481473209167/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT284 (i+1))
      = (∑ i ∈ Finset.range 280, stT284 (i+1)) + stT284 281 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 280
    simpa using h
  have hprev := st284_p280
  have hstep := st284_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p282 : ((14498905837891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT284 (i+1))
      = (∑ i ∈ Finset.range 281, stT284 (i+1)) + stT284 282 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 281
    simpa using h
  have hprev := st284_p281
  have hstep := st284_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p283 : ((14668956122113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT284 (i+1))
      = (∑ i ∈ Finset.range 282, stT284 (i+1)) + stT284 283 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 282
    simpa using h
  have hprev := st284_p282
  have hstep := st284_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p284 : ((14281405339321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT284 (i+1))
      = (∑ i ∈ Finset.range 283, stT284 (i+1)) + stT284 284 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 283
    simpa using h
  have hprev := st284_p283
  have hstep := st284_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p285 : ((13694709718177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT284 (i+1))
      = (∑ i ∈ Finset.range 284, stT284 (i+1)) + stT284 285 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 284
    simpa using h
  have hprev := st284_p284
  have hstep := st284_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p286 : ((1344437203781/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT284 (i+1))
      = (∑ i ∈ Finset.range 285, stT284 (i+1)) + stT284 286 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 285
    simpa using h
  have hprev := st284_p285
  have hstep := st284_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p287 : ((13754973768043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT284 (i+1))
      = (∑ i ∈ Finset.range 286, stT284 (i+1)) + stT284 287 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 286
    simpa using h
  have hprev := st284_p286
  have hstep := st284_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p288 : ((3585981620057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT284 (i+1))
      = (∑ i ∈ Finset.range 287, stT284 (i+1)) + stT284 288 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 287
    simpa using h
  have hprev := st284_p287
  have hstep := st284_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p289 : ((114713486801/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT284 (i+1))
      = (∑ i ∈ Finset.range 288, stT284 (i+1)) + stT284 289 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 288
    simpa using h
  have hprev := st284_p288
  have hstep := st284_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p290 : ((14473180467363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT284 (i+1))
      = (∑ i ∈ Finset.range 289, stT284 (i+1)) + stT284 290 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 289
    simpa using h
  have hprev := st284_p289
  have hstep := st284_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p291 : ((13901990538027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT284 (i+1))
      = (∑ i ∈ Finset.range 290, stT284 (i+1)) + stT284 291 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 290
    simpa using h
  have hprev := st284_p290
  have hstep := st284_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p292 : ((13472540626163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT284 (i+1))
      = (∑ i ∈ Finset.range 291, stT284 (i+1)) + stT284 292 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 291
    simpa using h
  have hprev := st284_p291
  have hstep := st284_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p293 : ((13558122715721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT284 (i+1))
      = (∑ i ∈ Finset.range 292, stT284 (i+1)) + stT284 293 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 292
    simpa using h
  have hprev := st284_p292
  have hstep := st284_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p294 : ((14081668897577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT284 (i+1))
      = (∑ i ∈ Finset.range 293, stT284 (i+1)) + stT284 294 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 293
    simpa using h
  have hprev := st284_p293
  have hstep := st284_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p295 : ((14590225841249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT284 (i+1))
      = (∑ i ∈ Finset.range 294, stT284 (i+1)) + stT284 295 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 294
    simpa using h
  have hprev := st284_p294
  have hstep := st284_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p296 : ((14649015158759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT284 (i+1))
      = (∑ i ∈ Finset.range 295, stT284 (i+1)) + stT284 296 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 295
    simpa using h
  have hprev := st284_p295
  have hstep := st284_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p297 : ((14210566816287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT284 (i+1))
      = (∑ i ∈ Finset.range 296, stT284 (i+1)) + stT284 297 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 296
    simpa using h
  have hprev := st284_p296
  have hstep := st284_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p298 : ((6823930186851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT284 (i+1))
      = (∑ i ∈ Finset.range 297, stT284 (i+1)) + stT284 298 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 297
    simpa using h
  have hprev := st284_p297
  have hstep := st284_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p299 : ((13433762955867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT284 (i+1))
      = (∑ i ∈ Finset.range 298, stT284 (i+1)) + stT284 299 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 298
    simpa using h
  have hprev := st284_p298
  have hstep := st284_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p300 : ((13744834517067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT284 (i+1))
      = (∑ i ∈ Finset.range 299, stT284 (i+1)) + stT284 300 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 299
    simpa using h
  have hprev := st284_p299
  have hstep := st284_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p301 : ((14320244654067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT284 (i+1))
      = (∑ i ∈ Finset.range 300, stT284 (i+1)) + stT284 301 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 300
    simpa using h
  have hprev := st284_p300
  have hstep := st284_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p302 : ((917776874057/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT284 (i+1))
      = (∑ i ∈ Finset.range 301, stT284 (i+1)) + stT284 302 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 301
    simpa using h
  have hprev := st284_p301
  have hstep := st284_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p303 : ((14540327890967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT284 (i+1))
      = (∑ i ∈ Finset.range 302, stT284 (i+1)) + stT284 303 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 302
    simpa using h
  have hprev := st284_p302
  have hstep := st284_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p304 : ((14007985842707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT284 (i+1))
      = (∑ i ∈ Finset.range 303, stT284 (i+1)) + stT284 304 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 303
    simpa using h
  have hprev := st284_p303
  have hstep := st284_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p305 : ((13520089122381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT284 (i+1))
      = (∑ i ∈ Finset.range 304, stT284 (i+1)) + stT284 305 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 304
    simpa using h
  have hprev := st284_p304
  have hstep := st284_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p306 : ((13468596096069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT284 (i+1))
      = (∑ i ∈ Finset.range 305, stT284 (i+1)) + stT284 306 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 305
    simpa using h
  have hprev := st284_p305
  have hstep := st284_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p307 : ((13892186194769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT284 (i+1))
      = (∑ i ∈ Finset.range 306, stT284 (i+1)) + stT284 307 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 306
    simpa using h
  have hprev := st284_p306
  have hstep := st284_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p308 : ((14451757399859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT284 (i+1))
      = (∑ i ∈ Finset.range 307, stT284 (i+1)) + stT284 308 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 307
    simpa using h
  have hprev := st284_p307
  have hstep := st284_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p309 : ((14704741749139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT284 (i+1))
      = (∑ i ∈ Finset.range 308, stT284 (i+1)) + stT284 309 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 308
    simpa using h
  have hprev := st284_p308
  have hstep := st284_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p310 : ((14454247788659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT284 (i+1))
      = (∑ i ∈ Finset.range 309, stT284 (i+1)) + stT284 310 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 309
    simpa using h
  have hprev := st284_p309
  have hstep := st284_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p311 : ((13898387078651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT284 (i+1))
      = (∑ i ∈ Finset.range 310, stT284 (i+1)) + stT284 311 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 310
    simpa using h
  have hprev := st284_p310
  have hstep := st284_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p312 : ((33674536901/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT284 (i+1))
      = (∑ i ∈ Finset.range 311, stT284 (i+1)) + stT284 312 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 311
    simpa using h
  have hprev := st284_p311
  have hstep := st284_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p313 : ((3374534363891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT284 (i+1))
      = (∑ i ∈ Finset.range 312, stT284 (i+1)) + stT284 313 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 312
    simpa using h
  have hprev := st284_p312
  have hstep := st284_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p314 : ((872445102713/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT284 (i+1))
      = (∑ i ∈ Finset.range 313, stT284 (i+1)) + stT284 314 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 313
    simpa using h
  have hprev := st284_p313
  have hstep := st284_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p315 : ((906202243781/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT284 (i+1))
      = (∑ i ∈ Finset.range 314, stT284 (i+1)) + stT284 315 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 314
    simpa using h
  have hprev := st284_p314
  have hstep := st284_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p316 : ((14709017748427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT284 (i+1))
      = (∑ i ∈ Finset.range 315, stT284 (i+1)) + stT284 316 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 315
    simpa using h
  have hprev := st284_p315
  have hstep := st284_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p317 : ((14432307248563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT284 (i+1))
      = (∑ i ∈ Finset.range 316, stT284 (i+1)) + stT284 317 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 316
    simpa using h
  have hprev := st284_p316
  have hstep := st284_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p318 : ((13878754761711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT284 (i+1))
      = (∑ i ∈ Finset.range 317, stT284 (i+1)) + stT284 318 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 317
    simpa using h
  have hprev := st284_p317
  have hstep := st284_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p319 : ((13461642315213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT284 (i+1))
      = (∑ i ∈ Finset.range 318, stT284 (i+1)) + stT284 319 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 318
    simpa using h
  have hprev := st284_p318
  have hstep := st284_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p320 : ((13488687509293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT284 (i+1))
      = (∑ i ∈ Finset.range 319, stT284 (i+1)) + stT284 320 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 319
    simpa using h
  have hprev := st284_p319
  have hstep := st284_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p321 : ((1742199255541/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT284 (i+1))
      = (∑ i ∈ Finset.range 320, stT284 (i+1)) + stT284 321 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 320
    simpa using h
  have hprev := st284_p320
  have hstep := st284_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p322 : ((7238938368581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT284 (i+1))
      = (∑ i ∈ Finset.range 321, stT284 (i+1)) + stT284 322 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 321
    simpa using h
  have hprev := st284_p321
  have hstep := st284_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p323 : ((7358158414291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT284 (i+1))
      = (∑ i ∈ Finset.range 322, stT284 (i+1)) + stT284 323 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 322
    simpa using h
  have hprev := st284_p322
  have hstep := st284_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p324 : ((1448218219683/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT284 (i+1))
      = (∑ i ∈ Finset.range 323, stT284 (i+1)) + stT284 324 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 323
    simpa using h
  have hprev := st284_p323
  have hstep := st284_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p325 : ((13946168518819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT284 (i+1))
      = (∑ i ∈ Finset.range 324, stT284 (i+1)) + stT284 325 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 324
    simpa using h
  have hprev := st284_p324
  have hstep := st284_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p326 : ((674636312509/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT284 (i+1))
      = (∑ i ∈ Finset.range 325, stT284 (i+1)) + stT284 326 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 325
    simpa using h
  have hprev := st284_p325
  have hstep := st284_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p327 : ((3360858465977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT284 (i+1))
      = (∑ i ∈ Finset.range 326, stT284 (i+1)) + stT284 327 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 326
    simpa using h
  have hprev := st284_p326
  have hstep := st284_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p328 : ((13830929364153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT284 (i+1))
      = (∑ i ∈ Finset.range 327, stT284 (i+1)) + stT284 328 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 327
    simpa using h
  have hprev := st284_p327
  have hstep := st284_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p329 : ((2876154428499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT284 (i+1))
      = (∑ i ∈ Finset.range 328, stT284 (i+1)) + stT284 329 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 328
    simpa using h
  have hprev := st284_p328
  have hstep := st284_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p330 : ((588327489267/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT284 (i+1))
      = (∑ i ∈ Finset.range 329, stT284 (i+1)) + stT284 330 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 329
    simpa using h
  have hprev := st284_p329
  have hstep := st284_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p331 : ((583480477693/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT284 (i+1))
      = (∑ i ∈ Finset.range 330, stT284 (i+1)) + stT284 331 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 330
    simpa using h
  have hprev := st284_p330
  have hstep := st284_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p332 : ((14103205042911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT284 (i+1))
      = (∑ i ∈ Finset.range 331, stT284 (i+1)) + stT284 332 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 331
    simpa using h
  have hprev := st284_p331
  have hstep := st284_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p333 : ((6795356658269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT284 (i+1))
      = (∑ i ∈ Finset.range 332, stT284 (i+1)) + stT284 333 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 332
    simpa using h
  have hprev := st284_p332
  have hstep := st284_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p334 : ((6699722057753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT284 (i+1))
      = (∑ i ∈ Finset.range 333, stT284 (i+1)) + stT284 334 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 333
    simpa using h
  have hprev := st284_p333
  have hstep := st284_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p335 : ((1365750976051/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT284 (i+1))
      = (∑ i ∈ Finset.range 334, stT284 (i+1)) + stT284 335 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 334
    simpa using h
  have hprev := st284_p334
  have hstep := st284_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p336 : ((7094175947627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT284 (i+1))
      = (∑ i ∈ Finset.range 335, stT284 (i+1)) + stT284 336 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 335
    simpa using h
  have hprev := st284_p335
  have hstep := st284_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p337 : ((7317121955477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT284 (i+1))
      = (∑ i ∈ Finset.range 336, stT284 (i+1)) + stT284 337 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 336
    simpa using h
  have hprev := st284_p336
  have hstep := st284_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p338 : ((1469800423897/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT284 (i+1))
      = (∑ i ∈ Finset.range 337, stT284 (i+1)) + stT284 338 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 337
    simpa using h
  have hprev := st284_p337
  have hstep := st284_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p339 : ((7169619007331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT284 (i+1))
      = (∑ i ∈ Finset.range 338, stT284 (i+1)) + stT284 339 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 338
    simpa using h
  have hprev := st284_p338
  have hstep := st284_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p340 : ((13796901795103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT284 (i+1))
      = (∑ i ∈ Finset.range 339, stT284 (i+1)) + stT284 340 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 339
    simpa using h
  have hprev := st284_p339
  have hstep := st284_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p341 : ((6713940725997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT284 (i+1))
      = (∑ i ∈ Finset.range 340, stT284 (i+1)) + stT284 341 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 340
    simpa using h
  have hprev := st284_p340
  have hstep := st284_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p342 : ((6736071510123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT284 (i+1))
      = (∑ i ∈ Finset.range 341, stT284 (i+1)) + stT284 342 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 341
    simpa using h
  have hprev := st284_p341
  have hstep := st284_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p343 : ((13898791821831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT284 (i+1))
      = (∑ i ∈ Finset.range 342, stT284 (i+1)) + stT284 343 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 342
    simpa using h
  have hprev := st284_p342
  have hstep := st284_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p344 : ((14430379581681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT284 (i+1))
      = (∑ i ∈ Finset.range 343, stT284 (i+1)) + stT284 344 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 343
    simpa using h
  have hprev := st284_p343
  have hstep := st284_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p345 : ((2944999993967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT284 (i+1))
      = (∑ i ∈ Finset.range 344, stT284 (i+1)) + stT284 345 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 344
    simpa using h
  have hprev := st284_p344
  have hstep := st284_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p346 : ((14595691692527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT284 (i+1))
      = (∑ i ∈ Finset.range 345, stT284 (i+1)) + stT284 346 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 345
    simpa using h
  have hprev := st284_p345
  have hstep := st284_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p347 : ((7063347934069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT284 (i+1))
      = (∑ i ∈ Finset.range 346, stT284 (i+1)) + stT284 347 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 346
    simpa using h
  have hprev := st284_p346
  have hstep := st284_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p348 : ((2723191475261/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT284 (i+1))
      = (∑ i ∈ Finset.range 347, stT284 (i+1)) + stT284 348 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 347
    simpa using h
  have hprev := st284_p347
  have hstep := st284_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p349 : ((2676907798341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT284 (i+1))
      = (∑ i ∈ Finset.range 348, stT284 (i+1)) + stT284 349 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 348
    simpa using h
  have hprev := st284_p348
  have hstep := st284_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p350 : ((13575593724687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT284 (i+1))
      = (∑ i ∈ Finset.range 349, stT284 (i+1)) + stT284 350 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 349
    simpa using h
  have hprev := st284_p349
  have hstep := st284_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p351 : ((14068221111567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT284 (i+1))
      = (∑ i ∈ Finset.range 350, stT284 (i+1)) + stT284 351 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 350
    simpa using h
  have hprev := st284_p350
  have hstep := st284_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p352 : ((2911268472273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT284 (i+1))
      = (∑ i ∈ Finset.range 351, stT284 (i+1)) + stT284 352 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 351
    simpa using h
  have hprev := st284_p351
  have hstep := st284_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p353 : ((14739824057191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT284 (i+1))
      = (∑ i ∈ Finset.range 352, stT284 (i+1)) + stT284 353 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 352
    simpa using h
  have hprev := st284_p352
  have hstep := st284_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p354 : ((14507943418591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT284 (i+1))
      = (∑ i ∈ Finset.range 353, stT284 (i+1)) + stT284 354 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 353
    simpa using h
  have hprev := st284_p353
  have hstep := st284_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p355 : ((14003812095871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT284 (i+1))
      = (∑ i ∈ Finset.range 354, stT284 (i+1)) + stT284 355 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 354
    simpa using h
  have hprev := st284_p354
  have hstep := st284_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p356 : ((13533787782711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT284 (i+1))
      = (∑ i ∈ Finset.range 355, stT284 (i+1)) + stT284 356 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 355
    simpa using h
  have hprev := st284_p355
  have hstep := st284_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p357 : ((133805557083/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT284 (i+1))
      = (∑ i ∈ Finset.range 356, stT284 (i+1)) + stT284 357 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 356
    simpa using h
  have hprev := st284_p356
  have hstep := st284_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p358 : ((681712433673/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT284 (i+1))
      = (∑ i ∈ Finset.range 357, stT284 (i+1)) + stT284 358 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 357
    simpa using h
  have hprev := st284_p357
  have hstep := st284_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p359 : ((7070868341013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT284 (i+1))
      = (∑ i ∈ Finset.range 358, stT284 (i+1)) + stT284 359 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 358
    simpa using h
  have hprev := st284_p358
  have hstep := st284_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p360 : ((7300549717353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT284 (i+1))
      = (∑ i ∈ Finset.range 359, stT284 (i+1)) + stT284 360 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 359
    simpa using h
  have hprev := st284_p359
  have hstep := st284_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p361 : ((460682936263/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT284 (i+1))
      = (∑ i ∈ Finset.range 360, stT284 (i+1)) + stT284 361 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 360
    simpa using h
  have hprev := st284_p360
  have hstep := st284_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p362 : ((7241511726327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT284 (i+1))
      = (∑ i ∈ Finset.range 361, stT284 (i+1)) + stT284 362 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 361
    simpa using h
  have hprev := st284_p361
  have hstep := st284_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p363 : ((279549635919/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT284 (i+1))
      = (∑ i ∈ Finset.range 362, stT284 (i+1)) + stT284 363 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 362
    simpa using h
  have hprev := st284_p362
  have hstep := st284_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p364 : ((2703932246091/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT284 (i+1))
      = (∑ i ∈ Finset.range 363, stT284 (i+1)) + stT284 364 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 363
    simpa using h
  have hprev := st284_p363
  have hstep := st284_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p365 : ((13373491937911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT284 (i+1))
      = (∑ i ∈ Finset.range 364, stT284 (i+1)) + stT284 365 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 364
    simpa using h
  have hprev := st284_p364
  have hstep := st284_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p366 : ((13621332367987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT284 (i+1))
      = (∑ i ∈ Finset.range 365, stT284 (i+1)) + stT284 366 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 365
    simpa using h
  have hprev := st284_p365
  have hstep := st284_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p367 : ((7059841802231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT284 (i+1))
      = (∑ i ∈ Finset.range 366, stT284 (i+1)) + stT284 367 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 366
    simpa using h
  have hprev := st284_p366
  have hstep := st284_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p368 : ((7292078885519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT284 (i+1))
      = (∑ i ∈ Finset.range 367, stT284 (i+1)) + stT284 368 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 367
    simpa using h
  have hprev := st284_p367
  have hstep := st284_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p369 : ((737617790239/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT284 (i+1))
      = (∑ i ∈ Finset.range 368, stT284 (i+1)) + stT284 369 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 368
    simpa using h
  have hprev := st284_p368
  have hstep := st284_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p370 : ((1816387267351/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT284 (i+1))
      = (∑ i ∈ Finset.range 369, stT284 (i+1)) + stT284 370 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 369
    simpa using h
  have hprev := st284_p369
  have hstep := st284_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p371 : ((7023014910629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT284 (i+1))
      = (∑ i ∈ Finset.range 370, stT284 (i+1)) + stT284 371 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 370
    simpa using h
  have hprev := st284_p370
  have hstep := st284_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p372 : ((6784184903703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT284 (i+1))
      = (∑ i ∈ Finset.range 371, stT284 (i+1)) + stT284 372 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 371
    simpa using h
  have hprev := st284_p371
  have hstep := st284_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p373 : ((13362558591059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT284 (i+1))
      = (∑ i ∈ Finset.range 372, stT284 (i+1)) + stT284 373 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 372
    simpa using h
  have hprev := st284_p372
  have hstep := st284_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p374 : ((13540633012119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT284 (i+1))
      = (∑ i ∈ Finset.range 373, stT284 (i+1)) + stT284 374 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 373
    simpa using h
  have hprev := st284_p373
  have hstep := st284_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p375 : ((1750391126207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT284 (i+1))
      = (∑ i ∈ Finset.range 374, stT284 (i+1)) + stT284 375 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 374
    simpa using h
  have hprev := st284_p374
  have hstep := st284_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p376 : ((7248211837253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT284 (i+1))
      = (∑ i ∈ Finset.range 375, stT284 (i+1)) + stT284 376 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 375
    simpa using h
  have hprev := st284_p375
  have hstep := st284_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p377 : ((3688172191627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT284 (i+1))
      = (∑ i ∈ Finset.range 376, stT284 (i+1)) + stT284 377 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 376
    simpa using h
  have hprev := st284_p376
  have hstep := st284_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p378 : ((14634677964053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT284 (i+1))
      = (∑ i ∈ Finset.range 377, stT284 (i+1)) + stT284 378 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 377
    simpa using h
  have hprev := st284_p377
  have hstep := st284_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p379 : ((2841505437487/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT284 (i+1))
      = (∑ i ∈ Finset.range 378, stT284 (i+1)) + stT284 379 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 378
    simpa using h
  have hprev := st284_p378
  have hstep := st284_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p380 : ((548039234193/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT284 (i+1))
      = (∑ i ∈ Finset.range 379, stT284 (i+1)) + stT284 380 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 379
    simpa using h
  have hprev := st284_p379
  have hstep := st284_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p381 : ((13384752779193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT284 (i+1))
      = (∑ i ∈ Finset.range 380, stT284 (i+1)) + stT284 381 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 380
    simpa using h
  have hprev := st284_p380
  have hstep := st284_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p382 : ((2685049675701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT284 (i+1))
      = (∑ i ∈ Finset.range 381, stT284 (i+1)) + stT284 382 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 381
    simpa using h
  have hprev := st284_p381
  have hstep := st284_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p383 : ((13799419241097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT284 (i+1))
      = (∑ i ∈ Finset.range 382, stT284 (i+1)) + stT284 383 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 382
    simpa using h
  have hprev := st284_p382
  have hstep := st284_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p384 : ((14309659838937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT284 (i+1))
      = (∑ i ∈ Finset.range 383, stT284 (i+1)) + stT284 384 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 383
    simpa using h
  have hprev := st284_p383
  have hstep := st284_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p385 : ((918082681283/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT284 (i+1))
      = (∑ i ∈ Finset.range 384, stT284 (i+1)) + stT284 385 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 384
    simpa using h
  have hprev := st284_p384
  have hstep := st284_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p386 : ((184275876721/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT284 (i+1))
      = (∑ i ∈ Finset.range 385, stT284 (i+1)) + stT284 386 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 385
    simpa using h
  have hprev := st284_p385
  have hstep := st284_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p387 : ((14442180935801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT284 (i+1))
      = (∑ i ∈ Finset.range 386, stT284 (i+1)) + stT284 387 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 386
    simpa using h
  have hprev := st284_p386
  have hstep := st284_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p388 : ((13945294500627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT284 (i+1))
      = (∑ i ∈ Finset.range 387, stT284 (i+1)) + stT284 388 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 387
    simpa using h
  have hprev := st284_p387
  have hstep := st284_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p389 : ((13506255890349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT284 (i+1))
      = (∑ i ∈ Finset.range 388, stT284 (i+1)) + stT284 389 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 388
    simpa using h
  have hprev := st284_p388
  have hstep := st284_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p390 : ((13348052230359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT284 (i+1))
      = (∑ i ∈ Finset.range 389, stT284 (i+1)) + stT284 390 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 389
    simpa using h
  have hprev := st284_p389
  have hstep := st284_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p391 : ((2709882627609/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT284 (i+1))
      = (∑ i ∈ Finset.range 390, stT284 (i+1)) + stT284 391 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 390
    simpa using h
  have hprev := st284_p390
  have hstep := st284_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p392 : ((14007241298549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT284 (i+1))
      = (∑ i ∈ Finset.range 391, stT284 (i+1)) + stT284 392 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 391
    simpa using h
  have hprev := st284_p391
  have hstep := st284_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p393 : ((905679562183/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT284 (i+1))
      = (∑ i ∈ Finset.range 392, stT284 (i+1)) + stT284 393 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 392
    simpa using h
  have hprev := st284_p392
  have hstep := st284_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p394 : ((922434991389/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT284 (i+1))
      = (∑ i ∈ Finset.range 393, stT284 (i+1)) + stT284 394 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 393
    simpa using h
  have hprev := st284_p393
  have hstep := st284_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p395 : ((14679422629289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT284 (i+1))
      = (∑ i ∈ Finset.range 394, stT284 (i+1)) + stT284 395 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 394
    simpa using h
  have hprev := st284_p394
  have hstep := st284_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p396 : ((3573277158861/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT284 (i+1))
      = (∑ i ∈ Finset.range 395, stT284 (i+1)) + stT284 396 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 395
    simpa using h
  have hprev := st284_p395
  have hstep := st284_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p397 : ((34478239777/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT284 (i+1))
      = (∑ i ∈ Finset.range 396, stT284 (i+1)) + stT284 397 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 396
    simpa using h
  have hprev := st284_p396
  have hstep := st284_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p398 : ((2683992539603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT284 (i+1))
      = (∑ i ∈ Finset.range 397, stT284 (i+1)) + stT284 398 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 397
    simpa using h
  have hprev := st284_p397
  have hstep := st284_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p399 : ((13359259671757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT284 (i+1))
      = (∑ i ∈ Finset.range 398, stT284 (i+1)) + stT284 399 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 398
    simpa using h
  have hprev := st284_p398
  have hstep := st284_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p400 : ((13637152671757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT284 (i+1))
      = (∑ i ∈ Finset.range 399, stT284 (i+1)) + stT284 400 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 399
    simpa using h
  have hprev := st284_p399
  have hstep := st284_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p401 : ((14118086216701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT284 (i+1))
      = (∑ i ∈ Finset.range 400, stT284 (i+1)) + stT284 401 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 400
    simpa using h
  have hprev := st284_p400
  have hstep := st284_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p402 : ((14570323924891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT284 (i+1))
      = (∑ i ∈ Finset.range 401, stT284 (i+1)) + stT284 402 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 401
    simpa using h
  have hprev := st284_p401
  have hstep := st284_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p403 : ((7388992474643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT284 (i+1))
      = (∑ i ∈ Finset.range 402, stT284 (i+1)) + stT284 403 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 402
    simpa using h
  have hprev := st284_p402
  have hstep := st284_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p404 : ((7321723925691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT284 (i+1))
      = (∑ i ∈ Finset.range 403, stT284 (i+1)) + stT284 404 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 403
    simpa using h
  have hprev := st284_p403
  have hstep := st284_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p405 : ((7115939829911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT284 (i+1))
      = (∑ i ∈ Finset.range 404, stT284 (i+1)) + stT284 405 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 404
    simpa using h
  have hprev := st284_p404
  have hstep := st284_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p406 : ((6869146225611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT284 (i+1))
      = (∑ i ∈ Finset.range 405, stT284 (i+1)) + stT284 406 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 405
    simpa using h
  have hprev := st284_p405
  have hstep := st284_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p407 : ((6697168860029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT284 (i+1))
      = (∑ i ∈ Finset.range 406, stT284 (i+1)) + stT284 407 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 406
    simpa using h
  have hprev := st284_p406
  have hstep := st284_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p408 : ((1335975086027/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT284 (i+1))
      = (∑ i ∈ Finset.range 407, stT284 (i+1)) + stT284 408 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 407
    simpa using h
  have hprev := st284_p407
  have hstep := st284_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p409 : ((6824589649057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT284 (i+1))
      = (∑ i ∈ Finset.range 408, stT284 (i+1)) + stT284 409 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 408
    simpa using h
  have hprev := st284_p408
  have hstep := st284_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p410 : ((7063706745121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT284 (i+1))
      = (∑ i ∈ Finset.range 409, stT284 (i+1)) + stT284 410 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 409
    simpa using h
  have hprev := st284_p409
  have hstep := st284_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p411 : ((14573645342981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT284 (i+1))
      = (∑ i ∈ Finset.range 410, stT284 (i+1)) + stT284 411 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 410
    simpa using h
  have hprev := st284_p410
  have hstep := st284_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p412 : ((14783731067173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT284 (i+1))
      = (∑ i ∈ Finset.range 411, stT284 (i+1)) + stT284 412 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 411
    simpa using h
  have hprev := st284_p411
  have hstep := st284_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p413 : ((14662980532381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT284 (i+1))
      = (∑ i ∈ Finset.range 412, stT284 (i+1)) + stT284 413 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 412
    simpa using h
  have hprev := st284_p412
  have hstep := st284_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p414 : ((14267594614121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT284 (i+1))
      = (∑ i ∈ Finset.range 413, stT284 (i+1)) + stT284 414 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 413
    simpa using h
  have hprev := st284_p413
  have hstep := st284_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p415 : ((13777254564983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT284 (i+1))
      = (∑ i ∈ Finset.range 414, stT284 (i+1)) + stT284 415 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 414
    simpa using h
  have hprev := st284_p414
  have hstep := st284_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p416 : ((1341268251233/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT284 (i+1))
      = (∑ i ∈ Finset.range 415, stT284 (i+1)) + stT284 416 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 415
    simpa using h
  have hprev := st284_p415
  have hstep := st284_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p417 : ((13336365727701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT284 (i+1))
      = (∑ i ∈ Finset.range 416, stT284 (i+1)) + stT284 417 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 416
    simpa using h
  have hprev := st284_p416
  have hstep := st284_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p418 : ((13580983877961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT284 (i+1))
      = (∑ i ∈ Finset.range 417, stT284 (i+1)) + stT284 418 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 417
    simpa using h
  have hprev := st284_p417
  have hstep := st284_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p419 : ((3509175429071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT284 (i+1))
      = (∑ i ∈ Finset.range 418, stT284 (i+1)) + stT284 419 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 418
    simpa using h
  have hprev := st284_p418
  have hstep := st284_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p420 : ((3625385113121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT284 (i+1))
      = (∑ i ∈ Finset.range 419, stT284 (i+1)) + stT284 420 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 419
    simpa using h
  have hprev := st284_p419
  have hstep := st284_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p421 : ((7385661326937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT284 (i+1))
      = (∑ i ∈ Finset.range 420, stT284 (i+1)) + stT284 421 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 420
    simpa using h
  have hprev := st284_p420
  have hstep := st284_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p422 : ((460279725549/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT284 (i+1))
      = (∑ i ∈ Finset.range 421, stT284 (i+1)) + stT284 422 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 421
    simpa using h
  have hprev := st284_p421
  have hstep := st284_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p423 : ((7197105617091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT284 (i+1))
      = (∑ i ∈ Finset.range 422, stT284 (i+1)) + stT284 423 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 422
    simpa using h
  have hprev := st284_p422
  have hstep := st284_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p424 : ((13913336762799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT284 (i+1))
      = (∑ i ∈ Finset.range 423, stT284 (i+1)) + stT284 424 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 423
    simpa using h
  have hprev := st284_p423
  have hstep := st284_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p425 : ((13494288397791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT284 (i+1))
      = (∑ i ∈ Finset.range 424, stT284 (i+1)) + stT284 425 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 424
    simpa using h
  have hprev := st284_p424
  have hstep := st284_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p426 : ((13316652038017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT284 (i+1))
      = (∑ i ∈ Finset.range 425, stT284 (i+1)) + stT284 426 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 425
    simpa using h
  have hprev := st284_p425
  have hstep := st284_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p427 : ((6727634177369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT284 (i+1))
      = (∑ i ∈ Finset.range 426, stT284 (i+1)) + stT284 427 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 426
    simpa using h
  have hprev := st284_p426
  have hstep := st284_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p428 : ((1384977591509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT284 (i+1))
      = (∑ i ∈ Finset.range 427, stT284 (i+1)) + stT284 428 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 427
    simpa using h
  have hprev := st284_p427
  have hstep := st284_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p429 : ((1433200055029/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT284 (i+1))
      = (∑ i ∈ Finset.range 428, stT284 (i+1)) + stT284 429 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 428
    simpa using h
  have hprev := st284_p428
  have hstep := st284_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p430 : ((459320172073/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT284 (i+1))
      = (∑ i ∈ Finset.range 429, stT284 (i+1)) + stT284 430 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 429
    simpa using h
  have hprev := st284_p429
  have hstep := st284_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p431 : ((3698823267611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT284 (i+1))
      = (∑ i ∈ Finset.range 430, stT284 (i+1)) + stT284 431 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 430
    simpa using h
  have hprev := st284_p430
  have hstep := st284_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p432 : ((7291860158787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT284 (i+1))
      = (∑ i ∈ Finset.range 431, stT284 (i+1)) + stT284 432 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 431
    simpa using h
  have hprev := st284_p431
  have hstep := st284_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p433 : ((7076413899807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT284 (i+1))
      = (∑ i ∈ Finset.range 432, stT284 (i+1)) + stT284 433 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 432
    simpa using h
  have hprev := st284_p432
  have hstep := st284_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p434 : ((1368197338499/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT284 (i+1))
      = (∑ i ∈ Finset.range 433, stT284 (i+1)) + stT284 434 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 433
    simpa using h
  have hprev := st284_p433
  have hstep := st284_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p435 : ((6682712989043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT284 (i+1))
      = (∑ i ∈ Finset.range 434, stT284 (i+1)) + stT284 435 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 434
    simpa using h
  have hprev := st284_p434
  have hstep := st284_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p436 : ((6666216317399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT284 (i+1))
      = (∑ i ∈ Finset.range 435, stT284 (i+1)) + stT284 436 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 435
    simpa using h
  have hprev := st284_p435
  have hstep := st284_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p437 : ((1359524725149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT284 (i+1))
      = (∑ i ∈ Finset.range 436, stT284 (i+1)) + stT284 437 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 436
    simpa using h
  have hprev := st284_p436
  have hstep := st284_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p438 : ((3511421689477/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT284 (i+1))
      = (∑ i ∈ Finset.range 437, stT284 (i+1)) + stT284 438 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 437
    simpa using h
  have hprev := st284_p437
  have hstep := st284_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p439 : ((7250240577077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT284 (i+1))
      = (∑ i ∈ Finset.range 438, stT284 (i+1)) + stT284 439 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 438
    simpa using h
  have hprev := st284_p438
  have hstep := st284_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p440 : ((14776191377039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT284 (i+1))
      = (∑ i ∈ Finset.range 439, stT284 (i+1)) + stT284 440 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 439
    simpa using h
  have hprev := st284_p439
  have hstep := st284_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p441 : ((14762859933803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT284 (i+1))
      = (∑ i ∈ Finset.range 440, stT284 (i+1)) + stT284 441 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 440
    simpa using h
  have hprev := st284_p440
  have hstep := st284_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p442 : ((14467006768063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT284 (i+1))
      = (∑ i ∈ Finset.range 441, stT284 (i+1)) + stT284 442 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 441
    simpa using h
  have hprev := st284_p441
  have hstep := st284_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p443 : ((7003774116329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT284 (i+1))
      = (∑ i ∈ Finset.range 442, stT284 (i+1)) + stT284 443 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 442
    simpa using h
  have hprev := st284_p442
  have hstep := st284_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p444 : ((6783612172439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT284 (i+1))
      = (∑ i ∈ Finset.range 443, stT284 (i+1)) + stT284 444 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 443
    simpa using h
  have hprev := st284_p443
  have hstep := st284_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p445 : ((3329916181109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT284 (i+1))
      = (∑ i ∈ Finset.range 444, stT284 (i+1)) + stT284 445 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 444
    simpa using h
  have hprev := st284_p444
  have hstep := st284_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p446 : ((13361304037117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT284 (i+1))
      = (∑ i ∈ Finset.range 445, stT284 (i+1)) + stT284 446 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 445
    simpa using h
  have hprev := st284_p445
  have hstep := st284_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p447 : ((6837312265361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT284 (i+1))
      = (∑ i ∈ Finset.range 446, stT284 (i+1)) + stT284 447 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 446
    simpa using h
  have hprev := st284_p446
  have hstep := st284_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p448 : ((7068230316071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT284 (i+1))
      = (∑ i ∈ Finset.range 447, stT284 (i+1)) + stT284 448 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 447
    simpa using h
  have hprev := st284_p447
  have hstep := st284_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p449 : ((14567083102559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT284 (i+1))
      = (∑ i ∈ Finset.range 448, stT284 (i+1)) + stT284 449 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 448
    simpa using h
  have hprev := st284_p448
  have hstep := st284_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p450 : ((2960066666071/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT284 (i+1))
      = (∑ i ∈ Finset.range 449, stT284 (i+1)) + stT284 450 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 449
    simpa using h
  have hprev := st284_p449
  have hstep := st284_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p451 : ((14747328027143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT284 (i+1))
      = (∑ i ∈ Finset.range 450, stT284 (i+1)) + stT284 451 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 450
    simpa using h
  have hprev := st284_p450
  have hstep := st284_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p452 : ((2885905911643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT284 (i+1))
      = (∑ i ∈ Finset.range 451, stT284 (i+1)) + stT284 452 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 451
    simpa using h
  have hprev := st284_p451
  have hstep := st284_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p453 : ((13969142698817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT284 (i+1))
      = (∑ i ∈ Finset.range 452, stT284 (i+1)) + stT284 453 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 452
    simpa using h
  have hprev := st284_p452
  have hstep := st284_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p454 : ((541659167293/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT284 (i+1))
      = (∑ i ∈ Finset.range 453, stT284 (i+1)) + stT284 454 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 453
    simpa using h
  have hprev := st284_p453
  have hstep := st284_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p455 : ((13308027331373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT284 (i+1))
      = (∑ i ∈ Finset.range 454, stT284 (i+1)) + stT284 455 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 454
    simpa using h
  have hprev := st284_p454
  have hstep := st284_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p456 : ((13355828237273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT284 (i+1))
      = (∑ i ∈ Finset.range 455, stT284 (i+1)) + stT284 456 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 455
    simpa using h
  have hprev := st284_p455
  have hstep := st284_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p457 : ((13665792363113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT284 (i+1))
      = (∑ i ∈ Finset.range 456, stT284 (i+1)) + stT284 457 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 456
    simpa using h
  have hprev := st284_p456
  have hstep := st284_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p458 : ((14121176843367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT284 (i+1))
      = (∑ i ∈ Finset.range 457, stT284 (i+1)) + stT284 458 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 457
    simpa using h
  have hprev := st284_p457
  have hstep := st284_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p459 : ((14552152687967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT284 (i+1))
      = (∑ i ∈ Finset.range 458, stT284 (i+1)) + stT284 459 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 458
    simpa using h
  have hprev := st284_p458
  have hstep := st284_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p460 : ((14799336652019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT284 (i+1))
      = (∑ i ∈ Finset.range 459, stT284 (i+1)) + stT284 460 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 459
    simpa using h
  have hprev := st284_p459
  have hstep := st284_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p461 : ((923272973249/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT284 (i+1))
      = (∑ i ∈ Finset.range 460, stT284 (i+1)) + stT284 461 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 460
    simpa using h
  have hprev := st284_p460
  have hstep := st284_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p462 : ((1448224296767/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT284 (i+1))
      = (∑ i ∈ Finset.range 461, stT284 (i+1)) + stT284 462 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 461
    simpa using h
  have hprev := st284_p461
  have hstep := st284_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p463 : ((1403601077343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT284 (i+1))
      = (∑ i ∈ Finset.range 462, stT284 (i+1)) + stT284 463 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 462
    simpa using h
  have hprev := st284_p462
  have hstep := st284_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p464 : ((13596655448069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT284 (i+1))
      = (∑ i ∈ Finset.range 463, stT284 (i+1)) + stT284 464 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 463
    simpa using h
  have hprev := st284_p463
  have hstep := st284_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p465 : ((13323337883727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT284 (i+1))
      = (∑ i ∈ Finset.range 464, stT284 (i+1)) + stT284 465 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 464
    simpa using h
  have hprev := st284_p464
  have hstep := st284_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p466 : ((13313991976377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT284 (i+1))
      = (∑ i ∈ Finset.range 465, stT284 (i+1)) + stT284 466 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 465
    simpa using h
  have hprev := st284_p465
  have hstep := st284_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p467 : ((13570900504017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT284 (i+1))
      = (∑ i ∈ Finset.range 466, stT284 (i+1)) + stT284 467 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 466
    simpa using h
  have hprev := st284_p466
  have hstep := st284_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p468 : ((14001046779267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT284 (i+1))
      = (∑ i ∈ Finset.range 467, stT284 (i+1)) + stT284 468 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 467
    simpa using h
  have hprev := st284_p467
  have hstep := st284_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p469 : ((2890086107739/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT284 (i+1))
      = (∑ i ∈ Finset.range 468, stT284 (i+1)) + stT284 469 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 468
    simpa using h
  have hprev := st284_p468
  have hstep := st284_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p470 : ((1475947024719/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT284 (i+1))
      = (∑ i ∈ Finset.range 469, stT284 (i+1)) + stT284 470 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 469
    simpa using h
  have hprev := st284_p469
  have hstep := st284_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p471 : ((1481947974009/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT284 (i+1))
      = (∑ i ∈ Finset.range 470, stT284 (i+1)) + stT284 471 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 470
    simpa using h
  have hprev := st284_p470
  have hstep := st284_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p472 : ((7305153921117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT284 (i+1))
      = (∑ i ∈ Finset.range 471, stT284 (i+1)) + stT284 472 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 471
    simpa using h
  have hprev := st284_p471
  have hstep := st284_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p473 : ((14206332661047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT284 (i+1))
      = (∑ i ∈ Finset.range 472, stT284 (i+1)) + stT284 473 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 472
    simpa using h
  have hprev := st284_p472
  have hstep := st284_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p474 : ((13749344015219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT284 (i+1))
      = (∑ i ∈ Finset.range 473, stT284 (i+1)) + stT284 474 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 473
    simpa using h
  have hprev := st284_p473
  have hstep := st284_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p475 : ((13398431136947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT284 (i+1))
      = (∑ i ∈ Finset.range 474, stT284 (i+1)) + stT284 475 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 474
    simpa using h
  have hprev := st284_p474
  have hstep := st284_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p476 : ((13274664261497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT284 (i+1))
      = (∑ i ∈ Finset.range 475, stT284 (i+1)) + stT284 476 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 475
    simpa using h
  have hprev := st284_p475
  have hstep := st284_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p477 : ((13419815285517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT284 (i+1))
      = (∑ i ∈ Finset.range 476, stT284 (i+1)) + stT284 477 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 476
    simpa using h
  have hprev := st284_p476
  have hstep := st284_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p478 : ((13782965685513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT284 (i+1))
      = (∑ i ∈ Finset.range 477, stT284 (i+1)) + stT284 478 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 477
    simpa using h
  have hprev := st284_p477
  have hstep := st284_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p479 : ((7119506790317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT284 (i+1))
      = (∑ i ∈ Finset.range 478, stT284 (i+1)) + stT284 479 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 478
    simpa using h
  have hprev := st284_p478
  have hstep := st284_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p480 : ((14632209054949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT284 (i+1))
      = (∑ i ∈ Finset.range 479, stT284 (i+1)) + stT284 480 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 479
    simpa using h
  have hprev := st284_p479
  have hstep := st284_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p481 : ((14829372998349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT284 (i+1))
      = (∑ i ∈ Finset.range 480, stT284 (i+1)) + stT284 481 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 480
    simpa using h
  have hprev := st284_p480
  have hstep := st284_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p482 : ((14764613080973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT284 (i+1))
      = (∑ i ∈ Finset.range 481, stT284 (i+1)) + stT284 482 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 481
    simpa using h
  have hprev := st284_p481
  have hstep := st284_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p483 : ((14460741565757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT284 (i+1))
      = (∑ i ∈ Finset.range 482, stT284 (i+1)) + stT284 483 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 482
    simpa using h
  have hprev := st284_p482
  have hstep := st284_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p484 : ((14020535128419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT284 (i+1))
      = (∑ i ∈ Finset.range 483, stT284 (i+1)) + stT284 484 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 483
    simpa using h
  have hprev := st284_p483
  have hstep := st284_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p485 : ((543659619411/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT284 (i+1))
      = (∑ i ∈ Finset.range 484, stT284 (i+1)) + stT284 485 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 484
    simpa using h
  have hprev := st284_p484
  have hstep := st284_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p486 : ((532649416047/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT284 (i+1))
      = (∑ i ∈ Finset.range 485, stT284 (i+1)) + stT284 486 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 485
    simpa using h
  have hprev := st284_p485
  have hstep := st284_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p487 : ((13285330527231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT284 (i+1))
      = (∑ i ∈ Finset.range 486, stT284 (i+1)) + stT284 487 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 486
    simpa using h
  have hprev := st284_p486
  have hstep := st284_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p488 : ((13508014605059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT284 (i+1))
      = (∑ i ∈ Finset.range 487, stT284 (i+1)) + stT284 488 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 487
    simpa using h
  have hprev := st284_p487
  have hstep := st284_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p489 : ((13910114234329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT284 (i+1))
      = (∑ i ∈ Finset.range 488, stT284 (i+1)) + stT284 489 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 488
    simpa using h
  have hprev := st284_p488
  have hstep := st284_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p490 : ((1435932702721/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT284 (i+1))
      = (∑ i ∈ Finset.range 489, stT284 (i+1)) + stT284 490 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 489
    simpa using h
  have hprev := st284_p489
  have hstep := st284_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p491 : ((7354504350251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT284 (i+1))
      = (∑ i ∈ Finset.range 490, stT284 (i+1)) + stT284 491 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 490
    simpa using h
  have hprev := st284_p490
  have hstep := st284_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p492 : ((3711494708053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT284 (i+1))
      = (∑ i ∈ Finset.range 491, stT284 (i+1)) + stT284 492 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 491
    simpa using h
  have hprev := st284_p491
  have hstep := st284_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p493 : ((7363372204679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT284 (i+1))
      = (∑ i ∈ Finset.range 492, stT284 (i+1)) + stT284 493 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 492
    simpa using h
  have hprev := st284_p492
  have hstep := st284_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p494 : ((1798833665309/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT284 (i+1))
      = (∑ i ∈ Finset.range 493, stT284 (i+1)) + stT284 494 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 493
    simpa using h
  have hprev := st284_p493
  have hstep := st284_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p495 : ((6973209418237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT284 (i+1))
      = (∑ i ∈ Finset.range 494, stT284 (i+1)) + stT284 495 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 494
    simpa using h
  have hprev := st284_p494
  have hstep := st284_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p496 : ((3384096496721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT284 (i+1))
      = (∑ i ∈ Finset.range 495, stT284 (i+1)) + stT284 496 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 495
    simpa using h
  have hprev := st284_p495
  have hstep := st284_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p497 : ((6645487736937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT284 (i+1))
      = (∑ i ∈ Finset.range 496, stT284 (i+1)) + stT284 497 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 496
    simpa using h
  have hprev := st284_p496
  have hstep := st284_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p498 : ((13287371317101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT284 (i+1))
      = (∑ i ∈ Finset.range 497, stT284 (i+1)) + stT284 498 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 497
    simpa using h
  have hprev := st284_p497
  have hstep := st284_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p499 : ((6762892634749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT284 (i+1))
      = (∑ i ∈ Finset.range 498, stT284 (i+1)) + stT284 499 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 498
    simpa using h
  have hprev := st284_p498
  have hstep := st284_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_p500 : ((13930268408987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT284 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT284 (i+1))
      = (∑ i ∈ Finset.range 499, stT284 (i+1)) + stT284 500 := by
    have h := Finset.sum_range_succ (fun i => stT284 (i+1)) 499
    simpa using h
  have hprev := st284_p499
  have hstep := st284_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st284_s500 :
    |Real.sin (((284 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))
      - ((-213181/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -68823/625000) (δ := 3571/250000000) (ψ := -92959/500000) 284 281
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 284`** (evaluated boundary). -/
theorem station_284_sign : hardyG ((((284:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 284 500 (by norm_num) (by norm_num)
    ((-92959/500000 : ℚ) : ℝ)
  have hchain := st284_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT284 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((284 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-92959/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st284_c500
  have hsinb := abs_le.mp st284_s500
  have hbdy_lo : ((107873215051719/3226250000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((284 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-92959/500000 : ℚ) : ℝ))) / 2
          - ((((284:ℕ)):ℝ))
            * Real.sin (((284 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-92959/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((284:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((284:ℝ) * Real.log (500:ℝ) - ((-92959/500000 : ℚ) : ℝ))) / 2
        - ((284:ℝ)) * Real.sin ((284:ℝ) * Real.log (500:ℝ) - ((-92959/500000 : ℚ) : ℝ))
        ≥ ((241212163/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((284:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((241212163/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((241212163/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((241212163/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((284:ℕ)):ℝ))+1) * (((((284:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((631723539657/1000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((13930268408987/10000000000000 : ℚ) : ℝ) + ((107873215051719/3226250000000000 : ℚ) : ℝ)
      - ((631723539657/1000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-92959/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((284:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-92959/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((284:ℕ)):ℝ)))).re
      - Real.sin ((-92959/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((284:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((284:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((284:ℕ)):ℝ))
      = (((((284:ℕ)):ℝ)) * (Real.log ((((284:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((284:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_284
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
  have hθwin : |(((-92959/500000 : ℚ) : ℝ) + ((64:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((284:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((284:ℕ)):ℝ)))
    (φ := ((-92959/500000 : ℚ) : ℝ) + ((64:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-92959/500000 : ℚ) : ℝ) + ((64:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-92959/500000 : ℚ)) : ℝ) - Real.pi) + ((64:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-92959/500000 : ℚ)) : ℝ) - Real.pi) 64).1,
    (cos_sin_shift ((((-92959/500000 : ℚ)) : ℝ) - Real.pi) 64).2]
  exact cos_sin_flip ((-92959/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_284_sign
end AxiomAudit
