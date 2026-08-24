import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 274` (rung-280.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT274 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((274 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-18923/62500 : ℚ) : ℝ))

theorem st274_c1 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((190903/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18923/250000) (δ := 1/1000000000) (ψ := -18923/62500) 274 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t1 : ((190893/200000 : ℚ) : ℝ) ≤ stT274 1 := by
  have hc : ((190893/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190893/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((190893/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c2 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-79033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 216191/500000) (δ := 13817/1000000000) (ψ := -18923/62500) 274 30
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t2 : ((-69878061743/625000000000 : ℚ) : ℝ) ≤ stT274 2 := by
  have hc : ((-39529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69878061743/625000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-39529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c3 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((120459/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337963/5000000) (δ := 13857/1000000000) (ψ := -18923/62500) 274 48
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t3 : ((1390868386061/2500000000000 : ℚ) : ℝ) ≤ stT274 3 := by
  have hc : ((481811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1390868386061/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((481811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c4 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-249973/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781721/1000000) (δ := 1733/125000000) (ψ := -18923/62500) 274 61
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t4 : ((-2499855499971/5000000000000 : ℚ) : ℝ) ≤ stT274 4 := by
  have hc : ((-499971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2499855499971/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-499971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c5 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((104809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3664487/10000000) (δ := 1713/125000000) (ψ := -18923/62500) 274 70
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t5 : ((93699278093/2000000000000 : ℚ) : ℝ) ≤ stT274 5 := by
  have hc : ((104759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93699278093/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((104759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c6 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((201317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22586/78125) (δ := 13841/1000000000) (ψ := -18923/62500) 274 78
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t6 : ((102721370843/625000000000 : ℚ) : ℝ) ≤ stT274 6 := by
  have hc : ((50323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102721370843/625000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((50323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c7 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((415859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294301/2000000) (δ := 857/62500000) (ψ := -18923/62500) 274 85
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t7 : ((196463060387/625000000000 : ℚ) : ℝ) ≤ stT274 7 := by
  have hc : ((207917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196463060387/625000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((207917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c8 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-64477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1062569/2500000) (δ := 1731/125000000) (ψ := -18923/62500) 274 91
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t8 : ((-57012253517/1250000000000 : ℚ) : ℝ) ≤ stT274 8 := by
  have hc : ((-32251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57012253517/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-32251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c9 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((83107/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108737/10000000) (δ := 857/62500000) (ψ := -18923/62500) 274 96
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t9 : ((1108009889199/5000000000000 : ℚ) : ℝ) ≤ stT274 9 := by
  have hc : ((332403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1108009889199/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((332403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c10 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-969147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 903919/1250000) (δ := 3471/250000000) (ψ := -18923/62500) 274 100
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t10 : ((-1532435175383/5000000000000 : ℚ) : ℝ) ≤ stT274 10 := by
  have hc : ((-969197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1532435175383/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-969197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c11 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-148607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6020977/10000000) (δ := 3437/250000000) (ψ := -18923/62500) 274 105
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t11 : ((-224048598669/1000000000000 : ℚ) : ℝ) ≤ stT274 11 := by
  have hc : ((-148617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224048598669/1000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-148617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c12 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-26503/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3228971/5000000) (δ := 6913/500000000) (ψ := -18923/62500) 274 108
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t12 : ((-38256049403/156250000000 : ℚ) : ℝ) ≤ stT274 12 := by
  have hc : ((-424073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38256049403/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-424073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c13 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((815117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544661/10000000) (δ := 6903/500000000) (ψ := -18923/62500) 274 112
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t13 : ((4521176649/20000000000 : ℚ) : ℝ) ≤ stT274 13 := by
  have hc : ((815067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4521176649/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((815067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c14 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((668823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2095429/10000000) (δ := 13727/1000000000) (ψ := -18923/62500) 274 115
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t14 : ((446842686269/2500000000000 : ℚ) : ℝ) ≤ stT274 14 := by
  have hc : ((668773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446842686269/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((668773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c15 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((125467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 557919/2500000) (δ := 13849/1000000000) (ψ := -18923/62500) 274 118
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t15 : ((80982117129/500000000000 : ℚ) : ℝ) ≤ stT274 15 := by
  have hc : ((125457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80982117129/500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((125457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c16 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((240719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341671/5000000) (δ := 13833/1000000000) (ψ := -18923/62500) 274 121
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t16 : ((481413/2000000 : ℚ) : ℝ) ≤ stT274 16 := by
  have hc : ((481413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((481413/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((481413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c17 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-808121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313969/500000) (δ := 3473/250000000) (ψ := -18923/62500) 274 124
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t17 : ((-1960103192047/10000000000000 : ℚ) : ℝ) ≤ stT274 17 := by
  have hc : ((-808171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1960103192047/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-808171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c18 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((834661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1458197/10000000) (δ := 6853/500000000) (ψ := -18923/62500) 274 126
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t18 : ((983598244221/5000000000000 : ℚ) : ℝ) ≤ stT274 18 := by
  have hc : ((834611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((983598244221/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((834611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c19 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-952251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3539151/5000000) (δ := 13883/1000000000) (ψ := -18923/62500) 274 128
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t19 : ((-1092364478779/5000000000000 : ℚ) : ℝ) ≤ stT274 19 := by
  have hc : ((-952301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1092364478779/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-952301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c20 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-38303/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4909677/10000000) (δ := 13761/1000000000) (ψ := -18923/62500) 274 131
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t20 : ((-5353705809/62500000000 : ℚ) : ℝ) ≤ stT274 20 := by
  have hc : ((-9577/25000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5353705809/62500000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-9577/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c21 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((99439/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726079/2500000) (δ := 433/31250000) (ψ := -18923/62500) 274 133
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t21 : ((216966320917/2500000000000 : ℚ) : ℝ) ≤ stT274 21 := by
  have hc : ((198853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216966320917/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((198853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c22 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((555679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2454043/10000000) (δ := 3433/250000000) (ψ := -18923/62500) 274 135
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t22 : ((1184604917403/10000000000000 : ℚ) : ℝ) ≤ stT274 22 := by
  have hc : ((555629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1184604917403/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((555629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c23 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((201219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1710243/5000000) (δ := 2777/200000000) (ψ := -18923/62500) 274 137
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t23 : ((52433291667/1250000000000 : ℚ) : ℝ) ≤ stT274 23 := by
  have hc : ((201169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52433291667/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((201169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c24 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-646081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5683087/10000000) (δ := 1713/125000000) (ψ := -18923/62500) 274 139
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t24 : ((-659454867351/5000000000000 : ℚ) : ℝ) ≤ stT274 24 := by
  have hc : ((-646131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-659454867351/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-646131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c25 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-435691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328601/500000) (δ := 13807/1000000000) (ψ := -18923/62500) 274 140
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t25 : ((-217858108929/1250000000000 : ℚ) : ℝ) ≤ stT274 25 := by
  have hc : ((-108929/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217858108929/1250000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-108929/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c26 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((43143/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2022273/10000000) (δ := 13821/1000000000) (ψ := -18923/62500) 274 142
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t26 : ((676833923159/5000000000000 : ℚ) : ℝ) ≤ stT274 26 := by
  have hc : ((345119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((676833923159/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((345119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c27 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((153567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -885387/2500000) (δ := 2767/200000000) (ψ := -18923/62500) 274 144
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t27 : ((590886933/20000000000 : ℚ) : ℝ) ≤ stT274 27 := by
  have hc : ((153517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((590886933/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((153517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c28 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-639731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5662363/10000000) (δ := 13743/1000000000) (ψ := -18923/62500) 274 145
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t28 : ((-1209072848763/10000000000000 : ℚ) : ℝ) ≤ stT274 28 := by
  have hc : ((-639781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1209072848763/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-639781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c29 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((773527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1716023/10000000) (δ := 13757/1000000000) (ψ := -18923/62500) 274 147
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t29 : ((1436310435581/10000000000000 : ℚ) : ℝ) ≤ stT274 29 := by
  have hc : ((773477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1436310435581/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((773477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c30 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-170157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5798541/10000000) (δ := 13739/1000000000) (ψ := -18923/62500) 274 148
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t30 : ((-310685603269/2500000000000 : ℚ) : ℝ) ≤ stT274 30 := by
  have hc : ((-340339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310685603269/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-340339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c31 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((60683/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197269/625000) (δ := 549/40000000) (ψ := -18923/62500) 274 150
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t31 : ((108971923669/2000000000000 : ℚ) : ℝ) ≤ stT274 31 := by
  have hc : ((60673/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108971923669/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((60673/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c32 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((101337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360449/1250000) (δ := 13817/1000000000) (ψ := -18923/62500) 274 151
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t32 : ((179118006067/2500000000000 : ℚ) : ℝ) ≤ stT274 32 := by
  have hc : ((202649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179118006067/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((202649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c33 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-197443/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1863447/2500000) (δ := 69/5000000) (ψ := -18923/62500) 274 153
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t33 : ((-343721640981/2000000000000 : ℚ) : ℝ) ≤ stT274 33 := by
  have hc : ((-197453/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-343721640981/2000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-197453/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c34 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((466931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2712447/10000000) (δ := 1737/125000000) (ψ := -18923/62500) 274 154
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t34 : ((160138782357/2000000000000 : ℚ) : ℝ) ≤ stT274 34 := by
  have hc : ((466881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160138782357/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((466881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c35 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((104939/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 359007/2500000) (δ := 6907/500000000) (ψ := -18923/62500) 274 155
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t35 : ((177368666787/1250000000000 : ℚ) : ℝ) ≤ stT274 35 := by
  have hc : ((419731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177368666787/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((419731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c36 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-212633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5025131/10000000) (δ := 6861/500000000) (ψ := -18923/62500) 274 156
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t36 : ((-177215035443/2500000000000 : ℚ) : ℝ) ≤ stT274 36 := by
  have hc : ((-106329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177215035443/2500000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-106329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c37 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-248929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7622481/10000000) (δ := 13867/1000000000) (ψ := -18923/62500) 274 158
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t37 : ((-81851467317/500000000000 : ℚ) : ℝ) ≤ stT274 37 := by
  have hc : ((-497883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81851467317/500000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-497883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c38 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-109707/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5062727/10000000) (δ := 43/3125000) (ψ := -18923/62500) 274 159
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t38 : ((-71195447477/1000000000000 : ℚ) : ℝ) ≤ stT274 38 := by
  have hc : ((-219439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71195447477/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-219439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c39 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((370741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2977473/10000000) (δ := 13853/1000000000) (ψ := -18923/62500) 274 160
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t39 : ((593580455171/10000000000000 : ℚ) : ℝ) ≤ stT274 39 := by
  have hc : ((370691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((593580455171/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((370691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c40 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((859197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1342743/10000000) (δ := 6873/500000000) (ψ := -18923/62500) 274 161
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t40 : ((679214984643/5000000000000 : ℚ) : ℝ) ≤ stT274 40 := by
  have hc : ((859147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((679214984643/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((859147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c41 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((199703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5451/400000) (δ := 2753/200000000) (ψ := -18923/62500) 274 162
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t41 : ((311867946741/2000000000000 : ℚ) : ℝ) ≤ stT274 41 := by
  have hc : ((199693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311867946741/2000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((199693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c42 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((24127/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 331309/5000000) (δ := 867/62500000) (ψ := -18923/62500) 274 163
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t42 : ((148907313599/1000000000000 : ℚ) : ℝ) ≤ stT274 42 := by
  have hc : ((96503/100000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148907313599/1000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((96503/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c43 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((909291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1073047/10000000) (δ := 13779/1000000000) (ψ := -18923/62500) 274 164
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t43 : ((277315777277/2000000000000 : ℚ) : ℝ) ≤ stT274 43 := by
  have hc : ((909241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277315777277/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((909241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c44 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((902543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1112891/10000000) (δ := 13717/1000000000) (ψ := -18923/62500) 274 165
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t44 : ((340139684277/2500000000000 : ℚ) : ℝ) ≤ stT274 44 := by
  have hc : ((902493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340139684277/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((902493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c45 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((949387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199699/2500000) (δ := 13793/1000000000) (ψ := -18923/62500) 274 166
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t45 : ((1415187108607/10000000000000 : ℚ) : ℝ) ≤ stT274 45 := by
  have hc : ((949337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1415187108607/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((949337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c46 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((499143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146379/10000000) (δ := 13703/1000000000) (ψ := -18923/62500) 274 167
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t46 : ((367954531221/2500000000000 : ℚ) : ℝ) ≤ stT274 46 := by
  have hc : ((249559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367954531221/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((249559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c47 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((472711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -829769/10000000) (δ := 2759/200000000) (ψ := -18923/62500) 274 168
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t47 : ((344741480607/2500000000000 : ℚ) : ℝ) ≤ stT274 47 := by
  have hc : ((236343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344741480607/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((236343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c48 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((331319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2116153/10000000) (δ := 2743/200000000) (ψ := -18923/62500) 274 169
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t48 : ((1912725909/20000000000 : ℚ) : ℝ) ≤ stT274 48 := by
  have hc : ((165647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1912725909/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((165647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c49 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((45343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -924991/2500000) (δ := 6911/500000000) (ψ := -18923/62500) 274 170
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t49 : ((32369990289/2500000000000 : ℚ) : ℝ) ≤ stT274 49 := by
  have hc : ((22659/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32369990289/2500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((22659/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c50 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-19081/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -556901/1000000) (δ := 6937/500000000) (ψ := -18923/62500) 274 171
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t50 : ((-215894616347/2500000000000 : ℚ) : ℝ) ≤ stT274 50 := by
  have hc : ((-305321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215894616347/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-305321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c51 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-124799/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120503/156250) (δ := 13767/1000000000) (ψ := -18923/62500) 274 172
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t51 : ((-699049681101/5000000000000 : ℚ) : ℝ) ≤ stT274 51 := by
  have hc : ((-499221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-699049681101/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-499221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c52 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-61697/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5589207/10000000) (δ := 3459/250000000) (ψ := -18923/62500) 274 172
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t52 : ((-42782655101/500000000000 : ℚ) : ℝ) ≤ stT274 52 := by
  have hc : ((-30851/50000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42782655101/500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-30851/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c53 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((194291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146463/500000) (δ := 13859/1000000000) (ψ := -18923/62500) 274 173
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t53 : ((26684474893/500000000000 : ℚ) : ℝ) ≤ stT274 53 := by
  have hc : ((97133/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26684474893/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((97133/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c54 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((249987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12693/5000000) (δ := 13851/1000000000) (ψ := -18923/62500) 274 174
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t54 : ((680344097823/5000000000000 : ℚ) : ℝ) ≤ stT274 54 := by
  have hc : ((499949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680344097823/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((499949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c55 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((159853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -778361/2500000) (δ := 6879/500000000) (ψ := -18923/62500) 274 175
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t55 : ((53877978843/1250000000000 : ℚ) : ℝ) ≤ stT274 55 := by
  have hc : ((39957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53877978843/1250000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((39957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c56 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-852473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1295747/2000000) (δ := 6869/500000000) (ψ := -18923/62500) 274 176
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t56 : ((-1139232452561/10000000000000 : ℚ) : ℝ) ≤ stT274 56 := by
  have hc : ((-852523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1139232452561/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-852523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c57 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-63453/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5645491/10000000) (δ := 6869/500000000) (ψ := -18923/62500) 274 176
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t57 : ((-42026107557/500000000000 : ℚ) : ℝ) ≤ stT274 57 := by
  have hc : ((-31729/50000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42026107557/500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-31729/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c58 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((738223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1850911/10000000) (δ := 3443/250000000) (ψ := -18923/62500) 274 177
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t58 : ((121158549009/1250000000000 : ℚ) : ℝ) ≤ stT274 58 := by
  have hc : ((738173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121158549009/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((738173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c59 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((653229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -536847/2500000) (δ := 13879/1000000000) (ψ := -18923/62500) 274 178
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t59 : ((850366555131/10000000000000 : ℚ) : ℝ) ≤ stT274 59 := by
  have hc : ((653179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((850366555131/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((653179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c60 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-822731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -792811/1250000) (δ := 13787/1000000000) (ψ := -18923/62500) 274 179
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t60 : ((-212441231419/2000000000000 : ℚ) : ℝ) ≤ stT274 60 := by
  have hc : ((-822781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212441231419/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-822781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c61 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-408889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2490041/5000000) (δ := 1727/125000000) (ψ := -18923/62500) 274 179
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t61 : ((-523592818491/10000000000000 : ℚ) : ℝ) ≤ stT274 61 := by
  have hc : ((-408939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-523592818491/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-408939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c62 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((197309/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205281/5000000) (δ := 6947/500000000) (ψ := -18923/62500) 274 180
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t62 : ((250569927299/2000000000000 : ℚ) : ℝ) ≤ stT274 62 := by
  have hc : ((197299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250569927299/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((197299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c63 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-4083/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -542141/1250000) (δ := 6901/500000000) (ψ := -18923/62500) 274 181
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t63 : ((-10291346117/500000000000 : ℚ) : ℝ) ≤ stT274 63 := by
  have hc : ((-16337/100000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10291346117/500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-16337/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c64 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-423253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3225229/5000000) (δ := 13801/1000000000) (ψ := -18923/62500) 274 181
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t64 : ((-264548961639/2500000000000 : ℚ) : ℝ) ≤ stT274 64 := by
  have hc : ((-211639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264548961639/2500000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-211639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c65 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((17101/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1362871/10000000) (δ := 2779/200000000) (ψ := -18923/62500) 274 182
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t65 : ((212099337/2000000000 : ℚ) : ℝ) ≤ stT274 65 := by
  have hc : ((171/200 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212099337/2000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((171/200 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c66 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((8027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1943427/5000000) (δ := 2763/200000000) (ψ := -18923/62500) 274 183
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t66 : ((2462443457/1250000000000 : ℚ) : ℝ) ≤ stT274 66 := by
  have hc : ((4001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2462443457/1250000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((4001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c67 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-33547/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6414107/10000000) (δ := 3447/250000000) (ψ := -18923/62500) 274 183
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t67 : ((-8197329111/80000000000 : ℚ) : ℝ) ≤ stT274 67 := by
  have hc : ((-33549/40000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8197329111/80000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-33549/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c68 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((188431/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 854487/10000000) (δ := 347/25000000) (ψ := -18923/62500) 274 184
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t68 : ((114247000719/1000000000000 : ℚ) : ℝ) ≤ stT274 68 := by
  have hc : ((188421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114247000719/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((188421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c69 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-362103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2426649/5000000) (δ := 13773/1000000000) (ψ := -18923/62500) 274 185
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t69 : ((-435981148427/10000000000000 : ℚ) : ℝ) ≤ stT274 69 := by
  have hc : ((-362153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435981148427/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-362153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c70 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-52153/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2501481/5000000) (δ := 1383/100000000) (ψ := -18923/62500) 274 185
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t70 : ((-249368992873/5000000000000 : ℚ) : ℝ) ≤ stT274 70 := by
  have hc : ((-208637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249368992873/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-208637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c71 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((184567/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -988551/10000000) (δ := 6933/500000000) (ψ := -18923/62500) 274 186
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t71 : ((219028741017/2000000000000 : ℚ) : ℝ) ≤ stT274 71 := by
  have hc : ((184557/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219028741017/2000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((184557/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c72 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-478367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3557949/5000000) (δ := 3461/250000000) (ψ := -18923/62500) 274 187
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t72 : ((-4404614943/39062500000 : ℚ) : ℝ) ≤ stT274 72 := by
  have hc : ((-59799/62500 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4404614943/39062500000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-59799/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c73 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((595423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72891/312500) (δ := 13759/1000000000) (ψ := -18923/62500) 274 187
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t73 : ((696831108303/10000000000000 : ℚ) : ℝ) ≤ stT274 73 := by
  have hc : ((595373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((696831108303/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((595373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c74 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-51427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -811123/2000000) (δ := 13751/1000000000) (ψ := -18923/62500) 274 188
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t74 : ((-59840828529/10000000000000 : ℚ) : ℝ) ≤ stT274 74 := by
  have hc : ((-51477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59840828529/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-51477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c75 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-116527/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 642401/1250000) (δ := 3463/250000000) (ψ := -18923/62500) 274 188
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t75 : ((-269136554379/5000000000000 : ℚ) : ℝ) ≤ stT274 75 := by
  have hc : ((-233079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269136554379/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-233079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c76 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((165257/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1495793/10000000) (δ := 2749/200000000) (ψ := -18923/62500) 274 189
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t76 : ((94775599133/1000000000000 : ℚ) : ℝ) ≤ stT274 76 := by
  have hc : ((165247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94775599133/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((165247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c77 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-3086/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1864649/2500000) (δ := 6929/500000000) (ψ := -18923/62500) 274 189
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t77 : ((-56272034871/500000000000 : ℚ) : ℝ) ≤ stT274 77 := by
  have hc : ((-98757/100000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56272034871/500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-98757/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c78 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((972331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589461/10000000) (δ := 13837/1000000000) (ψ := -18923/62500) 274 190
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t78 : ((1100891413837/10000000000000 : ℚ) : ℝ) ≤ stT274 78 := by
  have hc : ((972281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1100891413837/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((972281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c79 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-83389/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6392287/10000000) (δ := 1373/100000000) (ψ := -18923/62500) 274 191
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t79 : ((-1466024823/15625000000 : ℚ) : ℝ) ≤ stT274 79 := by
  have hc : ((-41697/50000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1466024823/15625000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-41697/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c80 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((629663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2224191/10000000) (δ := 1373/100000000) (ψ := -18923/62500) 274 191
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t80 : ((703928111229/10000000000000 : ℚ) : ℝ) ≤ stT274 80 := by
  have hc : ((629613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((703928111229/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((629613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c81 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-406799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124359/250000) (δ := 13823/1000000000) (ψ := -18923/62500) 274 192
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t81 : ((-56506850761/1250000000000 : ℚ) : ℝ) ≤ stT274 81 := by
  have hc : ((-406849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56506850761/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-406849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c82 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((197231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3430659/10000000) (δ := 689/50000000) (ψ := -18923/62500) 274 192
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t82 : ((43549987203/2000000000000 : ℚ) : ℝ) ≤ stT274 82 := by
  have hc : ((197181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43549987203/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((197181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c83 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-18861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794829/2000000) (δ := 13887/1000000000) (ψ := -18923/62500) 274 193
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t83 : ((-20757526773/10000000000000 : ℚ) : ℝ) ≤ stT274 83 := by
  have hc : ((-18911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20757526773/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-18911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c84 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-24143/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4229517/10000000) (δ := 6879/250000000) (ψ := -18923/62500) 274 193
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t84 : ((-2635309677/200000000000 : ℚ) : ℝ) ≤ stT274 84 := by
  have hc : ((-24153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2635309677/200000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-24153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c85 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((220237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421481/1250000) (δ := 13809/1000000000) (ψ := -18923/62500) 274 194
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t85 : ((59706567481/2500000000000 : ℚ) : ℝ) ≤ stT274 85 := by
  have hc : ((220187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59706567481/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((220187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c86 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-281319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 579989/1250000) (δ := 13809/1000000000) (ψ := -18923/62500) 274 194
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t86 : ((-37926008879/1250000000000 : ℚ) : ℝ) ≤ stT274 86 := by
  have hc : ((-281369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37926008879/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-281369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c87 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((306261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -629767/2000000) (δ := 13901/1000000000) (ψ := -18923/62500) 274 195
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t87 : ((20518280477/625000000000 : ℚ) : ℝ) ≤ stT274 87 := by
  have hc : ((306211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20518280477/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((306211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c88 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-296603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187193/400000) (δ := 6851/500000000) (ψ := -18923/62500) 274 195
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t88 : ((-79058321153/2500000000000 : ℚ) : ℝ) ≤ stT274 88 := by
  have hc : ((-296653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79058321153/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-296653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c89 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((25283/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3287981/10000000) (δ := 6897/500000000) (ψ := -18923/62500) 274 196
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t89 : ((13397302083/500000000000 : ℚ) : ℝ) ≤ stT274 89 := by
  have hc : ((12639/50000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13397302083/500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((12639/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c90 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-43649/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 436573/1000000) (δ := 13809/1000000000) (ψ := -18923/62500) 274 196
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t90 : ((-92046563039/5000000000000 : ℚ) : ℝ) ≤ stT274 90 := by
  have hc : ((-87323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92046563039/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-87323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c91 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((61523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1886543/5000000) (δ := 6879/250000000) (ψ := -18923/62500) 274 197
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t91 : ((16110290583/2500000000000 : ℚ) : ℝ) ≤ stT274 91 := by
  have hc : ((61473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16110290583/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((61473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c92 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((85367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3713313/10000000) (δ := 3429/250000000) (ψ := -18923/62500) 274 197
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t92 : ((22237278831/2500000000000 : ℚ) : ℝ) ≤ stT274 92 := by
  have hc : ((85317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22237278831/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((85317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c93 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-261791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35853/78125) (δ := 689/50000000) (ψ := -18923/62500) 274 198
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t93 : ((-33939568579/1250000000000 : ℚ) : ℝ) ≤ stT274 93 := by
  have hc : ((-261841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33939568579/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-261841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c94 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((45819/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2737097/10000000) (δ := 13823/1000000000) (ψ := -18923/62500) 274 198
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t94 : ((23626760847/500000000000 : ℚ) : ℝ) ≤ stT274 94 := by
  have hc : ((22907/50000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23626760847/500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((22907/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c95 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-657921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -357633/625000) (δ := 1373/100000000) (ψ := -18923/62500) 274 199
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t95 : ((-675064428609/10000000000000 : ℚ) : ℝ) ≤ stT274 95 := by
  have hc : ((-657971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-675064428609/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-657971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c96 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((836307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181339/1250000) (δ := 13873/1000000000) (ψ := -18923/62500) 274 199
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t96 : ((42675030967/500000000000 : ℚ) : ℝ) ≤ stT274 96 := by
  have hc : ((836257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42675030967/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((836257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c97 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-961579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7158733/10000000) (δ := 6883/500000000) (ψ := -18923/62500) 274 200
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t97 : ((-976387120263/10000000000000 : ℚ) : ℝ) ≤ stT274 97 := by
  have hc : ((-961629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-976387120263/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-961629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c98 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((199717/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13303/1000000) (δ := 13837/1000000000) (ψ := -18923/62500) 274 200
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t98 : ((25216803183/250000000000 : ℚ) : ℝ) ≤ stT274 98 := by
  have hc : ((199707/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25216803183/250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((199707/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c99 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-457951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1705341/2500000) (δ := 13837/1000000000) (ψ := -18923/62500) 274 200
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t99 : ((-28767705193/312500000000 : ℚ) : ℝ) ≤ stT274 99 := by
  have hc : ((-57247/62500 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28767705193/312500000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-57247/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c100 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((696091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62567/312500) (δ := 2749/200000000) (ψ := -18923/62500) 274 201
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t100 : ((696040303959/10000000000000 : ℚ) : ℝ) ≤ stT274 100 := by
  have hc : ((696041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((696040303959/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((696041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c101 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-347361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120347/250000) (δ := 2749/200000000) (ψ := -18923/62500) 274 201
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t101 : ((-172843573309/5000000000000 : ℚ) : ℝ) ≤ stT274 101 := by
  have hc : ((-347411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172843573309/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-347411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c102 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-21799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2072629/5000000) (δ := 13751/1000000000) (ψ := -18923/62500) 274 202
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t102 : ((-10798306551/1250000000000 : ℚ) : ℝ) ≤ stT274 102 := by
  have hc : ((-43623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10798306551/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-43623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c103 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((263781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2537671/10000000) (δ := 3463/250000000) (ψ := -18923/62500) 274 202
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t103 : ((64971608931/1250000000000 : ℚ) : ℝ) ≤ stT274 103 := by
  have hc : ((65939/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64971608931/1250000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((65939/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c104 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-867403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6551891/10000000) (δ := 13759/1000000000) (ψ := -18923/62500) 274 203
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t104 : ((-850607930193/10000000000000 : ℚ) : ℝ) ≤ stT274 104 := by
  have hc : ((-867453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-850607930193/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-867453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c105 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 201/625000) (δ := 3461/250000000) (ψ := -18923/62500) 274 203
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t105 : ((9758502291/100000000000 : ℚ) : ℝ) ≤ stT274 105 := by
  have hc : ((999949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9758502291/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((999949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c106 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-856089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3248063/5000000) (δ := 13759/1000000000) (ψ := -18923/62500) 274 203
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t106 : ((-415777912377/5000000000000 : ℚ) : ℝ) ≤ stT274 106 := by
  have hc : ((-856139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415777912377/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-856139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c107 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((110733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -173739/625000) (δ := 6933/500000000) (ψ := -18923/62500) 274 204
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t107 : ((13379686661/312500000000 : ℚ) : ℝ) ≤ stT274 107 := by
  have hc : ((221441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13379686661/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((221441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c108 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((133469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5613/15625) (δ := 6933/500000000) (ψ := -18923/62500) 274 204
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t108 : ((513529731/40000000000 : ℚ) : ℝ) ≤ stT274 108 := by
  have hc : ((133419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((513529731/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((133419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c109 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-681721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5802273/10000000) (δ := 1383/100000000) (ψ := -18923/62500) 274 205
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t109 : ((-653018671617/10000000000000 : ℚ) : ℝ) ≤ stT274 109 := by
  have hc : ((-681771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653018671617/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-681771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c110 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((983593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45349/1000000) (δ := 13773/1000000000) (ψ := -18923/62500) 274 205
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t110 : ((468885437933/5000000000000 : ℚ) : ℝ) ≤ stT274 110 := by
  have hc : ((983543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468885437933/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((983543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c111 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-886753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6652671/10000000) (δ := 1383/100000000) (ψ := -18923/62500) 274 205
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t111 : ((-420858080937/5000000000000 : ℚ) : ℝ) ≤ stT274 111 := by
  have hc : ((-886803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-420858080937/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-886803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c112 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((395007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2911801/10000000) (δ := 13723/1000000000) (ψ := -18923/62500) 274 206
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t112 : ((373199213827/10000000000000 : ℚ) : ℝ) ≤ stT274 112 := by
  have hc : ((394957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373199213827/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((394957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c113 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((147727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 794291/2500000) (δ := 13723/1000000000) (ψ := -18923/62500) 274 206
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t113 : ((868413909/31250000000 : ℚ) : ℝ) ≤ stT274 113 := by
  have hc : ((73851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((868413909/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((73851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c114 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-855967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3247769/5000000) (δ := 3447/250000000) (ψ := -18923/62500) 274 207
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t114 : ((-400866768981/5000000000000 : ℚ) : ℝ) ≤ stT274 114 := by
  have hc : ((-856017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400866768981/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-856017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c115 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((61189/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256477/5000000) (δ := 2763/200000000) (ψ := -18923/62500) 274 207
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t115 : ((57056073181/625000000000 : ℚ) : ℝ) ≤ stT274 115 := by
  have hc : ((489487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57056073181/625000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((489487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c116 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-561597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 338611/625000) (δ := 2763/200000000) (ψ := -18923/62500) 274 207
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t116 : ((-521476321619/10000000000000 : ℚ) : ℝ) ≤ stT274 116 := by
  have hc : ((-561647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521476321619/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-561647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c117 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-38423/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102571/2500000) (δ := 3427/250000000) (ψ := -18923/62500) 274 208
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t117 : ((-35531346933/2000000000000 : ℚ) : ℝ) ≤ stT274 117 := by
  have hc : ((-38433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35531346933/2000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-38433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c118 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((210769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 709773/5000000) (δ := 2779/200000000) (ψ := -18923/62500) 274 208
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t118 : ((194016954231/2500000000000 : ℚ) : ℝ) ≤ stT274 118 := by
  have hc : ((421513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194016954231/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((421513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c119 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-120749/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1800031/2500000) (δ := 2779/200000000) (ψ := -18923/62500) 274 208
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t119 : ((-442784867679/5000000000000 : ℚ) : ℝ) ≤ stT274 119 := by
  have hc : ((-483021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-442784867679/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-483021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c120 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((444463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1387777/5000000) (δ := 6901/500000000) (ψ := -18923/62500) 274 209
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t120 : ((40569129531/1000000000000 : ℚ) : ℝ) ≤ stT274 120 := by
  have hc : ((444413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40569129531/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((444413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c121 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((395991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 727281/2500000) (δ := 6901/500000000) (ψ := -18923/62500) 274 209
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t121 : ((35994600369/1000000000000 : ℚ) : ℝ) ≤ stT274 121 := by
  have hc : ((395941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35994600369/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((395941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c122 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-480911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7160947/10000000) (δ := 13709/1000000000) (ψ := -18923/62500) 274 210
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t122 : ((-27213703443/312500000000 : ℚ) : ℝ) ≤ stT274 122 := by
  have hc : ((-60117/62500 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27213703443/312500000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-60117/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c123 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((809419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1569087/10000000) (δ := 6947/500000000) (ψ := -18923/62500) 274 210
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t123 : ((729782936861/10000000000000 : ℚ) : ℝ) ≤ stT274 123 := by
  have hc : ((809369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((729782936861/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((809369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c124 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-101/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 795499/2000000) (δ := 6947/500000000) (ψ := -18923/62500) 274 210
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t124 : ((-72740187/40000000000 : ℚ) : ℝ) ≤ stT274 124 := by
  have hc : ((-81/4000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72740187/40000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-81/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c125 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-397973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6228411/10000000) (δ := 13787/1000000000) (ψ := -18923/62500) 274 211
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t125 : ((-44497569393/625000000000 : ℚ) : ℝ) ≤ stT274 125 := by
  have hc : ((-198999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44497569393/625000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-198999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c126 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((476459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -385097/5000000) (δ := 13787/1000000000) (ψ := -18923/62500) 274 211
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t126 : ((21222037879/250000000000 : ℚ) : ℝ) ≤ stT274 126 := by
  have hc : ((238217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21222037879/250000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((238217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c127 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-56639/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2903/6250) (δ := 1727/125000000) (ψ := -18923/62500) 274 211
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t127 : ((-50267886693/2000000000000 : ℚ) : ℝ) ≤ stT274 127 := by
  have hc : ((-56649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50267886693/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-56649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c128 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-648363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1422643/2500000) (δ := 13879/1000000000) (ψ := -18923/62500) 274 212
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t128 : ((-143280469023/2500000000000 : ℚ) : ℝ) ≤ stT274 128 := by
  have hc : ((-648413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143280469023/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-648413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c129 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((989663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71953/2000000) (δ := 13879/1000000000) (ψ := -18923/62500) 274 212
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t129 : ((17426095317/200000000000 : ℚ) : ℝ) ≤ stT274 129 := by
  have hc : ((989613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17426095317/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((989613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c130 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-78091/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 985961/2000000) (δ := 13879/1000000000) (ψ := -18923/62500) 274 212
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t130 : ((-68499184959/2000000000000 : ℚ) : ℝ) ≤ stT274 130 := by
  have hc : ((-78101/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68499184959/2000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-78101/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c131 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-597863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5529071/10000000) (δ := 13831/1000000000) (ψ := -18923/62500) 274 213
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t131 : ((-104479915533/2000000000000 : ℚ) : ℝ) ≤ stT274 131 := by
  have hc : ((-597913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104479915533/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-597913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c132 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((991823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3999/125000) (δ := 13831/1000000000) (ψ := -18923/62500) 274 213
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t132 : ((215806829481/2500000000000 : ℚ) : ℝ) ≤ stT274 132 := by
  have hc : ((991773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215806829481/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((991773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c133 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-9021/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606239/1250000) (δ := 13831/1000000000) (ψ := -18923/62500) 274 213
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t133 : ((-3129313279/100000000000 : ℚ) : ℝ) ≤ stT274 133 := by
  have hc : ((-36089/100000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3129313279/100000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-36089/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c134 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-329687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1431739/2500000) (δ := 13769/500000000) (ψ := -18923/62500) 274 214
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t134 : ((-17801748483/312500000000 : ℚ) : ℝ) ≤ stT274 134 := by
  have hc : ((-20607/31250 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17801748483/312500000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-20607/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c135 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((484007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19813/312500) (δ := 2773/200000000) (ψ := -18923/62500) 274 214
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t135 : ((104136229021/1250000000000 : ℚ) : ℝ) ≤ stT274 135 := by
  have hc : ((241991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104136229021/1250000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((241991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c136 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-196459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4421353/10000000) (δ := 6869/500000000) (ψ := -18923/62500) 274 214
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t136 : ((-168505091937/10000000000000 : ℚ) : ℝ) ≤ stT274 136 := by
  have hc : ((-196509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168505091937/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-196509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c137 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-805487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -783529/1250000) (δ := 6879/500000000) (ψ := -18923/62500) 274 215
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t137 : ((-344108490123/5000000000000 : ℚ) : ℝ) ≤ stT274 137 := by
  have hc : ((-805537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344108490123/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-805537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c138 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((870503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40201/312500) (δ := 2769/200000000) (ψ := -18923/62500) 274 215
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t138 : ((92622292371/1250000000000 : ℚ) : ℝ) ≤ stT274 138 := by
  have hc : ((870453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92622292371/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((870453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c139 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((106803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3659473/10000000) (δ := 6879/500000000) (ψ := -18923/62500) 274 215
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t139 : ((22636653391/2500000000000 : ℚ) : ℝ) ≤ stT274 139 := by
  have hc : ((106753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22636653391/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((106753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c140 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-959277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1784517/2500000) (δ := 13851/1000000000) (ψ := -18923/62500) 274 216
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t140 : ((-162156002137/2000000000000 : ℚ) : ℝ) ≤ stT274 140 := by
  have hc : ((-959327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162156002137/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-959327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c141 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((617639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2262649/10000000) (δ := 13851/1000000000) (ψ := -18923/62500) 274 216
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t141 : ((520103193939/10000000000000 : ℚ) : ℝ) ≤ stT274 141 := by
  have hc : ((617589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520103193939/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((617589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c142 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((256829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2578383/10000000) (δ := 13851/1000000000) (ψ := -18923/62500) 274 216
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t142 : ((53876259381/1250000000000 : ℚ) : ℝ) ≤ stT274 142 := by
  have hc : ((64201/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53876259381/1250000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((64201/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c143 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-982489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7385439/10000000) (δ := 13851/1000000000) (ψ := -18923/62500) 274 216
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t143 : ((-821641360977/10000000000000 : ℚ) : ℝ) ≤ stT274 143 := by
  have hc : ((-982539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-821641360977/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-982539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c144 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((9413/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3549033/10000000) (δ := 859/62500000) (ψ := -18923/62500) 274 217
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t144 : ((62732474907/5000000000000 : ℚ) : ℝ) ≤ stT274 144 := by
  have hc : ((75279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62732474907/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((75279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c145 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((444279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119151/1000000) (δ := 13859/1000000000) (ψ := -18923/62500) 274 217
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t145 : ((92233127829/1250000000000 : ℚ) : ℝ) ≤ stT274 145 := by
  have hc : ((222127/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92233127829/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((222127/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c146 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-177409/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2949723/5000000) (δ := 859/62500000) (ψ := -18923/62500) 274 217
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t146 : ((-146835097929/2500000000000 : ℚ) : ℝ) ≤ stT274 146 := by
  have hc : ((-354843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146835097929/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-354843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c147 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-463831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641597/1250000) (δ := 3459/250000000) (ψ := -18923/62500) 274 218
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t147 : ((-382603018347/10000000000000 : ℚ) : ℝ) ≤ stT274 147 := by
  have hc : ((-463881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382603018347/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-463881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c148 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((245239/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488681/10000000) (δ := 13767/1000000000) (ψ := -18923/62500) 274 218
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t148 : ((201574711641/2500000000000 : ℚ) : ℝ) ≤ stT274 148 := by
  have hc : ((490453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201574711641/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((490453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c149 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-78793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4124177/10000000) (δ := 3459/250000000) (ψ := -18923/62500) 274 218
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t149 : ((-2018459643/312500000000 : ℚ) : ℝ) ≤ stT274 149 := by
  have hc : ((-78843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2018459643/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-78843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c150 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-37699/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7001889/10000000) (δ := 6937/500000000) (ψ := -18923/62500) 274 219
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t150 : ((-30782753397/400000000000 : ℚ) : ℝ) ≤ stT274 150 := by
  have hc : ((-37701/40000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30782753397/400000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-37701/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c151 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((55691/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1225169/5000000) (δ := 6937/500000000) (ψ := -18923/62500) 274 219
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t151 : ((5664574821/125000000000 : ℚ) : ℝ) ≤ stT274 151 := by
  have hc : ((27843/50000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5664574821/125000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((27843/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c152 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((338007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2071141/10000000) (δ := 13729/1000000000) (ψ := -18923/62500) 274 219
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t152 : ((137069783037/2500000000000 : ℚ) : ℝ) ≤ stT274 152 := by
  have hc : ((168991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137069783037/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((168991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c153 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-434799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82037/125000) (δ := 13729/1000000000) (ψ := -18923/62500) 274 219
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t153 : ((-43941845909/625000000000 : ℚ) : ℝ) ≤ stT274 153 := by
  have hc : ((-54353/62500 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43941845909/625000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-54353/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c154 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-186/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2341217/5000000) (δ := 6911/500000000) (ψ := -18923/62500) 274 220
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t154 : ((-4797064319/200000000000 : ℚ) : ℝ) ≤ stT274 154 := by
  have hc : ((-5953/20000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4797064319/200000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-5953/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c155 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((995053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -248771/10000000) (δ := 13781/1000000000) (ψ := -18923/62500) 274 220
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t155 : ((799205314657/10000000000000 : ℚ) : ℝ) ≤ stT274 155 := by
  have hc : ((995003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799205314657/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((995003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c156 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-91633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 831279/2000000) (δ := 6911/500000000) (ψ := -18923/62500) 274 220
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t156 : ((-73405168803/10000000000000 : ℚ) : ℝ) ≤ stT274 156 := by
  have hc : ((-91683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73405168803/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-91683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c157 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-963297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1434911/2000000) (δ := 2743/200000000) (ψ := -18923/62500) 274 221
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t157 : ((-768834717189/10000000000000 : ℚ) : ℝ) ≤ stT274 157 := by
  have hc : ((-963347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-768834717189/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-963347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c158 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((106633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2825353/10000000) (δ := 2743/200000000) (ψ := -18923/62500) 274 221
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t158 : ((169645370237/5000000000000 : ℚ) : ℝ) ≤ stT274 158 := by
  have hc : ((213241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169645370237/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((213241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c159 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((826137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1496449/10000000) (δ := 2743/200000000) (ψ := -18923/62500) 274 221
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t159 : ((655129121437/10000000000000 : ℚ) : ℝ) ≤ stT274 159 := by
  have hc : ((826087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((655129121437/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((826087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c160 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-169613/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46329/80000) (δ := 2743/200000000) (ψ := -18923/62500) 274 221
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t160 : ((-26820166307/500000000000 : ℚ) : ℝ) ≤ stT274 160 := by
  have hc : ((-339251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26820166307/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-339251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c161 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-635597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2824473/5000000) (δ := 863/62500000) (ψ := -18923/62500) 274 222
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t161 : ((-500960392817/10000000000000 : ℚ) : ℝ) ≤ stT274 161 := by
  have hc : ((-635647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500960392817/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-635647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c162 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((422837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703713/5000000) (δ := 863/62500000) (ψ := -18923/62500) 274 222
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t162 : ((41524049411/625000000000 : ℚ) : ℝ) ≤ stT274 162 := by
  have hc : ((105703/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41524049411/625000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((105703/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c163 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((432801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701999/2500000) (δ := 2759/200000000) (ψ := -18923/62500) 274 222
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t163 : ((16947827413/500000000000 : ℚ) : ℝ) ≤ stT274 163 := by
  have hc : ((432751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16947827413/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((432751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c164 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-941899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6997593/10000000) (δ := 2759/200000000) (ψ := -18923/62500) 274 222
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t164 : ((-735538773681/10000000000000 : ℚ) : ℝ) ≤ stT274 164 := by
  have hc : ((-941949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-735538773681/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-941949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c165 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-245181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284141/625000) (δ := 139/10000000) (ψ := -18923/62500) 274 223
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t165 : ((-190912088269/10000000000000 : ℚ) : ℝ) ≤ stT274 165 := by
  have hc : ((-245231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190912088269/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-245231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c166 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((986759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5091/125000) (δ := 13703/1000000000) (ψ := -18923/62500) 274 223
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t166 : ((15316683807/200000000000 : ℚ) : ℝ) ≤ stT274 166 := by
  have hc : ((986709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15316683807/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((986709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c167 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((87923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1853449/5000000) (δ := 139/10000000) (ψ := -18923/62500) 274 223
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t167 : ((67998148479/10000000000000 : ℚ) : ℝ) ≤ stT274 167 := by
  have hc : ((87873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67998148479/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((87873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c168 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-199947/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7796417/10000000) (δ := 13703/1000000000) (ψ := -18923/62500) 274 223
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t168 : ((-154270224769/2000000000000 : ℚ) : ℝ) ≤ stT274 168 := by
  have hc : ((-199957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154270224769/2000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-199957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c169 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((8077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60097/156250) (δ := 1381/100000000) (ψ := -18923/62500) 274 224
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t169 : ((1240691067/500000000000 : ℚ) : ℝ) ≤ stT274 169 := by
  have hc : ((16129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1240691067/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((16129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c170 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((996957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97543/5000000) (δ := 13793/1000000000) (ψ := -18923/62500) 274 224
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t170 : ((191147945087/2500000000000 : ℚ) : ℝ) ≤ stT274 170 := by
  have hc : ((996907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191147945087/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((996907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c171 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-114027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 105317/250000) (δ := 1381/100000000) (ψ := -18923/62500) 274 224
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t171 : ((-1090462043/125000000000 : ℚ) : ℝ) ≤ stT274 171 := by
  have hc : ((-114077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1090462043/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-114077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c172 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-198011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7501117/10000000) (δ := 13717/1000000000) (ψ := -18923/62500) 274 225
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t172 : ((-150989626353/2000000000000 : ℚ) : ℝ) ≤ stT274 172 := by
  have hc : ((-198021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150989626353/2000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-198021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c173 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((158089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -441263/1250000) (δ := 6943/500000000) (ψ := -18923/62500) 274 225
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t173 : ((24030936223/2000000000000 : ℚ) : ℝ) ≤ stT274 173 := by
  have hc : ((158039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24030936223/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((158039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c174 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((986053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418031/10000000) (δ := 13717/1000000000) (ψ := -18923/62500) 274 225
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t174 : ((373743451147/5000000000000 : ℚ) : ℝ) ≤ stT274 174 := by
  have hc : ((986003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373743451147/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((986003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c175 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-82929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108589/250000) (δ := 6943/500000000) (ψ := -18923/62500) 274 225
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t175 : ((-31353667133/2500000000000 : ℚ) : ℝ) ≤ stT274 175 := by
  have hc : ((-41477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31353667133/2500000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-41477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c176 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-123461/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7461273/10000000) (δ := 13779/1000000000) (ψ := -18923/62500) 274 226
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t176 : ((-372268080951/5000000000000 : ℚ) : ℝ) ≤ stT274 176 := by
  have hc : ((-493869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-372268080951/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-493869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c177 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((4321/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17901/50000) (δ := 13779/1000000000) (ψ := -18923/62500) 274 226
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t177 : ((25973503353/2500000000000 : ℚ) : ℝ) ≤ stT274 177 := by
  have hc : ((69111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25973503353/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((69111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c178 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((993781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278953/10000000) (δ := 13779/1000000000) (ψ := -18923/62500) 274 226
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t178 : ((744832190161/10000000000000 : ℚ) : ℝ) ≤ stT274 178 := by
  have hc : ((993731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((744832190161/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((993731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c179 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-75743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4116529/10000000) (δ := 27/1953125) (ψ := -18923/62500) 274 226
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t179 : ((-14162604187/2500000000000 : ℚ) : ℝ) ≤ stT274 179 := by
  have hc : ((-75793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14162604187/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-75793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c180 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-199901/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77753/100000) (δ := 867/62500000) (ψ := -18923/62500) 274 227
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t180 : ((-37251215829/500000000000 : ℚ) : ℝ) ≤ stT274 180 := by
  have hc : ((-199911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37251215829/500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-199911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c181 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-21307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3980263/10000000) (δ := 867/62500000) (ψ := -18923/62500) 274 227
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t181 : ((-3174910263/2000000000000 : ℚ) : ℝ) ≤ stT274 181 := by
  have hc : ((-21357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3174910263/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-21357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c182 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((996601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206187/10000000) (δ := 867/62500000) (ψ := -18923/62500) 274 227
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t182 : ((738692432199/10000000000000 : ℚ) : ℝ) ≤ stT274 182 := by
  have hc : ((996551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((738692432199/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((996551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c183 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((30261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3547271/10000000) (δ := 13731/1000000000) (ψ := -18923/62500) 274 227
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t183 : ((22362174471/2000000000000 : ℚ) : ℝ) ≤ stT274 183 := by
  have hc : ((30251/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22362174471/2000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((30251/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c184 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-486891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7280247/10000000) (δ := 13731/1000000000) (ψ := -18923/62500) 274 227
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t184 : ((-8973983609/125000000000 : ℚ) : ℝ) ≤ stT274 184 := by
  have hc : ((-121729/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8973983609/125000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-121729/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c185 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-30999/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1178737/2500000) (δ := 2753/200000000) (ψ := -18923/62500) 274 228
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t185 : ((-1139730293/50000000000 : ℚ) : ℝ) ≤ stT274 185 := by
  have hc : ((-7751/25000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1139730293/50000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-7751/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c186 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((917559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4089/40000) (δ := 2753/200000000) (ψ := -18923/62500) 274 228
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t186 : ((134549942323/2000000000000 : ℚ) : ℝ) ≤ stT274 186 := by
  have hc : ((917509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134549942323/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((917509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c187 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((488621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16567/62500) (δ := 2753/200000000) (ψ := -18923/62500) 274 228
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t187 : ((44659786539/1250000000000 : ℚ) : ℝ) ≤ stT274 187 := by
  have hc : ((488571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44659786539/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((488571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c188 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-81389/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6304031/10000000) (δ := 6919/500000000) (ψ := -18923/62500) 274 228
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t188 : ((-1187253581/20000000000 : ℚ) : ℝ) ≤ stT274 188 := by
  have hc : ((-40697/50000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1187253581/20000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-40697/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c189 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-336101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5769939/10000000) (δ := 6873/500000000) (ψ := -18923/62500) 274 229
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t189 : ((-122247849759/2500000000000 : ℚ) : ℝ) ≤ stT274 189 := by
  have hc : ((-168063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122247849759/2500000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-168063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c190 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((325431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1077597/5000000) (δ := 6873/500000000) (ψ := -18923/62500) 274 229
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t190 : ((29509280407/625000000000 : ℚ) : ℝ) ≤ stT274 190 := by
  have hc : ((162703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29509280407/625000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((162703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c191 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((838507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288129/2000000) (δ := 6873/500000000) (ψ := -18923/62500) 274 229
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t191 : ((303342842659/5000000000000 : ℚ) : ℝ) ≤ stT274 191 := by
  have hc : ((838457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303342842659/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((838457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c192 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-84511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2508823/5000000) (δ := 13857/1000000000) (ψ := -18923/62500) 274 229
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t192 : ((-7624723931/250000000000 : ℚ) : ℝ) ≤ stT274 192 := by
  have hc : ((-84521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7624723931/250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-84521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c193 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-38343/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7131879/10000000) (δ := 11/800000) (ψ := -18923/62500) 274 230
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t193 : ((-690033613/10000000000 : ℚ) : ℝ) ≤ stT274 193 := by
  have hc : ((-7669/8000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-690033613/10000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-7669/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c194 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((5347/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3591799/10000000) (δ := 11/800000) (ψ := -18923/62500) 274 230
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t194 : ((383748551/40000000000 : ℚ) : ℝ) ≤ stT274 194 := by
  have hc : ((1069/8000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383748551/40000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((1069/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c195 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((999609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3497/500000) (δ := 11/800000) (ψ := -18923/62500) 274 230
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t195 : ((357899096863/5000000000000 : ℚ) : ℝ) ≤ stT274 195 := by
  have hc : ((999559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((357899096863/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((999559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c196 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((97979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214619/625000) (δ := 13853/1000000000) (ψ := -18923/62500) 274 230
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t196 : ((6996707289/500000000000 : ℚ) : ℝ) ≤ stT274 196 := by
  have hc : ((48977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6996707289/500000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((48977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c197 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-931013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6919937/10000000) (δ := 11/800000) (ψ := -18923/62500) 274 230
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t197 : ((-663355386673/10000000000000 : ℚ) : ℝ) ≤ stT274 197 := by
  have hc : ((-931063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-663355386673/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-931063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c198 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-264351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2659833/5000000) (δ := 13843/1000000000) (ψ := -18923/62500) 274 231
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t198 : ((-2348551149/62500000000 : ℚ) : ℝ) ≤ stT274 198 := by
  have hc : ((-33047/62500 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2348551149/62500000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-33047/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c199 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((91673/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1868773/10000000) (δ := 13843/1000000000) (ψ := -18923/62500) 274 231
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t199 : ((259923269627/5000000000000 : ℚ) : ℝ) ≤ stT274 199 := by
  have hc : ((366667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259923269627/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((366667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c200 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((810427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156479/1000000) (δ := 43/3125000) (ψ := -18923/62500) 274 231
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t200 : ((286511219481/5000000000000 : ℚ) : ℝ) ≤ stT274 200 := by
  have hc : ((810377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286511219481/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((810377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c201 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-102333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311331/625000) (δ := 43/3125000) (ψ := -18923/62500) 274 231
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t201 : ((-72188989043/2500000000000 : ℚ) : ℝ) ≤ stT274 201 := by
  have hc : ((-204691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72188989043/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-204691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c202 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-244471/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3663609/5000000) (δ := 1717/125000000) (ψ := -18923/62500) 274 232
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t202 : ((-172018101633/2500000000000 : ℚ) : ℝ) ≤ stT274 202 := by
  have hc : ((-488967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172018101633/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-488967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c203 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-1749/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1972241/5000000) (δ := 13867/1000000000) (ψ := -18923/62500) 274 232
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t203 : ((-2472663349/5000000000000 : ℚ) : ℝ) ≤ stT274 203 := by
  have hc : ((-3523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2472663349/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-3523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c204 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((243339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72299/1250000) (δ := 13867/1000000000) (ψ := -18923/62500) 274 232
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t204 : ((17036261571/250000000000 : ℚ) : ℝ) ≤ stT274 204 := by
  have hc : ((486653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17036261571/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((486653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c205 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((223001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1385629/5000000) (δ := 13867/1000000000) (ψ := -18923/62500) 274 232
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t205 : ((60833253/1953125000 : ℚ) : ℝ) ≤ stT274 205 := by
  have hc : ((6968/15625 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60833253/1953125000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((6968/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c206 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-765003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1220921/2000000) (δ := 13867/1000000000) (ψ := -18923/62500) 274 232
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t206 : ((-266519218451/5000000000000 : ℚ) : ℝ) ≤ stT274 206 := by
  have hc : ((-765053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266519218451/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-765053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c207 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-20243/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3143089/5000000) (δ := 13829/1000000000) (ψ := -18923/62500) 274 233
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t207 : ((-56282982873/1000000000000 : ℚ) : ℝ) ≤ stT274 207 := by
  have hc : ((-80977/100000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56282982873/1000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-80977/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c208 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((367959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2984957/10000000) (δ := 6887/500000000) (ψ := -18923/62500) 274 233
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t208 : ((2040791223/80000000000 : ℚ) : ℝ) ≤ stT274 208 := by
  have hc : ((367909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2040791223/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((367909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c209 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((248197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7511/250000) (δ := 6887/500000000) (ψ := -18923/62500) 274 233
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t209 : ((171672693233/2500000000000 : ℚ) : ℝ) ≤ stT274 209 := by
  have hc : ((496369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171672693233/2500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((496369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c210 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((35563/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71403/200000) (δ := 13829/1000000000) (ψ := -18923/62500) 274 233
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t210 : ((9812862313/1000000000000 : ℚ) : ℝ) ≤ stT274 210 := by
  have hc : ((71101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9812862313/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((71101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c211 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-7331/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6824311/10000000) (δ := 13829/1000000000) (ψ := -18923/62500) 274 233
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t211 : ((-25235741853/400000000000 : ℚ) : ℝ) ≤ stT274 211 := by
  have hc : ((-36657/40000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25235741853/400000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-36657/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c212 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-158587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5644903/10000000) (δ := 6941/500000000) (ψ := -18923/62500) 274 234
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t212 : ((-217853224797/5000000000000 : ℚ) : ℝ) ≤ stT274 212 := by
  have hc : ((-317199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217853224797/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-317199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c213 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((566499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1210681/5000000) (δ := 13721/1000000000) (ψ := -18923/62500) 274 234
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t213 : ((97031014353/2500000000000 : ℚ) : ℝ) ≤ stT274 213 := by
  have hc : ((566449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97031014353/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((566449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c214 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((190169/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78711/1000000) (δ := 6941/500000000) (ψ := -18923/62500) 274 234
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t214 : ((25997968003/400000000000 : ℚ) : ℝ) ≤ stT274 214 := by
  have hc : ((190159/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25997968003/400000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((190159/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c215 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-10717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199029/500000) (δ := 6941/500000000) (ψ := -18923/62500) 274 234
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t215 : ((-732599029/500000000000 : ℚ) : ℝ) ≤ stT274 215 := by
  have hc : ((-5371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-732599029/500000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-5371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c216 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-240409/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3579627/5000000) (δ := 6941/500000000) (ψ := -18923/62500) 274 234
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t216 : ((-163586154501/2500000000000 : ℚ) : ℝ) ≤ stT274 216 := by
  have hc : ((-480843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163586154501/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-480843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c217 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-275311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5384763/10000000) (δ := 13789/1000000000) (ψ := -18923/62500) 274 235
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t217 : ((-4672761673/125000000000 : ℚ) : ℝ) ≤ stT274 217 := by
  have hc : ((-34417/62500 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4672761673/125000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-34417/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c218 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((626193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2235339/10000000) (δ := 6907/500000000) (ψ := -18923/62500) 274 235
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t218 : ((84815452351/2000000000000 : ℚ) : ℝ) ≤ stT274 218 := by
  have hc : ((626143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84815452351/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((626143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c219 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((935939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 899701/10000000) (δ := 13789/1000000000) (ψ := -18923/62500) 274 235
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t219 : ((632414825193/10000000000000 : ℚ) : ℝ) ≤ stT274 219 := by
  have hc : ((935889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((632414825193/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((935889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c220 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-7473/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502553/1250000) (δ := 13789/1000000000) (ψ := -18923/62500) 274 235
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t220 : ((-25225193/10000000000 : ℚ) : ℝ) ≤ stT274 220 := by
  have hc : ((-7483/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25225193/10000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-7483/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c221 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-958021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1781759/2500000) (δ := 13789/1000000000) (ψ := -18923/62500) 274 235
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t221 : ((-644468493783/10000000000000 : ℚ) : ℝ) ≤ stT274 221 := by
  have hc : ((-958071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-644468493783/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-958071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c222 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-36547/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2744213/5000000) (δ := 1737/125000000) (ψ := -18923/62500) 274 236
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t222 : ((-196246977957/5000000000000 : ℚ) : ℝ) ≤ stT274 222 := by
  have hc : ((-292401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196246977957/5000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-292401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c223 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((570317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1204881/5000000) (δ := 1737/125000000) (ψ := -18923/62500) 274 236
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t223 : ((381878726283/10000000000000 : ℚ) : ℝ) ≤ stT274 223 := by
  have hc : ((570267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381878726283/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((570267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c224 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((48293/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655133/10000000) (δ := 13707/1000000000) (ψ := -18923/62500) 274 236
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t224 : ((64530884893/1000000000000 : ℚ) : ℝ) ≤ stT274 224 := by
  have hc : ((96581/100000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64530884893/1000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((96581/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c225 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((88123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3706397/10000000) (δ := 13707/1000000000) (ψ := -18923/62500) 274 236
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t225 : ((29357637309/5000000000000 : ℚ) : ℝ) ≤ stT274 225 := by
  have hc : ((88073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29357637309/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((88073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c226 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-180611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52688/78125) (δ := 3437/125000000) (ψ := -18923/62500) 274 236
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t226 : ((-120147463611/2000000000000 : ℚ) : ℝ) ≤ stT274 226 := by
  have hc : ((-180621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120147463611/2000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-180621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c227 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-360429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -593959/1000000) (δ := 13803/1000000000) (ψ := -18923/62500) 274 237
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t227 : ((-29905246337/625000000000 : ℚ) : ℝ) ≤ stT274 227 := by
  have hc : ((-180227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29905246337/625000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-180227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c228 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((48603/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -732151/2500000) (δ := 13803/1000000000) (ψ := -18923/62500) 274 237
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t228 : ((64367950471/2500000000000 : ℚ) : ℝ) ≤ stT274 228 := by
  have hc : ((194387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64367950471/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((194387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c229 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((999617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6923/1000000) (δ := 13803/1000000000) (ψ := -18923/62500) 274 237
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t229 : ((330265932903/5000000000000 : ℚ) : ℝ) ≤ stT274 229 := by
  have hc : ((999567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330265932903/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((999567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c230 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((6843/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152699/500000) (δ := 69/5000000) (ψ := -18923/62500) 274 237
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t230 : ((112786949/5000000000 : ℚ) : ℝ) ≤ stT274 230 := by
  have hc : ((3421/10000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112786949/5000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((3421/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c231 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-744321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 753223/1250000) (δ := 69/5000000) (ψ := -18923/62500) 274 237
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t231 : ((-15305012131/312500000000 : ℚ) : ℝ) ≤ stT274 231 := by
  have hc : ((-744371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15305012131/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-744371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c232 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-112431/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6723253/10000000) (δ := 1371/100000000) (ψ := -18923/62500) 274 238
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t232 : ((-295275060217/5000000000000 : ℚ) : ℝ) ≤ stT274 232 := by
  have hc : ((-449749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295275060217/5000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-449749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c233 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((1499/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3777/10000) (δ := 13893/1000000000) (ψ := -18923/62500) 274 238
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t233 : ((3924829911/1000000000000 : ℚ) : ℝ) ≤ stT274 233 := by
  have hc : ((5991/100000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3924829911/1000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((5991/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c234 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((471819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16867/200000) (δ := 1371/100000000) (ψ := -18923/62500) 274 238
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t234 : ((3855264671/62500000000 : ℚ) : ℝ) ≤ stT274 234 := by
  have hc : ((235897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3855264671/62500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((235897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c235 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((674059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519441/2500000) (δ := 1371/100000000) (ψ := -18923/62500) 274 238
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t235 : ((54959367869/1250000000000 : ℚ) : ℝ) ≤ stT274 235 := by
  have hc : ((674009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54959367869/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((674009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c236 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-411223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4986479/10000000) (δ := 13893/1000000000) (ψ := -18923/62500) 274 238
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t236 : ((-53543220597/2000000000000 : ℚ) : ℝ) ≤ stT274 236 := by
  have hc : ((-411273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53543220597/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-411273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c237 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-999933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3912549/5000000) (δ := 13817/1000000000) (ψ := -18923/62500) 274 239
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t237 : ((-64955895731/1000000000000 : ℚ) : ℝ) ≤ stT274 237 := by
  have hc : ((-999983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64955895731/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-999983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c238 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-394539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2470453/5000000) (δ := 6893/500000000) (ψ := -18923/62500) 274 239
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t238 : ((-63943542039/2500000000000 : ℚ) : ℝ) ≤ stT274 238 := by
  have hc : ((-394589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63943542039/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-394589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c239 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((676713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2068769/10000000) (δ := 13817/1000000000) (ψ := -18923/62500) 274 239
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t239 : ((218848377449/5000000000000 : ℚ) : ℝ) ≤ stT274 239 := by
  have hc : ((676663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218848377449/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((676663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c240 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((475157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39569/500000) (δ := 13817/1000000000) (ψ := -18923/62500) 274 239
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t240 : ((76674070151/1250000000000 : ℚ) : ℝ) ≤ stT274 240 := by
  have hc : ((118783/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76674070151/1250000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((118783/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c241 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((114699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363961/1000000) (δ := 13817/1000000000) (ψ := -18923/62500) 274 239
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t241 : ((18462960311/2500000000000 : ℚ) : ℝ) ≤ stT274 241 := by
  have hc : ((114649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18462960311/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((114649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c242 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-851913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3238029/5000000) (δ := 13817/1000000000) (ψ := -18923/62500) 274 239
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t242 : ((-21906524619/400000000000 : ℚ) : ℝ) ≤ stT274 242 := by
  have hc : ((-851963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21906524619/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-851963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c243 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-837161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6407171/10000000) (δ := 549/40000000) (ψ := -18923/62500) 274 240
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t243 : ((-537071693711/10000000000000 : ℚ) : ℝ) ≤ stT274 243 := by
  have hc : ((-837211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537071693711/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-837211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c244 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((66399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3594013/10000000) (δ := 549/40000000) (ψ := -18923/62500) 274 240
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t244 : ((2655723301/312500000000 : ℚ) : ℝ) ≤ stT274 244 := by
  have hc : ((33187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2655723301/312500000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((33187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c245 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((237547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -792397/10000000) (δ := 1101/40000000) (ψ := -18923/62500) 274 240
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t245 : ((75877545611/1250000000000 : ℚ) : ℝ) ≤ stT274 245 := by
  have hc : ((475069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75877545611/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((475069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c246 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((174331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1997847/10000000) (δ := 6939/500000000) (ψ := -18923/62500) 274 240
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t246 : ((27785322989/625000000000 : ℚ) : ℝ) ≤ stT274 246 := by
  have hc : ((348637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27785322989/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((348637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c247 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-166699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955351/2000000) (δ := 6939/500000000) (ψ := -18923/62500) 274 240
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t247 : ((-5304199017/250000000000 : ℚ) : ℝ) ≤ stT274 247 := by
  have hc : ((-41681/125000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5304199017/250000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-41681/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c248 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-124043/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7544429/10000000) (δ := 6939/500000000) (ψ := -18923/62500) 274 240
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t248 : ((-315085591197/5000000000000 : ℚ) : ℝ) ≤ stT274 248 := by
  have hc : ((-496197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315085591197/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-496197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c249 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-558033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216281/400000) (δ := 1729/125000000) (ψ := -18923/62500) 274 241
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t249 : ((-14146845967/400000000000 : ℚ) : ℝ) ≤ stT274 249 := by
  have hc : ((-558083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14146845967/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-558083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_c250 :
    |Real.cos (((274 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((242431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2661477/10000000) (δ := 13771/1000000000) (ψ := -18923/62500) 274 241
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st274_t250 : ((15331088673/500000000000 : ℚ) : ℝ) ≤ stT274 250 := by
  have hc : ((121203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((274 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st274_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15331088673/500000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((121203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st274_p1 : ((190893/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT274 (i+1) := by
  rw [Finset.sum_range_one]
  exact st274_t1

theorem st274_p2 : ((526662563257/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT274 (i+1))
      = (∑ i ∈ Finset.range 1, stT274 (i+1)) + stT274 2 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 1
    simpa using h
  have hprev := st274_p1
  have hstep := st274_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p3 : ((3497518639089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT274 (i+1))
      = (∑ i ∈ Finset.range 2, stT274 (i+1)) + stT274 3 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 2
    simpa using h
  have hprev := st274_p2
  have hstep := st274_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p4 : ((4495181778207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT274 (i+1))
      = (∑ i ∈ Finset.range 3, stT274 (i+1)) + stT274 4 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 3
    simpa using h
  have hprev := st274_p3
  have hstep := st274_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p5 : ((9458859946879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT274 (i+1))
      = (∑ i ∈ Finset.range 4, stT274 (i+1)) + stT274 5 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 4
    simpa using h
  have hprev := st274_p4
  have hstep := st274_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p6 : ((11102401880367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT274 (i+1))
      = (∑ i ∈ Finset.range 5, stT274 (i+1)) + stT274 6 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 5
    simpa using h
  have hprev := st274_p5
  have hstep := st274_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p7 : ((14245810846559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT274 (i+1))
      = (∑ i ∈ Finset.range 6, stT274 (i+1)) + stT274 7 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 6
    simpa using h
  have hprev := st274_p6
  have hstep := st274_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p8 : ((13789712818423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT274 (i+1))
      = (∑ i ∈ Finset.range 7, stT274 (i+1)) + stT274 8 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 7
    simpa using h
  have hprev := st274_p7
  have hstep := st274_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p9 : ((16005732596821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT274 (i+1))
      = (∑ i ∈ Finset.range 8, stT274 (i+1)) + stT274 9 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 8
    simpa using h
  have hprev := st274_p8
  have hstep := st274_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p10 : ((2588172449211/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT274 (i+1))
      = (∑ i ∈ Finset.range 9, stT274 (i+1)) + stT274 10 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 9
    simpa using h
  have hprev := st274_p9
  have hstep := st274_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p11 : ((2140075251873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT274 (i+1))
      = (∑ i ∈ Finset.range 10, stT274 (i+1)) + stT274 11 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 10
    simpa using h
  have hprev := st274_p10
  have hstep := st274_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p12 : ((8251989097573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT274 (i+1))
      = (∑ i ∈ Finset.range 11, stT274 (i+1)) + stT274 12 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 11
    simpa using h
  have hprev := st274_p11
  have hstep := st274_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p13 : ((10512577422073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT274 (i+1))
      = (∑ i ∈ Finset.range 12, stT274 (i+1)) + stT274 13 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 12
    simpa using h
  have hprev := st274_p12
  have hstep := st274_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p14 : ((12299948167149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT274 (i+1))
      = (∑ i ∈ Finset.range 13, stT274 (i+1)) + stT274 14 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 13
    simpa using h
  have hprev := st274_p13
  have hstep := st274_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p15 : ((13919590509729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT274 (i+1))
      = (∑ i ∈ Finset.range 14, stT274 (i+1)) + stT274 15 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 14
    simpa using h
  have hprev := st274_p14
  have hstep := st274_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p16 : ((16326655509729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT274 (i+1))
      = (∑ i ∈ Finset.range 15, stT274 (i+1)) + stT274 16 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 15
    simpa using h
  have hprev := st274_p15
  have hstep := st274_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p17 : ((7183276158841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT274 (i+1))
      = (∑ i ∈ Finset.range 16, stT274 (i+1)) + stT274 17 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 16
    simpa using h
  have hprev := st274_p16
  have hstep := st274_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p18 : ((4083437201531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT274 (i+1))
      = (∑ i ∈ Finset.range 17, stT274 (i+1)) + stT274 18 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 17
    simpa using h
  have hprev := st274_p17
  have hstep := st274_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p19 : ((7074509924283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT274 (i+1))
      = (∑ i ∈ Finset.range 18, stT274 (i+1)) + stT274 19 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 18
    simpa using h
  have hprev := st274_p18
  have hstep := st274_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p20 : ((6646213459563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT274 (i+1))
      = (∑ i ∈ Finset.range 19, stT274 (i+1)) + stT274 20 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 19
    simpa using h
  have hprev := st274_p19
  have hstep := st274_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p21 : ((7080146101397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT274 (i+1))
      = (∑ i ∈ Finset.range 20, stT274 (i+1)) + stT274 21 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 20
    simpa using h
  have hprev := st274_p20
  have hstep := st274_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p22 : ((15344897120197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT274 (i+1))
      = (∑ i ∈ Finset.range 21, stT274 (i+1)) + stT274 22 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 21
    simpa using h
  have hprev := st274_p21
  have hstep := st274_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p23 : ((15764363453533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT274 (i+1))
      = (∑ i ∈ Finset.range 22, stT274 (i+1)) + stT274 23 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 22
    simpa using h
  have hprev := st274_p22
  have hstep := st274_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p24 : ((14445453718831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT274 (i+1))
      = (∑ i ∈ Finset.range 23, stT274 (i+1)) + stT274 24 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 23
    simpa using h
  have hprev := st274_p23
  have hstep := st274_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p25 : ((12702588847399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT274 (i+1))
      = (∑ i ∈ Finset.range 24, stT274 (i+1)) + stT274 25 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 24
    simpa using h
  have hprev := st274_p24
  have hstep := st274_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p26 : ((14056256693717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT274 (i+1))
      = (∑ i ∈ Finset.range 25, stT274 (i+1)) + stT274 26 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 25
    simpa using h
  have hprev := st274_p25
  have hstep := st274_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p27 : ((14351700160217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT274 (i+1))
      = (∑ i ∈ Finset.range 26, stT274 (i+1)) + stT274 27 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 26
    simpa using h
  have hprev := st274_p26
  have hstep := st274_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p28 : ((6571313655727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT274 (i+1))
      = (∑ i ∈ Finset.range 27, stT274 (i+1)) + stT274 28 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 27
    simpa using h
  have hprev := st274_p27
  have hstep := st274_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p29 : ((2915787549407/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT274 (i+1))
      = (∑ i ∈ Finset.range 28, stT274 (i+1)) + stT274 29 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 28
    simpa using h
  have hprev := st274_p28
  have hstep := st274_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p30 : ((13336195333959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT274 (i+1))
      = (∑ i ∈ Finset.range 29, stT274 (i+1)) + stT274 30 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 29
    simpa using h
  have hprev := st274_p29
  have hstep := st274_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p31 : ((867565934519/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT274 (i+1))
      = (∑ i ∈ Finset.range 30, stT274 (i+1)) + stT274 31 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 30
    simpa using h
  have hprev := st274_p30
  have hstep := st274_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p32 : ((3649381744143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT274 (i+1))
      = (∑ i ∈ Finset.range 31, stT274 (i+1)) + stT274 32 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 31
    simpa using h
  have hprev := st274_p31
  have hstep := st274_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p33 : ((12878918771667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT274 (i+1))
      = (∑ i ∈ Finset.range 32, stT274 (i+1)) + stT274 33 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 32
    simpa using h
  have hprev := st274_p32
  have hstep := st274_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p34 : ((3419903170863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT274 (i+1))
      = (∑ i ∈ Finset.range 33, stT274 (i+1)) + stT274 34 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 33
    simpa using h
  have hprev := st274_p33
  have hstep := st274_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p35 : ((3774640504437/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT274 (i+1))
      = (∑ i ∈ Finset.range 34, stT274 (i+1)) + stT274 35 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 34
    simpa using h
  have hprev := st274_p34
  have hstep := st274_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p36 : ((1798712734497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT274 (i+1))
      = (∑ i ∈ Finset.range 35, stT274 (i+1)) + stT274 36 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 35
    simpa using h
  have hprev := st274_p35
  have hstep := st274_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p37 : ((3188168132409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT274 (i+1))
      = (∑ i ∈ Finset.range 36, stT274 (i+1)) + stT274 37 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 36
    simpa using h
  have hprev := st274_p36
  have hstep := st274_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p38 : ((6020359027433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT274 (i+1))
      = (∑ i ∈ Finset.range 37, stT274 (i+1)) + stT274 38 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 37
    simpa using h
  have hprev := st274_p37
  have hstep := st274_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p39 : ((12634298510037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT274 (i+1))
      = (∑ i ∈ Finset.range 38, stT274 (i+1)) + stT274 39 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 38
    simpa using h
  have hprev := st274_p38
  have hstep := st274_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p40 : ((13992728479323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT274 (i+1))
      = (∑ i ∈ Finset.range 39, stT274 (i+1)) + stT274 40 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 39
    simpa using h
  have hprev := st274_p39
  have hstep := st274_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p41 : ((3888017053257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT274 (i+1))
      = (∑ i ∈ Finset.range 40, stT274 (i+1)) + stT274 41 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 40
    simpa using h
  have hprev := st274_p40
  have hstep := st274_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p42 : ((8520570674509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT274 (i+1))
      = (∑ i ∈ Finset.range 41, stT274 (i+1)) + stT274 42 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 41
    simpa using h
  have hprev := st274_p41
  have hstep := st274_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p43 : ((18427720235403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT274 (i+1))
      = (∑ i ∈ Finset.range 42, stT274 (i+1)) + stT274 43 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 42
    simpa using h
  have hprev := st274_p42
  have hstep := st274_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p44 : ((19788278972511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT274 (i+1))
      = (∑ i ∈ Finset.range 43, stT274 (i+1)) + stT274 44 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 43
    simpa using h
  have hprev := st274_p43
  have hstep := st274_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p45 : ((10601733040559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT274 (i+1))
      = (∑ i ∈ Finset.range 44, stT274 (i+1)) + stT274 45 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 44
    simpa using h
  have hprev := st274_p44
  have hstep := st274_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p46 : ((11337642103001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT274 (i+1))
      = (∑ i ∈ Finset.range 45, stT274 (i+1)) + stT274 46 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 45
    simpa using h
  have hprev := st274_p45
  have hstep := st274_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p47 : ((2405425012843/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT274 (i+1))
      = (∑ i ∈ Finset.range 46, stT274 (i+1)) + stT274 47 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 46
    simpa using h
  have hprev := st274_p46
  have hstep := st274_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p48 : ((2501061308293/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT274 (i+1))
      = (∑ i ∈ Finset.range 47, stT274 (i+1)) + stT274 48 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 47
    simpa using h
  have hprev := st274_p47
  have hstep := st274_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p49 : ((12570046522043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT274 (i+1))
      = (∑ i ∈ Finset.range 48, stT274 (i+1)) + stT274 49 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 48
    simpa using h
  have hprev := st274_p48
  have hstep := st274_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p50 : ((12138257289349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT274 (i+1))
      = (∑ i ∈ Finset.range 49, stT274 (i+1)) + stT274 50 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 49
    simpa using h
  have hprev := st274_p49
  have hstep := st274_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p51 : ((1429900951031/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT274 (i+1))
      = (∑ i ∈ Finset.range 50, stT274 (i+1)) + stT274 51 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 50
    simpa using h
  have hprev := st274_p50
  have hstep := st274_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p52 : ((5505690528619/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT274 (i+1))
      = (∑ i ∈ Finset.range 51, stT274 (i+1)) + stT274 52 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 51
    simpa using h
  have hprev := st274_p51
  have hstep := st274_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p53 : ((1409778225771/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT274 (i+1))
      = (∑ i ∈ Finset.range 52, stT274 (i+1)) + stT274 53 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 52
    simpa using h
  have hprev := st274_p52
  have hstep := st274_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p54 : ((11958569903991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT274 (i+1))
      = (∑ i ∈ Finset.range 53, stT274 (i+1)) + stT274 54 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 53
    simpa using h
  have hprev := st274_p53
  have hstep := st274_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p55 : ((12174081819363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT274 (i+1))
      = (∑ i ∈ Finset.range 54, stT274 (i+1)) + stT274 55 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 54
    simpa using h
  have hprev := st274_p54
  have hstep := st274_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p56 : ((4641786237233/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT274 (i+1))
      = (∑ i ∈ Finset.range 55, stT274 (i+1)) + stT274 56 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 55
    simpa using h
  have hprev := st274_p55
  have hstep := st274_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p57 : ((894736361401/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT274 (i+1))
      = (∑ i ∈ Finset.range 56, stT274 (i+1)) + stT274 57 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 56
    simpa using h
  have hprev := st274_p56
  have hstep := st274_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p58 : ((23337677427097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT274 (i+1))
      = (∑ i ∈ Finset.range 57, stT274 (i+1)) + stT274 58 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 57
    simpa using h
  have hprev := st274_p57
  have hstep := st274_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p59 : ((6047010995557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT274 (i+1))
      = (∑ i ∈ Finset.range 58, stT274 (i+1)) + stT274 59 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 58
    simpa using h
  have hprev := st274_p58
  have hstep := st274_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p60 : ((23125837825133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT274 (i+1))
      = (∑ i ∈ Finset.range 59, stT274 (i+1)) + stT274 60 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 59
    simpa using h
  have hprev := st274_p59
  have hstep := st274_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p61 : ((11301122503321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT274 (i+1))
      = (∑ i ∈ Finset.range 60, stT274 (i+1)) + stT274 61 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 60
    simpa using h
  have hprev := st274_p60
  have hstep := st274_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p62 : ((23855094643137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT274 (i+1))
      = (∑ i ∈ Finset.range 61, stT274 (i+1)) + stT274 62 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 61
    simpa using h
  have hprev := st274_p61
  have hstep := st274_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p63 : ((23649267720797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT274 (i+1))
      = (∑ i ∈ Finset.range 62, stT274 (i+1)) + stT274 63 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 62
    simpa using h
  have hprev := st274_p62
  have hstep := st274_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p64 : ((22591071874241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT274 (i+1))
      = (∑ i ∈ Finset.range 63, stT274 (i+1)) + stT274 64 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 63
    simpa using h
  have hprev := st274_p63
  have hstep := st274_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p65 : ((23651568559241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT274 (i+1))
      = (∑ i ∈ Finset.range 64, stT274 (i+1)) + stT274 65 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 64
    simpa using h
  have hprev := st274_p64
  have hstep := st274_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p66 : ((23671268106897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT274 (i+1))
      = (∑ i ∈ Finset.range 65, stT274 (i+1)) + stT274 66 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 65
    simpa using h
  have hprev := st274_p65
  have hstep := st274_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p67 : ((11323300984011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT274 (i+1))
      = (∑ i ∈ Finset.range 66, stT274 (i+1)) + stT274 67 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 66
    simpa using h
  have hprev := st274_p66
  have hstep := st274_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p68 : ((5947267993803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT274 (i+1))
      = (∑ i ∈ Finset.range 67, stT274 (i+1)) + stT274 68 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 67
    simpa using h
  have hprev := st274_p67
  have hstep := st274_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p69 : ((4670618165357/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT274 (i+1))
      = (∑ i ∈ Finset.range 68, stT274 (i+1)) + stT274 69 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 68
    simpa using h
  have hprev := st274_p68
  have hstep := st274_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p70 : ((22854352841039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT274 (i+1))
      = (∑ i ∈ Finset.range 69, stT274 (i+1)) + stT274 70 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 69
    simpa using h
  have hprev := st274_p69
  have hstep := st274_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p71 : ((5987374136531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT274 (i+1))
      = (∑ i ∈ Finset.range 70, stT274 (i+1)) + stT274 71 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 70
    simpa using h
  have hprev := st274_p70
  have hstep := st274_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p72 : ((5705478780179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT274 (i+1))
      = (∑ i ∈ Finset.range 71, stT274 (i+1)) + stT274 72 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 71
    simpa using h
  have hprev := st274_p71
  have hstep := st274_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p73 : ((23518746229019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT274 (i+1))
      = (∑ i ∈ Finset.range 72, stT274 (i+1)) + stT274 73 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 72
    simpa using h
  have hprev := st274_p72
  have hstep := st274_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p74 : ((2345890540049/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT274 (i+1))
      = (∑ i ∈ Finset.range 73, stT274 (i+1)) + stT274 74 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 73
    simpa using h
  have hprev := st274_p73
  have hstep := st274_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p75 : ((5730158072933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT274 (i+1))
      = (∑ i ∈ Finset.range 74, stT274 (i+1)) + stT274 75 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 74
    simpa using h
  have hprev := st274_p74
  have hstep := st274_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p76 : ((11934194141531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT274 (i+1))
      = (∑ i ∈ Finset.range 75, stT274 (i+1)) + stT274 76 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 75
    simpa using h
  have hprev := st274_p75
  have hstep := st274_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p77 : ((11371473792821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT274 (i+1))
      = (∑ i ∈ Finset.range 76, stT274 (i+1)) + stT274 77 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 76
    simpa using h
  have hprev := st274_p76
  have hstep := st274_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p78 : ((23843838999479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT274 (i+1))
      = (∑ i ∈ Finset.range 77, stT274 (i+1)) + stT274 78 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 77
    simpa using h
  have hprev := st274_p77
  have hstep := st274_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p79 : ((22905583112759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT274 (i+1))
      = (∑ i ∈ Finset.range 78, stT274 (i+1)) + stT274 79 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 78
    simpa using h
  have hprev := st274_p78
  have hstep := st274_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p80 : ((5902377805997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT274 (i+1))
      = (∑ i ∈ Finset.range 79, stT274 (i+1)) + stT274 80 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 79
    simpa using h
  have hprev := st274_p79
  have hstep := st274_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p81 : ((231574564179/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT274 (i+1))
      = (∑ i ∈ Finset.range 80, stT274 (i+1)) + stT274 81 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 80
    simpa using h
  have hprev := st274_p80
  have hstep := st274_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p82 : ((4675041270783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT274 (i+1))
      = (∑ i ∈ Finset.range 81, stT274 (i+1)) + stT274 82 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 81
    simpa using h
  have hprev := st274_p81
  have hstep := st274_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p83 : ((11677224413571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT274 (i+1))
      = (∑ i ∈ Finset.range 82, stT274 (i+1)) + stT274 83 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 82
    simpa using h
  have hprev := st274_p82
  have hstep := st274_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p84 : ((5805670835823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT274 (i+1))
      = (∑ i ∈ Finset.range 83, stT274 (i+1)) + stT274 84 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 83
    simpa using h
  have hprev := st274_p83
  have hstep := st274_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p85 : ((733172175413/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT274 (i+1))
      = (∑ i ∈ Finset.range 84, stT274 (i+1)) + stT274 85 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 84
    simpa using h
  have hprev := st274_p84
  have hstep := st274_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p86 : ((2894762692773/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT274 (i+1))
      = (∑ i ∈ Finset.range 85, stT274 (i+1)) + stT274 86 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 85
    simpa using h
  have hprev := st274_p85
  have hstep := st274_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p87 : ((2935799253727/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT274 (i+1))
      = (∑ i ∈ Finset.range 86, stT274 (i+1)) + stT274 87 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 86
    simpa using h
  have hprev := st274_p86
  have hstep := st274_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p88 : ((5792540186301/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT274 (i+1))
      = (∑ i ∈ Finset.range 87, stT274 (i+1)) + stT274 88 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 87
    simpa using h
  have hprev := st274_p87
  have hstep := st274_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p89 : ((1464881674179/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT274 (i+1))
      = (∑ i ∈ Finset.range 88, stT274 (i+1)) + stT274 89 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 88
    simpa using h
  have hprev := st274_p88
  have hstep := st274_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p90 : ((11627006830393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT274 (i+1))
      = (∑ i ∈ Finset.range 89, stT274 (i+1)) + stT274 90 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 89
    simpa using h
  have hprev := st274_p89
  have hstep := st274_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p91 : ((11659227411559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT274 (i+1))
      = (∑ i ∈ Finset.range 90, stT274 (i+1)) + stT274 91 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 90
    simpa using h
  have hprev := st274_p90
  have hstep := st274_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p92 : ((11703701969221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT274 (i+1))
      = (∑ i ∈ Finset.range 91, stT274 (i+1)) + stT274 92 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 91
    simpa using h
  have hprev := st274_p91
  have hstep := st274_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p93 : ((2313588738981/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT274 (i+1))
      = (∑ i ∈ Finset.range 92, stT274 (i+1)) + stT274 93 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 92
    simpa using h
  have hprev := st274_p92
  have hstep := st274_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p94 : ((94433690427/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT274 (i+1))
      = (∑ i ∈ Finset.range 93, stT274 (i+1)) + stT274 94 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 93
    simpa using h
  have hprev := st274_p93
  have hstep := st274_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p95 : ((22933358178141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT274 (i+1))
      = (∑ i ∈ Finset.range 94, stT274 (i+1)) + stT274 95 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 94
    simpa using h
  have hprev := st274_p94
  have hstep := st274_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p96 : ((23786858797481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT274 (i+1))
      = (∑ i ∈ Finset.range 95, stT274 (i+1)) + stT274 96 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 95
    simpa using h
  have hprev := st274_p95
  have hstep := st274_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p97 : ((11405235838609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT274 (i+1))
      = (∑ i ∈ Finset.range 96, stT274 (i+1)) + stT274 97 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 96
    simpa using h
  have hprev := st274_p96
  have hstep := st274_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p98 : ((11909571902269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT274 (i+1))
      = (∑ i ∈ Finset.range 97, stT274 (i+1)) + stT274 98 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 97
    simpa using h
  have hprev := st274_p97
  have hstep := st274_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p99 : ((11449288619181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT274 (i+1))
      = (∑ i ∈ Finset.range 98, stT274 (i+1)) + stT274 99 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 98
    simpa using h
  have hprev := st274_p98
  have hstep := st274_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p100 : ((23594617542321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT274 (i+1))
      = (∑ i ∈ Finset.range 99, stT274 (i+1)) + stT274 100 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 99
    simpa using h
  have hprev := st274_p99
  have hstep := st274_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p101 : ((23248930395703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT274 (i+1))
      = (∑ i ∈ Finset.range 100, stT274 (i+1)) + stT274 101 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 100
    simpa using h
  have hprev := st274_p100
  have hstep := st274_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p102 : ((4632508788659/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT274 (i+1))
      = (∑ i ∈ Finset.range 101, stT274 (i+1)) + stT274 102 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 101
    simpa using h
  have hprev := st274_p101
  have hstep := st274_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p103 : ((23682316814743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT274 (i+1))
      = (∑ i ∈ Finset.range 102, stT274 (i+1)) + stT274 103 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 102
    simpa using h
  have hprev := st274_p102
  have hstep := st274_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p104 : ((456634177691/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT274 (i+1))
      = (∑ i ∈ Finset.range 103, stT274 (i+1)) + stT274 104 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 103
    simpa using h
  have hprev := st274_p103
  have hstep := st274_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p105 : ((476151182273/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT274 (i+1))
      = (∑ i ∈ Finset.range 104, stT274 (i+1)) + stT274 105 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 104
    simpa using h
  have hprev := st274_p104
  have hstep := st274_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p106 : ((359000051389/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT274 (i+1))
      = (∑ i ∈ Finset.range 105, stT274 (i+1)) + stT274 106 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 105
    simpa using h
  have hprev := st274_p105
  have hstep := st274_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p107 : ((731379789439/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT274 (i+1))
      = (∑ i ∈ Finset.range 106, stT274 (i+1)) + stT274 107 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 106
    simpa using h
  have hprev := st274_p106
  have hstep := st274_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p108 : ((11766267847399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT274 (i+1))
      = (∑ i ∈ Finset.range 107, stT274 (i+1)) + stT274 108 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 107
    simpa using h
  have hprev := st274_p107
  have hstep := st274_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p109 : ((22879517023181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT274 (i+1))
      = (∑ i ∈ Finset.range 108, stT274 (i+1)) + stT274 109 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 108
    simpa using h
  have hprev := st274_p108
  have hstep := st274_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p110 : ((23817287899047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT274 (i+1))
      = (∑ i ∈ Finset.range 109, stT274 (i+1)) + stT274 110 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 109
    simpa using h
  have hprev := st274_p109
  have hstep := st274_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p111 : ((22975571737173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT274 (i+1))
      = (∑ i ∈ Finset.range 110, stT274 (i+1)) + stT274 111 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 110
    simpa using h
  have hprev := st274_p110
  have hstep := st274_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p112 : ((23348770951/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT274 (i+1))
      = (∑ i ∈ Finset.range 111, stT274 (i+1)) + stT274 112 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 111
    simpa using h
  have hprev := st274_p111
  have hstep := st274_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p113 : ((590666585047/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT274 (i+1))
      = (∑ i ∈ Finset.range 112, stT274 (i+1)) + stT274 113 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 112
    simpa using h
  have hprev := st274_p112
  have hstep := st274_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p114 : ((11412464931959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT274 (i+1))
      = (∑ i ∈ Finset.range 113, stT274 (i+1)) + stT274 114 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 113
    simpa using h
  have hprev := st274_p113
  have hstep := st274_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p115 : ((11868913517407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT274 (i+1))
      = (∑ i ∈ Finset.range 114, stT274 (i+1)) + stT274 115 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 114
    simpa using h
  have hprev := st274_p114
  have hstep := st274_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p116 : ((4643270142639/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT274 (i+1))
      = (∑ i ∈ Finset.range 115, stT274 (i+1)) + stT274 116 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 115
    simpa using h
  have hprev := st274_p115
  have hstep := st274_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p117 : ((2303869397853/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT274 (i+1))
      = (∑ i ∈ Finset.range 116, stT274 (i+1)) + stT274 117 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 116
    simpa using h
  have hprev := st274_p116
  have hstep := st274_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p118 : ((11907380897727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT274 (i+1))
      = (∑ i ∈ Finset.range 117, stT274 (i+1)) + stT274 118 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 117
    simpa using h
  have hprev := st274_p117
  have hstep := st274_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p119 : ((358268625939/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT274 (i+1))
      = (∑ i ∈ Finset.range 118, stT274 (i+1)) + stT274 119 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 118
    simpa using h
  have hprev := st274_p118
  have hstep := st274_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p120 : ((11667441677703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT274 (i+1))
      = (∑ i ∈ Finset.range 119, stT274 (i+1)) + stT274 120 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 119
    simpa using h
  have hprev := st274_p119
  have hstep := st274_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p121 : ((2961853669887/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT274 (i+1))
      = (∑ i ∈ Finset.range 120, stT274 (i+1)) + stT274 121 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 120
    simpa using h
  have hprev := st274_p120
  have hstep := st274_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p122 : ((570599771223/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT274 (i+1))
      = (∑ i ∈ Finset.range 121, stT274 (i+1)) + stT274 122 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 121
    simpa using h
  have hprev := st274_p121
  have hstep := st274_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p123 : ((23553773785781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT274 (i+1))
      = (∑ i ∈ Finset.range 122, stT274 (i+1)) + stT274 123 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 122
    simpa using h
  have hprev := st274_p122
  have hstep := st274_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p124 : ((23535588739031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT274 (i+1))
      = (∑ i ∈ Finset.range 123, stT274 (i+1)) + stT274 124 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 123
    simpa using h
  have hprev := st274_p123
  have hstep := st274_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p125 : ((22823627628743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT274 (i+1))
      = (∑ i ∈ Finset.range 124, stT274 (i+1)) + stT274 125 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 124
    simpa using h
  have hprev := st274_p124
  have hstep := st274_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p126 : ((23672509143903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT274 (i+1))
      = (∑ i ∈ Finset.range 125, stT274 (i+1)) + stT274 126 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 125
    simpa using h
  have hprev := st274_p125
  have hstep := st274_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p127 : ((11710584855219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT274 (i+1))
      = (∑ i ∈ Finset.range 126, stT274 (i+1)) + stT274 127 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 126
    simpa using h
  have hprev := st274_p126
  have hstep := st274_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p128 : ((11424023917173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT274 (i+1))
      = (∑ i ∈ Finset.range 127, stT274 (i+1)) + stT274 128 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 127
    simpa using h
  have hprev := st274_p127
  have hstep := st274_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p129 : ((5929838150049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT274 (i+1))
      = (∑ i ∈ Finset.range 128, stT274 (i+1)) + stT274 129 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 128
    simpa using h
  have hprev := st274_p128
  have hstep := st274_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p130 : ((23376856675401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT274 (i+1))
      = (∑ i ∈ Finset.range 129, stT274 (i+1)) + stT274 130 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 129
    simpa using h
  have hprev := st274_p129
  have hstep := st274_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p131 : ((2856807137217/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT274 (i+1))
      = (∑ i ∈ Finset.range 130, stT274 (i+1)) + stT274 131 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 130
    simpa using h
  have hprev := st274_p130
  have hstep := st274_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p132 : ((1185884220783/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT274 (i+1))
      = (∑ i ∈ Finset.range 131, stT274 (i+1)) + stT274 132 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 131
    simpa using h
  have hprev := st274_p131
  have hstep := st274_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p133 : ((292559413597/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT274 (i+1))
      = (∑ i ∈ Finset.range 132, stT274 (i+1)) + stT274 133 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 132
    simpa using h
  have hprev := st274_p132
  have hstep := st274_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p134 : ((1427193571019/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT274 (i+1))
      = (∑ i ∈ Finset.range 133, stT274 (i+1)) + stT274 134 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 133
    simpa using h
  have hprev := st274_p133
  have hstep := st274_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p135 : ((2958523371059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT274 (i+1))
      = (∑ i ∈ Finset.range 134, stT274 (i+1)) + stT274 135 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 134
    simpa using h
  have hprev := st274_p134
  have hstep := st274_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p136 : ((4699936375307/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT274 (i+1))
      = (∑ i ∈ Finset.range 135, stT274 (i+1)) + stT274 136 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 135
    simpa using h
  have hprev := st274_p135
  have hstep := st274_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p137 : ((22811464896289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT274 (i+1))
      = (∑ i ∈ Finset.range 136, stT274 (i+1)) + stT274 137 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 136
    simpa using h
  have hprev := st274_p136
  have hstep := st274_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p138 : ((23552443235257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT274 (i+1))
      = (∑ i ∈ Finset.range 137, stT274 (i+1)) + stT274 138 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 137
    simpa using h
  have hprev := st274_p137
  have hstep := st274_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p139 : ((23642989848821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT274 (i+1))
      = (∑ i ∈ Finset.range 138, stT274 (i+1)) + stT274 139 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 138
    simpa using h
  have hprev := st274_p138
  have hstep := st274_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p140 : ((2854026229767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT274 (i+1))
      = (∑ i ∈ Finset.range 139, stT274 (i+1)) + stT274 140 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 139
    simpa using h
  have hprev := st274_p139
  have hstep := st274_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p141 : ((934092521283/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT274 (i+1))
      = (∑ i ∈ Finset.range 140, stT274 (i+1)) + stT274 141 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 140
    simpa using h
  have hprev := st274_p140
  have hstep := st274_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p142 : ((23783323107123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT274 (i+1))
      = (∑ i ∈ Finset.range 141, stT274 (i+1)) + stT274 142 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 141
    simpa using h
  have hprev := st274_p141
  have hstep := st274_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p143 : ((11480840873073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT274 (i+1))
      = (∑ i ∈ Finset.range 142, stT274 (i+1)) + stT274 143 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 142
    simpa using h
  have hprev := st274_p142
  have hstep := st274_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p144 : ((577178667399/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT274 (i+1))
      = (∑ i ∈ Finset.range 143, stT274 (i+1)) + stT274 144 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 143
    simpa using h
  have hprev := st274_p143
  have hstep := st274_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p145 : ((372265808103/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT274 (i+1))
      = (∑ i ∈ Finset.range 144, stT274 (i+1)) + stT274 145 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 144
    simpa using h
  have hprev := st274_p144
  have hstep := st274_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p146 : ((5809417831719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT274 (i+1))
      = (∑ i ∈ Finset.range 145, stT274 (i+1)) + stT274 146 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 145
    simpa using h
  have hprev := st274_p145
  have hstep := st274_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p147 : ((22855068308529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT274 (i+1))
      = (∑ i ∈ Finset.range 146, stT274 (i+1)) + stT274 147 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 146
    simpa using h
  have hprev := st274_p146
  have hstep := st274_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p148 : ((23661367155093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT274 (i+1))
      = (∑ i ∈ Finset.range 147, stT274 (i+1)) + stT274 148 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 147
    simpa using h
  have hprev := st274_p147
  have hstep := st274_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p149 : ((23596776446517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT274 (i+1))
      = (∑ i ∈ Finset.range 148, stT274 (i+1)) + stT274 149 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 148
    simpa using h
  have hprev := st274_p148
  have hstep := st274_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p150 : ((2853400951449/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT274 (i+1))
      = (∑ i ∈ Finset.range 149, stT274 (i+1)) + stT274 150 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 149
    simpa using h
  have hprev := st274_p149
  have hstep := st274_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p151 : ((2910046699659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT274 (i+1))
      = (∑ i ∈ Finset.range 150, stT274 (i+1)) + stT274 151 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 150
    simpa using h
  have hprev := st274_p150
  have hstep := st274_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p152 : ((1191432636471/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT274 (i+1))
      = (∑ i ∈ Finset.range 151, stT274 (i+1)) + stT274 152 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 151
    simpa using h
  have hprev := st274_p151
  have hstep := st274_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p153 : ((5781395798719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT274 (i+1))
      = (∑ i ∈ Finset.range 152, stT274 (i+1)) + stT274 153 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 152
    simpa using h
  have hprev := st274_p152
  have hstep := st274_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p154 : ((11442864989463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT274 (i+1))
      = (∑ i ∈ Finset.range 153, stT274 (i+1)) + stT274 154 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 153
    simpa using h
  have hprev := st274_p153
  have hstep := st274_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p155 : ((23684935293583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT274 (i+1))
      = (∑ i ∈ Finset.range 154, stT274 (i+1)) + stT274 155 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 154
    simpa using h
  have hprev := st274_p154
  have hstep := st274_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p156 : ((1180576506239/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT274 (i+1))
      = (∑ i ∈ Finset.range 155, stT274 (i+1)) + stT274 156 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 155
    simpa using h
  have hprev := st274_p155
  have hstep := st274_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p157 : ((22842695407591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT274 (i+1))
      = (∑ i ∈ Finset.range 156, stT274 (i+1)) + stT274 157 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 156
    simpa using h
  have hprev := st274_p156
  have hstep := st274_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p158 : ((4636397229613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT274 (i+1))
      = (∑ i ∈ Finset.range 157, stT274 (i+1)) + stT274 158 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 157
    simpa using h
  have hprev := st274_p157
  have hstep := st274_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p159 : ((11918557634751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT274 (i+1))
      = (∑ i ∈ Finset.range 158, stT274 (i+1)) + stT274 159 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 158
    simpa using h
  have hprev := st274_p158
  have hstep := st274_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p160 : ((11650355971681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT274 (i+1))
      = (∑ i ∈ Finset.range 159, stT274 (i+1)) + stT274 160 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 159
    simpa using h
  have hprev := st274_p159
  have hstep := st274_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p161 : ((4559950310109/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT274 (i+1))
      = (∑ i ∈ Finset.range 160, stT274 (i+1)) + stT274 161 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 160
    simpa using h
  have hprev := st274_p160
  have hstep := st274_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p162 : ((23464136341121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT274 (i+1))
      = (∑ i ∈ Finset.range 161, stT274 (i+1)) + stT274 162 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 161
    simpa using h
  have hprev := st274_p161
  have hstep := st274_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p163 : ((23803092889381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT274 (i+1))
      = (∑ i ∈ Finset.range 162, stT274 (i+1)) + stT274 163 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 162
    simpa using h
  have hprev := st274_p162
  have hstep := st274_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p164 : ((230675541157/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT274 (i+1))
      = (∑ i ∈ Finset.range 163, stT274 (i+1)) + stT274 164 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 163
    simpa using h
  have hprev := st274_p163
  have hstep := st274_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p165 : ((22876642027431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT274 (i+1))
      = (∑ i ∈ Finset.range 164, stT274 (i+1)) + stT274 165 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 164
    simpa using h
  have hprev := st274_p164
  have hstep := st274_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p166 : ((23642476217781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT274 (i+1))
      = (∑ i ∈ Finset.range 165, stT274 (i+1)) + stT274 166 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 165
    simpa using h
  have hprev := st274_p165
  have hstep := st274_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p167 : ((1185523718313/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT274 (i+1))
      = (∑ i ∈ Finset.range 166, stT274 (i+1)) + stT274 167 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 166
    simpa using h
  have hprev := st274_p166
  have hstep := st274_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p168 : ((4587824648483/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT274 (i+1))
      = (∑ i ∈ Finset.range 167, stT274 (i+1)) + stT274 168 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 167
    simpa using h
  have hprev := st274_p167
  have hstep := st274_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p169 : ((4592787412751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT274 (i+1))
      = (∑ i ∈ Finset.range 168, stT274 (i+1)) + stT274 169 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 168
    simpa using h
  have hprev := st274_p168
  have hstep := st274_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p170 : ((23728528844103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT274 (i+1))
      = (∑ i ∈ Finset.range 169, stT274 (i+1)) + stT274 170 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 169
    simpa using h
  have hprev := st274_p169
  have hstep := st274_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p171 : ((23641291880663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT274 (i+1))
      = (∑ i ∈ Finset.range 170, stT274 (i+1)) + stT274 171 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 170
    simpa using h
  have hprev := st274_p170
  have hstep := st274_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p172 : ((11443171874449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT274 (i+1))
      = (∑ i ∈ Finset.range 171, stT274 (i+1)) + stT274 172 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 171
    simpa using h
  have hprev := st274_p171
  have hstep := st274_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p173 : ((23006498430013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT274 (i+1))
      = (∑ i ∈ Finset.range 172, stT274 (i+1)) + stT274 173 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 172
    simpa using h
  have hprev := st274_p172
  have hstep := st274_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p174 : ((23753985332307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT274 (i+1))
      = (∑ i ∈ Finset.range 173, stT274 (i+1)) + stT274 174 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 173
    simpa using h
  have hprev := st274_p173
  have hstep := st274_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p175 : ((945142826551/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT274 (i+1))
      = (∑ i ∈ Finset.range 174, stT274 (i+1)) + stT274 175 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 174
    simpa using h
  have hprev := st274_p174
  have hstep := st274_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p176 : ((22884034501873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT274 (i+1))
      = (∑ i ∈ Finset.range 175, stT274 (i+1)) + stT274 176 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 175
    simpa using h
  have hprev := st274_p175
  have hstep := st274_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p177 : ((4597585703057/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT274 (i+1))
      = (∑ i ∈ Finset.range 176, stT274 (i+1)) + stT274 177 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 176
    simpa using h
  have hprev := st274_p176
  have hstep := st274_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p178 : ((11866380352723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT274 (i+1))
      = (∑ i ∈ Finset.range 177, stT274 (i+1)) + stT274 178 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 177
    simpa using h
  have hprev := st274_p177
  have hstep := st274_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p179 : ((11838055144349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT274 (i+1))
      = (∑ i ∈ Finset.range 178, stT274 (i+1)) + stT274 179 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 178
    simpa using h
  have hprev := st274_p178
  have hstep := st274_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p180 : ((11465542986059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT274 (i+1))
      = (∑ i ∈ Finset.range 179, stT274 (i+1)) + stT274 180 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 179
    simpa using h
  have hprev := st274_p179
  have hstep := st274_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p181 : ((22915211420803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT274 (i+1))
      = (∑ i ∈ Finset.range 180, stT274 (i+1)) + stT274 181 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 180
    simpa using h
  have hprev := st274_p180
  have hstep := st274_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p182 : ((11826951926501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT274 (i+1))
      = (∑ i ∈ Finset.range 181, stT274 (i+1)) + stT274 182 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 181
    simpa using h
  have hprev := st274_p181
  have hstep := st274_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p183 : ((23765714725357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT274 (i+1))
      = (∑ i ∈ Finset.range 182, stT274 (i+1)) + stT274 183 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 182
    simpa using h
  have hprev := st274_p182
  have hstep := st274_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p184 : ((23047796036637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT274 (i+1))
      = (∑ i ∈ Finset.range 183, stT274 (i+1)) + stT274 184 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 183
    simpa using h
  have hprev := st274_p183
  have hstep := st274_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p185 : ((22819849978037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT274 (i+1))
      = (∑ i ∈ Finset.range 184, stT274 (i+1)) + stT274 185 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 184
    simpa using h
  have hprev := st274_p184
  have hstep := st274_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p186 : ((5873149922413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT274 (i+1))
      = (∑ i ∈ Finset.range 185, stT274 (i+1)) + stT274 186 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 185
    simpa using h
  have hprev := st274_p185
  have hstep := st274_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p187 : ((5962469495491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT274 (i+1))
      = (∑ i ∈ Finset.range 186, stT274 (i+1)) + stT274 187 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 186
    simpa using h
  have hprev := st274_p186
  have hstep := st274_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p188 : ((2907031398933/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT274 (i+1))
      = (∑ i ∈ Finset.range 187, stT274 (i+1)) + stT274 188 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 187
    simpa using h
  have hprev := st274_p187
  have hstep := st274_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p189 : ((5691814948107/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT274 (i+1))
      = (∑ i ∈ Finset.range 188, stT274 (i+1)) + stT274 189 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 188
    simpa using h
  have hprev := st274_p188
  have hstep := st274_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p190 : ((1161970413947/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT274 (i+1))
      = (∑ i ∈ Finset.range 189, stT274 (i+1)) + stT274 190 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 189
    simpa using h
  have hprev := st274_p189
  have hstep := st274_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p191 : ((11923046982129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT274 (i+1))
      = (∑ i ∈ Finset.range 190, stT274 (i+1)) + stT274 191 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 190
    simpa using h
  have hprev := st274_p190
  have hstep := st274_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p192 : ((11770552503509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT274 (i+1))
      = (∑ i ∈ Finset.range 191, stT274 (i+1)) + stT274 192 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 191
    simpa using h
  have hprev := st274_p191
  have hstep := st274_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p193 : ((11425535697009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT274 (i+1))
      = (∑ i ∈ Finset.range 192, stT274 (i+1)) + stT274 193 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 192
    simpa using h
  have hprev := st274_p192
  have hstep := st274_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p194 : ((2868376066471/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT274 (i+1))
      = (∑ i ∈ Finset.range 193, stT274 (i+1)) + stT274 194 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 193
    simpa using h
  have hprev := st274_p193
  have hstep := st274_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p195 : ((11831403362747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT274 (i+1))
      = (∑ i ∈ Finset.range 194, stT274 (i+1)) + stT274 195 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 194
    simpa using h
  have hprev := st274_p194
  have hstep := st274_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p196 : ((11901370435637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT274 (i+1))
      = (∑ i ∈ Finset.range 195, stT274 (i+1)) + stT274 196 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 195
    simpa using h
  have hprev := st274_p195
  have hstep := st274_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p197 : ((23139385484601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT274 (i+1))
      = (∑ i ∈ Finset.range 196, stT274 (i+1)) + stT274 197 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 196
    simpa using h
  have hprev := st274_p196
  have hstep := st274_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p198 : ((22763617300761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT274 (i+1))
      = (∑ i ∈ Finset.range 197, stT274 (i+1)) + stT274 198 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 197
    simpa using h
  have hprev := st274_p197
  have hstep := st274_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p199 : ((4656692768003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT274 (i+1))
      = (∑ i ∈ Finset.range 198, stT274 (i+1)) + stT274 199 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 198
    simpa using h
  have hprev := st274_p198
  have hstep := st274_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p200 : ((23856486278977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT274 (i+1))
      = (∑ i ∈ Finset.range 199, stT274 (i+1)) + stT274 200 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 199
    simpa using h
  have hprev := st274_p199
  have hstep := st274_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p201 : ((4713546064561/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT274 (i+1))
      = (∑ i ∈ Finset.range 200, stT274 (i+1)) + stT274 201 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 200
    simpa using h
  have hprev := st274_p200
  have hstep := st274_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p202 : ((22879657916273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT274 (i+1))
      = (∑ i ∈ Finset.range 201, stT274 (i+1)) + stT274 202 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 201
    simpa using h
  have hprev := st274_p201
  have hstep := st274_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p203 : ((914988503583/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT274 (i+1))
      = (∑ i ∈ Finset.range 202, stT274 (i+1)) + stT274 203 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 202
    simpa using h
  have hprev := st274_p202
  have hstep := st274_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p204 : ((4711232610483/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT274 (i+1))
      = (∑ i ∈ Finset.range 203, stT274 (i+1)) + stT274 204 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 203
    simpa using h
  have hprev := st274_p203
  have hstep := st274_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p205 : ((954705172311/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT274 (i+1))
      = (∑ i ∈ Finset.range 204, stT274 (i+1)) + stT274 205 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 204
    simpa using h
  have hprev := st274_p204
  have hstep := st274_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p206 : ((23334590870873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT274 (i+1))
      = (∑ i ∈ Finset.range 205, stT274 (i+1)) + stT274 206 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 205
    simpa using h
  have hprev := st274_p205
  have hstep := st274_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p207 : ((22771761042143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT274 (i+1))
      = (∑ i ∈ Finset.range 206, stT274 (i+1)) + stT274 207 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 206
    simpa using h
  have hprev := st274_p206
  have hstep := st274_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p208 : ((11513429972509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT274 (i+1))
      = (∑ i ∈ Finset.range 207, stT274 (i+1)) + stT274 208 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 207
    simpa using h
  have hprev := st274_p207
  have hstep := st274_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p209 : ((474271014359/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT274 (i+1))
      = (∑ i ∈ Finset.range 208, stT274 (i+1)) + stT274 209 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 208
    simpa using h
  have hprev := st274_p208
  have hstep := st274_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p210 : ((595291983527/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT274 (i+1))
      = (∑ i ∈ Finset.range 209, stT274 (i+1)) + stT274 210 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 209
    simpa using h
  have hprev := st274_p209
  have hstep := st274_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p211 : ((4636157158951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT274 (i+1))
      = (∑ i ∈ Finset.range 210, stT274 (i+1)) + stT274 211 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 210
    simpa using h
  have hprev := st274_p210
  have hstep := st274_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p212 : ((22745079345161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT274 (i+1))
      = (∑ i ∈ Finset.range 211, stT274 (i+1)) + stT274 212 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 211
    simpa using h
  have hprev := st274_p211
  have hstep := st274_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p213 : ((23133203402573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT274 (i+1))
      = (∑ i ∈ Finset.range 212, stT274 (i+1)) + stT274 213 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 212
    simpa using h
  have hprev := st274_p212
  have hstep := st274_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p214 : ((2972894075331/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT274 (i+1))
      = (∑ i ∈ Finset.range 213, stT274 (i+1)) + stT274 214 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 213
    simpa using h
  have hprev := st274_p213
  have hstep := st274_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p215 : ((5942125155517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT274 (i+1))
      = (∑ i ∈ Finset.range 214, stT274 (i+1)) + stT274 215 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 214
    simpa using h
  have hprev := st274_p214
  have hstep := st274_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p216 : ((722317375127/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT274 (i+1))
      = (∑ i ∈ Finset.range 215, stT274 (i+1)) + stT274 216 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 215
    simpa using h
  have hprev := st274_p215
  have hstep := st274_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p217 : ((1421270941889/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT274 (i+1))
      = (∑ i ∈ Finset.range 216, stT274 (i+1)) + stT274 217 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 216
    simpa using h
  have hprev := st274_p216
  have hstep := st274_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p218 : ((23164412331979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT274 (i+1))
      = (∑ i ∈ Finset.range 217, stT274 (i+1)) + stT274 218 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 217
    simpa using h
  have hprev := st274_p217
  have hstep := st274_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p219 : ((5949206789293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT274 (i+1))
      = (∑ i ∈ Finset.range 218, stT274 (i+1)) + stT274 219 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 218
    simpa using h
  have hprev := st274_p218
  have hstep := st274_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p220 : ((5942900491043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT274 (i+1))
      = (∑ i ∈ Finset.range 219, stT274 (i+1)) + stT274 220 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 219
    simpa using h
  have hprev := st274_p219
  have hstep := st274_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p221 : ((23127133470389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT274 (i+1))
      = (∑ i ∈ Finset.range 220, stT274 (i+1)) + stT274 221 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 220
    simpa using h
  have hprev := st274_p220
  have hstep := st274_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p222 : ((909385580579/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT274 (i+1))
      = (∑ i ∈ Finset.range 221, stT274 (i+1)) + stT274 222 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 221
    simpa using h
  have hprev := st274_p221
  have hstep := st274_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p223 : ((11558259120379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT274 (i+1))
      = (∑ i ∈ Finset.range 222, stT274 (i+1)) + stT274 223 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 222
    simpa using h
  have hprev := st274_p222
  have hstep := st274_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p224 : ((2970228386211/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT274 (i+1))
      = (∑ i ∈ Finset.range 223, stT274 (i+1)) + stT274 224 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 223
    simpa using h
  have hprev := st274_p223
  have hstep := st274_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p225 : ((11910271182153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT274 (i+1))
      = (∑ i ∈ Finset.range 224, stT274 (i+1)) + stT274 225 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 224
    simpa using h
  have hprev := st274_p224
  have hstep := st274_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p226 : ((23219805046251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT274 (i+1))
      = (∑ i ∈ Finset.range 225, stT274 (i+1)) + stT274 226 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 225
    simpa using h
  have hprev := st274_p225
  have hstep := st274_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p227 : ((22741321104859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT274 (i+1))
      = (∑ i ∈ Finset.range 226, stT274 (i+1)) + stT274 227 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 226
    simpa using h
  have hprev := st274_p226
  have hstep := st274_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p228 : ((22998792906743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT274 (i+1))
      = (∑ i ∈ Finset.range 227, stT274 (i+1)) + stT274 228 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 227
    simpa using h
  have hprev := st274_p227
  have hstep := st274_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p229 : ((23659324772549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT274 (i+1))
      = (∑ i ∈ Finset.range 228, stT274 (i+1)) + stT274 229 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 228
    simpa using h
  have hprev := st274_p228
  have hstep := st274_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p230 : ((23884898670549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT274 (i+1))
      = (∑ i ∈ Finset.range 229, stT274 (i+1)) + stT274 230 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 229
    simpa using h
  have hprev := st274_p229
  have hstep := st274_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p231 : ((23395138282357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT274 (i+1))
      = (∑ i ∈ Finset.range 230, stT274 (i+1)) + stT274 231 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 230
    simpa using h
  have hprev := st274_p230
  have hstep := st274_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p232 : ((22804588161923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT274 (i+1))
      = (∑ i ∈ Finset.range 231, stT274 (i+1)) + stT274 232 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 231
    simpa using h
  have hprev := st274_p231
  have hstep := st274_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p233 : ((22843836461033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT274 (i+1))
      = (∑ i ∈ Finset.range 232, stT274 (i+1)) + stT274 233 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 232
    simpa using h
  have hprev := st274_p232
  have hstep := st274_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p234 : ((23460678808393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT274 (i+1))
      = (∑ i ∈ Finset.range 233, stT274 (i+1)) + stT274 234 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 233
    simpa using h
  have hprev := st274_p233
  have hstep := st274_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p235 : ((4780070750269/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT274 (i+1))
      = (∑ i ∈ Finset.range 234, stT274 (i+1)) + stT274 235 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 234
    simpa using h
  have hprev := st274_p234
  have hstep := st274_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p236 : ((590815941209/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT274 (i+1))
      = (∑ i ∈ Finset.range 235, stT274 (i+1)) + stT274 236 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 235
    simpa using h
  have hprev := st274_p235
  have hstep := st274_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p237 : ((459661573821/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT274 (i+1))
      = (∑ i ∈ Finset.range 236, stT274 (i+1)) + stT274 237 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 236
    simpa using h
  have hprev := st274_p236
  have hstep := st274_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p238 : ((11363652261447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT274 (i+1))
      = (∑ i ∈ Finset.range 237, stT274 (i+1)) + stT274 238 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 237
    simpa using h
  have hprev := st274_p237
  have hstep := st274_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p239 : ((723906289931/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT274 (i+1))
      = (∑ i ∈ Finset.range 238, stT274 (i+1)) + stT274 239 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 238
    simpa using h
  have hprev := st274_p238
  have hstep := st274_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p240 : ((23778393839/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT274 (i+1))
      = (∑ i ∈ Finset.range 239, stT274 (i+1)) + stT274 240 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 239
    simpa using h
  have hprev := st274_p239
  have hstep := st274_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p241 : ((5963061420061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT274 (i+1))
      = (∑ i ∈ Finset.range 240, stT274 (i+1)) + stT274 241 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 240
    simpa using h
  have hprev := st274_p240
  have hstep := st274_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p242 : ((23304582564769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT274 (i+1))
      = (∑ i ∈ Finset.range 241, stT274 (i+1)) + stT274 242 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 241
    simpa using h
  have hprev := st274_p241
  have hstep := st274_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p243 : ((11383755435529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT274 (i+1))
      = (∑ i ∈ Finset.range 242, stT274 (i+1)) + stT274 243 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 242
    simpa using h
  have hprev := st274_p242
  have hstep := st274_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p244 : ((2285249401669/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT274 (i+1))
      = (∑ i ∈ Finset.range 243, stT274 (i+1)) + stT274 244 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 243
    simpa using h
  have hprev := st274_p243
  have hstep := st274_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p245 : ((11729757190789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT274 (i+1))
      = (∑ i ∈ Finset.range 244, stT274 (i+1)) + stT274 245 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 244
    simpa using h
  have hprev := st274_p244
  have hstep := st274_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p246 : ((11952039774701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT274 (i+1))
      = (∑ i ∈ Finset.range 245, stT274 (i+1)) + stT274 246 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 245
    simpa using h
  have hprev := st274_p245
  have hstep := st274_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p247 : ((11845955794361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT274 (i+1))
      = (∑ i ∈ Finset.range 246, stT274 (i+1)) + stT274 247 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 246
    simpa using h
  have hprev := st274_p246
  have hstep := st274_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p248 : ((2882717550791/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT274 (i+1))
      = (∑ i ∈ Finset.range 247, stT274 (i+1)) + stT274 248 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 247
    simpa using h
  have hprev := st274_p247
  have hstep := st274_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p249 : ((22708069257153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT274 (i+1))
      = (∑ i ∈ Finset.range 248, stT274 (i+1)) + stT274 249 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 248
    simpa using h
  have hprev := st274_p248
  have hstep := st274_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_p250 : ((23014691030613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT274 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT274 (i+1))
      = (∑ i ∈ Finset.range 249, stT274 (i+1)) + stT274 250 := by
    have h := Finset.sum_range_succ (fun i => stT274 (i+1)) 249
    simpa using h
  have hprev := st274_p249
  have hstep := st274_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st274_s250 :
    |Real.sin (((274 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))
      - ((-874591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -2661477/10000000) (δ := 13771/1000000000) (ψ := -18923/62500) 274 241
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 274`** (evaluated boundary). -/
theorem station_274_sign : hardyG ((((274:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 274 250 (by norm_num) (by norm_num)
    ((-18923/62500 : ℚ) : ℝ)
  have hchain := st274_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT274 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((274 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-18923/62500 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st274_c250
  have hsinb := abs_le.mp st274_s250
  have hbdy_lo : ((15139820240499/300305000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((274 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18923/62500 : ℚ) : ℝ))) / 2
          - ((((274:ℕ)):ℝ))
            * Real.sin (((274 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-18923/62500 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((274:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((274:ℝ) * Real.log (250:ℝ) - ((-18923/62500 : ℚ) : ℝ))) / 2
        - ((274:ℝ)) * Real.sin ((274:ℝ) * Real.log (250:ℝ) - ((-18923/62500 : ℚ) : ℝ))
        ≥ ((119690889/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((274:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((119690889/500000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((119690889/500000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((119690889/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((274:ℕ)):ℝ))+1) * (((((274:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((10258357263/6250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((23014691030613/10000000000000 : ℚ) : ℝ) + ((15139820240499/300305000000000 : ℚ) : ℝ)
      - ((10258357263/6250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-18923/62500 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((274:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-18923/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((274:ℕ)):ℝ)))).re
      - Real.sin ((-18923/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((274:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((274:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((274:ℕ)):ℝ))
      = (((((274:ℕ)):ℝ)) * (Real.log ((((274:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((274:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_274
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
  have hθwin : |(((-18923/62500 : ℚ) : ℝ) + ((61:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((274:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((274:ℕ)):ℝ)))
    (φ := ((-18923/62500 : ℚ) : ℝ) + ((61:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-18923/62500 : ℚ) : ℝ) + ((61:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-18923/62500 : ℚ)) : ℝ) - Real.pi) + ((61:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-18923/62500 : ℚ)) : ℝ) - Real.pi) 61).1,
    (cos_sin_shift ((((-18923/62500 : ℚ)) : ℝ) - Real.pi) 61).2]
  exact cos_sin_flip ((-18923/62500 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_274_sign
end AxiomAudit
