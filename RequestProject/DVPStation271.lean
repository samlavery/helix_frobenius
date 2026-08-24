import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 271` (rung-280.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT271 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((271 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((162891/500000 : ℚ) : ℝ))

theorem st271_c1 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((947401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162891/2000000) (δ := 1/1000000000) (ψ := 162891/500000) 271 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t1 : ((947351/1000000 : ℚ) : ℝ) ≤ stT271 1 := by
  have hc : ((947351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((947351/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((947351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c2 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((279149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2446159/10000000) (δ := 6793/500000000) (ψ := 162891/500000) 271 30
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t2 : ((493426126327/1250000000000 : ℚ) : ℝ) ≤ stT271 2 := by
  have hc : ((69781/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493426126327/1250000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((69781/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c3 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-61853/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5221071/10000000) (δ := 13639/1000000000) (ψ := 162891/500000) 271 47
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t3 : ((-1428578261811/5000000000000 : ℚ) : ℝ) ≤ stT271 3 := by
  have hc : ((-247437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1428578261811/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-247437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c4 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-60299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4077829/10000000) (δ := 13571/1000000000) (ψ := 162891/500000) 271 60
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t4 : ((-301745060349/10000000000000 : ℚ) : ℝ) ≤ stT271 4 := by
  have hc : ((-60349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301745060349/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-60349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c5 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-660377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5730291/10000000) (δ := 13697/1000000000) (ψ := 162891/500000) 271 69
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t5 : ((-369189920259/1250000000000 : ℚ) : ℝ) ≤ stT271 5 := by
  have hc : ((-660427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369189920259/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-660427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c6 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((67313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3589401/10000000) (δ := 6827/500000000) (ψ := 162891/500000) 271 77
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t6 : ((17168878051/312500000000 : ℚ) : ℝ) ≤ stT271 6 := by
  have hc : ((8411/62500 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17168878051/312500000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((8411/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c7 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((89591/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1929243/10000000) (δ := 6799/500000000) (ψ := 162891/500000) 271 84
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t7 : ((338598462829/1250000000000 : ℚ) : ℝ) ≤ stT271 7 := by
  have hc : ((358339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338598462829/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((358339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c8 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-163527/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5709499/10000000) (δ := 2711/200000000) (ψ := 162891/500000) 271 90
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t8 : ((-578199462593/2500000000000 : ℚ) : ℝ) ≤ stT271 8 := by
  have hc : ((-327079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-578199462593/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-327079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c9 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-208203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4451333/10000000) (δ := 13619/1000000000) (ψ := 162891/500000) 271 95
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t9 : ((-347088402751/5000000000000 : ℚ) : ℝ) ≤ stT271 9 := by
  have hc : ((-208253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347088402751/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-208253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c10 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-68571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4098553/10000000) (δ := 3403/250000000) (ψ := 162891/500000) 271 99
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t10 : ((-108499339319/5000000000000 : ℚ) : ℝ) ≤ stT271 10 := by
  have hc : ((-68621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108499339319/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-68621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c11 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-692499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9124/15625) (δ := 6831/500000000) (ψ := 162891/500000) 271 103
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t11 : ((-1044057092793/5000000000000 : ℚ) : ℝ) ≤ stT271 11 := by
  have hc : ((-692549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1044057092793/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-692549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c12 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((141747/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1957731/10000000) (δ := 1367/100000000) (ψ := 162891/500000) 271 107
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t12 : ((409159426487/2000000000000 : ℚ) : ℝ) ≤ stT271 12 := by
  have hc : ((141737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409159426487/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((141737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c13 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-442683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6645193/10000000) (δ := 6799/500000000) (ψ := 162891/500000) 271 111
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t13 : ((-306962770177/1250000000000 : ℚ) : ℝ) ≤ stT271 13 := by
  have hc : ((-110677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306962770177/1250000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-110677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c14 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((36477/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3560913/10000000) (δ := 13583/1000000000) (ψ := 162891/500000) 271 114
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t14 : ((48727730137/1250000000000 : ℚ) : ℝ) ≤ stT271 14 := by
  have hc : ((72929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48727730137/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((72929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c15 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-6049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3942113/10000000) (δ := 13561/1000000000) (ψ := 162891/500000) 271 117
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t15 : ((-15747550911/10000000000000 : ℚ) : ℝ) ≤ stT271 15 := by
  have hc : ((-6099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15747550911/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-6099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c16 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-244759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7341169/10000000) (δ := 13563/1000000000) (ψ := 162891/500000) 271 120
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t16 : ((-1223857989543/5000000000000 : ℚ) : ℝ) ≤ stT271 16 := by
  have hc : ((-489543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1223857989543/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-489543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c17 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((600693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2316071/10000000) (δ := 13577/1000000000) (ψ := 162891/500000) 271 122
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t17 : ((364193275977/2500000000000 : ℚ) : ℝ) ≤ stT271 17 := by
  have hc : ((600643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364193275977/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((600643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c18 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-759409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6083003/10000000) (δ := 3401/250000000) (ψ := 162891/500000) 271 125
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t18 : ((-1790062330557/10000000000000 : ℚ) : ℝ) ≤ stT271 18 := by
  have hc : ((-759459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1790062330557/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-759459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c19 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((37611/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -868401/10000000) (δ := 13713/1000000000) (ψ := 162891/500000) 271 127
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t19 : ((86280950613/400000000000 : ℚ) : ℝ) ≤ stT271 19 := by
  have hc : ((37609/40000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86280950613/400000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((37609/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c20 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((551401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2466883/10000000) (δ := 3407/250000000) (ψ := 162891/500000) 271 129
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t20 : ((1232857776517/10000000000000 : ℚ) : ℝ) ≤ stT271 20 := by
  have hc : ((551351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1232857776517/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((551351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c21 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-71669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4106317/10000000) (δ := 6821/500000000) (ψ := 162891/500000) 271 131
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t21 : ((-156503695701/10000000000000 : ℚ) : ℝ) ≤ stT271 21 := by
  have hc : ((-71719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156503695701/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-71719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c22 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-28011/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420769/1000000) (δ := 13647/1000000000) (ψ := 162891/500000) 271 133
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t22 : ((-14936581547/625000000000 : ℚ) : ℝ) ≤ stT271 22 := by
  have hc : ((-56047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14936581547/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-56047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c23 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((49557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1453929/5000000) (δ := 213/15625000) (ψ := 162891/500000) 271 135
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t23 : ((51660224529/625000000000 : ℚ) : ℝ) ≤ stT271 23 := by
  have hc : ((198203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51660224529/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((198203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c24 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((991507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326061/10000000) (δ := 2737/200000000) (ψ := 162891/500000) 271 137
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t24 : ((2023802678137/10000000000000 : ℚ) : ℝ) ≤ stT271 24 := by
  have hc : ((991457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2023802678137/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((991457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c25 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((24541/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3432961/10000000) (δ := 3401/250000000) (ψ := 162891/500000) 271 139
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t25 : ((98139/2500000 : ℚ) : ℝ) ≤ stT271 25 := by
  have hc : ((98139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98139/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((98139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c26 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-15402/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74311/100000) (δ := 3399/250000000) (ψ := 162891/500000) 271 140
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t26 : ((-483317588509/2500000000000 : ℚ) : ℝ) ≤ stT271 26 := by
  have hc : ((-492889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483317588509/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-492889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c27 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((100731/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1584227/10000000) (δ := 13621/1000000000) (ψ := 162891/500000) 271 142
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t27 : ((1550758251/10000000000 : ℚ) : ℝ) ≤ stT271 27 := by
  have hc : ((402899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1550758251/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((402899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c28 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-48489/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5192583/10000000) (δ := 53/3906250) (ψ := 162891/500000) 271 144
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t28 : ((-45822538281/500000000000 : ℚ) : ℝ) ≤ stT271 28 := by
  have hc : ((-24247/50000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45822538281/500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-24247/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c29 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((204461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287381/1000000) (δ := 13743/1000000000) (ψ := 162891/500000) 271 145
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t29 : ((94907010877/1250000000000 : ℚ) : ℝ) ≤ stT271 29 := by
  have hc : ((51109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94907010877/1250000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((51109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c30 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-153031/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5573851/10000000) (δ := 6823/500000000) (ψ := 162891/500000) 271 147
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t30 : ((-279417945777/2500000000000 : ℚ) : ℝ) ≤ stT271 30 := by
  have hc : ((-306087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279417945777/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-306087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c31 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((186223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 933343/10000000) (δ := 13639/1000000000) (ψ := 162891/500000) 271 148
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t31 : ((334448417289/2000000000000 : ℚ) : ℝ) ≤ stT271 31 := by
  have hc : ((186213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334448417289/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((186213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c32 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-901513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1683781/2500000) (δ := 213/15625000) (ψ := 162891/500000) 271 149
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t32 : ((-1593753319821/10000000000000 : ℚ) : ℝ) ≤ stT271 32 := by
  have hc : ((-901563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1593753319821/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-901563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c33 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((3757/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3833043/10000000) (δ := 6843/500000000) (ψ := 162891/500000) 271 151
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t33 : ((102052993/15625000000 : ℚ) : ℝ) ≤ stT271 33 := by
  have hc : ((469/12500 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102052993/15625000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((469/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c34 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((962761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 684401/10000000) (δ := 13593/1000000000) (ψ := 162891/500000) 271 152
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t34 : ((330206984867/2000000000000 : ℚ) : ℝ) ≤ stT271 34 := by
  have hc : ((962711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330206984867/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((962711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c35 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-271923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4615469/10000000) (δ := 17/1250000) (ψ := 162891/500000) 271 153
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t35 : ((-459718409657/10000000000000 : ℚ) : ℝ) ≤ stT271 35 := by
  have hc : ((-271973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459718409657/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-271973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c36 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-62403/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7714673/10000000) (δ := 13589/1000000000) (ψ := 162891/500000) 271 155
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t36 : ((-832081833083/5000000000000 : ℚ) : ℝ) ≤ stT271 36 := by
  have hc : ((-499249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-832081833083/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-499249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c37 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-364531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2429907/5000000) (δ := 13681/1000000000) (ψ := 162891/500000) 271 156
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t37 : ((-59936751819/1000000000000 : ℚ) : ℝ) ≤ stT271 37 := by
  have hc : ((-364581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59936751819/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-364581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c38 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((270139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2500071/10000000) (δ := 13729/1000000000) (ψ := 162891/500000) 271 157
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t38 : ((109545678099/1250000000000 : ℚ) : ℝ) ≤ stT271 38 := by
  have hc : ((135057/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109545678099/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((135057/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c39 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((194083/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -609633/10000000) (δ := 1717/125000000) (ψ := 162891/500000) 271 158
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t39 : ((310765407513/2000000000000 : ℚ) : ℝ) ≤ stT271 39 := by
  have hc : ((194073/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310765407513/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((194073/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c40 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((944711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835213/10000000) (δ := 13643/1000000000) (ψ := 162891/500000) 271 159
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t40 : ((746819702109/5000000000000 : ℚ) : ℝ) ≤ stT271 40 := by
  have hc : ((944661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((746819702109/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((944661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c41 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((736717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 928243/5000000) (δ := 13553/1000000000) (ψ := 162891/500000) 271 160
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t41 : ((1150480110579/10000000000000 : ℚ) : ℝ) ≤ stT271 41 := by
  have hc : ((736667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1150480110579/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((736667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c42 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((68601/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2474647/10000000) (δ := 13657/1000000000) (ψ := 162891/500000) 271 161
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t42 : ((423375851507/5000000000000 : ℚ) : ℝ) ≤ stT271 42 := by
  have hc : ((274379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((423375851507/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((274379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c43 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((468293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2708597/10000000) (δ := 6819/500000000) (ψ := 162891/500000) 271 162
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t43 : ((142812710271/2000000000000 : ℚ) : ℝ) ≤ stT271 43 := by
  have hc : ((468243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142812710271/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((468243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c44 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((514469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128801/500000) (δ := 13631/1000000000) (ψ := 162891/500000) 271 163
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t44 : ((193878862491/2500000000000 : ℚ) : ℝ) ≤ stT271 44 := by
  have hc : ((514419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193878862491/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((514419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c45 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((669433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2093379/10000000) (δ := 13579/1000000000) (ψ := 162891/500000) 271 164
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t45 : ((997856601313/10000000000000 : ℚ) : ℝ) ≤ stT271 45 := by
  have hc : ((669383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((997856601313/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((669383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c46 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((436263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31903/250000) (δ := 13717/1000000000) (ψ := 162891/500000) 271 165
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t46 : ((321598797861/2500000000000 : ℚ) : ℝ) ≤ stT271 46 := by
  have hc : ((218119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321598797861/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((218119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c47 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((499231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5547/400000) (δ := 1371/100000000) (ψ := 162891/500000) 271 166
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t47 : ((364083166347/2500000000000 : ℚ) : ℝ) ≤ stT271 47 := by
  have hc : ((249603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364083166347/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((249603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c48 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((433351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1305609/10000000) (δ := 137/10000000) (ψ := 162891/500000) 271 167
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t48 : ((2501807661/20000000000 : ℚ) : ℝ) ≤ stT271 48 := by
  have hc : ((216663/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2501807661/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((216663/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c49 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((172937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -608813/2000000) (δ := 2739/200000000) (ψ := 162891/500000) 271 168
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t49 : ((15438566797/312500000000 : ℚ) : ℝ) ≤ stT271 49 := by
  have hc : ((10807/31250 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15438566797/312500000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((10807/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c50 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-439513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5064631/10000000) (δ := 3397/250000000) (ψ := 162891/500000) 271 169
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t50 : ((-310818074241/5000000000000 : ℚ) : ℝ) ≤ stT271 50 := by
  have hc : ((-439563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310818074241/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-439563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c51 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-980253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7356333/10000000) (δ := 13681/1000000000) (ψ := 162891/500000) 271 170
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t51 : ((-1372699665143/10000000000000 : ℚ) : ℝ) ≤ stT271 51 := by
  have hc : ((-980303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1372699665143/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-980303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c52 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-680889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 579943/1000000) (δ := 13581/1000000000) (ψ := 162891/500000) 271 170
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t52 : ((-944292839189/10000000000000 : ℚ) : ℝ) ≤ stT271 52 := by
  have hc : ((-680939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-944292839189/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-680939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c53 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((363617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1498311/5000000) (δ := 6837/500000000) (ψ := 162891/500000) 271 171
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t53 : ((99879489807/2000000000000 : ℚ) : ℝ) ≤ stT271 53 := by
  have hc : ((363567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99879489807/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((363567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c54 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((49991/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47443/10000000) (δ := 3409/250000000) (ψ := 162891/500000) 271 172
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t54 : ((136051400979/1000000000000 : ℚ) : ℝ) ≤ stT271 54 := by
  have hc : ((99977/100000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136051400979/1000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((99977/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c55 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((238907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3323891/10000000) (δ := 3411/250000000) (ψ := 162891/500000) 271 173
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t55 : ((322074539943/10000000000000 : ℚ) : ℝ) ≤ stT271 55 := by
  have hc : ((238857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322074539943/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((238857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c56 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-114547/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6824321/10000000) (δ := 3413/250000000) (ψ := 162891/500000) 271 174
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t56 : ((-612313239391/5000000000000 : ℚ) : ℝ) ≤ stT271 56 := by
  have hc : ((-458213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-612313239391/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-458213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c57 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-47597/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2583579/5000000) (δ := 3413/250000000) (ψ := 162891/500000) 271 174
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t57 : ((-31525209933/500000000000 : ℚ) : ℝ) ≤ stT271 57 := by
  have hc : ((-23801/50000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31525209933/500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-23801/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c58 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((439543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1242139/10000000) (δ := 2749/200000000) (ψ := 162891/500000) 271 175
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t58 : ((36069703947/312500000000 : ℚ) : ℝ) ≤ stT271 58 := by
  have hc : ((219759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36069703947/312500000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((219759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c59 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((50633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180273/625000) (δ := 6819/500000000) (ψ := 162891/500000) 271 176
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t59 : ((263641635723/5000000000000 : ℚ) : ℝ) ≤ stT271 59 := by
  have hc : ((202507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263641635723/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((202507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c60 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-241637/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7205521/10000000) (δ := 13631/1000000000) (ψ := 162891/500000) 271 177
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t60 : ((-124787318501/1000000000000 : ℚ) : ℝ) ≤ stT271 60 := by
  have hc : ((-483299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124787318501/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-483299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c61 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-26433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99827/250000) (δ := 3393/250000000) (ψ := 162891/500000) 271 177
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t61 : ((-33908012227/10000000000000 : ℚ) : ℝ) ≤ stT271 61 := by
  have hc : ((-26483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33908012227/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-26483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c62 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((961233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139679/2000000) (δ := 3431/250000000) (ψ := 162891/500000) 271 178
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t62 : ((1220703371183/10000000000000 : ℚ) : ℝ) ≤ stT271 62 := by
  have hc : ((961183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1220703371183/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((961183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c63 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-121933/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5566087/10000000) (δ := 851/62500000) (ψ := 162891/500000) 271 179
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t63 : ((-76816895363/1000000000000 : ℚ) : ℝ) ≤ stT271 63 := by
  have hc : ((-121943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76816895363/1000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-121943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c64 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-56673/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2551693/5000000) (δ := 3429/250000000) (ψ := 162891/500000) 271 179
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t64 : ((-283396476717/5000000000000 : ℚ) : ℝ) ≤ stT271 64 := by
  have hc : ((-226717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283396476717/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-226717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c65 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((124899/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100481/10000000) (δ := 6847/500000000) (ψ := 162891/500000) 271 180
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t65 : ((619641391137/5000000000000 : ℚ) : ℝ) ≤ stT271 65 := by
  have hc : ((499571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((619641391137/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((499571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c66 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-577031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5464713/10000000) (δ := 13701/1000000000) (ψ := 162891/500000) 271 181
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t66 : ((-142067531823/2000000000000 : ℚ) : ℝ) ≤ stT271 66 := by
  have hc : ((-577081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142067531823/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-577081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c67 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-313227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 590433/1250000) (δ := 13601/1000000000) (ψ := 162891/500000) 271 181
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t67 : ((-76545788903/2000000000000 : ℚ) : ℝ) ≤ stT271 67 := by
  have hc : ((-313277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76545788903/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-313277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c68 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((929069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -947269/10000000) (δ := 1701/125000000) (ψ := 162891/500000) 271 182
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t68 : ((563300451441/5000000000000 : ℚ) : ℝ) ≤ stT271 68 := by
  have hc : ((929019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563300451441/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((929019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c69 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-906543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1352909/2000000) (δ := 2743/200000000) (ψ := 162891/500000) 271 183
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t69 : ((-1091410142387/10000000000000 : ℚ) : ℝ) ≤ stT271 69 := by
  have hc : ((-906593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1091410142387/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-906593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c70 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((36839/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2983799/10000000) (δ := 2723/200000000) (ψ := 162891/500000) 271 183
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t70 : ((5503128519/125000000000 : ℚ) : ℝ) ≤ stT271 70 := by
  have hc : ((18417/50000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5503128519/125000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((18417/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c71 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((159729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1557049/5000000) (δ := 679/50000000) (ψ := 162891/500000) 271 184
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t71 : ((23691709103/625000000000 : ℚ) : ℝ) ≤ stT271 71 := by
  have hc : ((19963/62500 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23691709103/625000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((19963/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c72 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-827057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318081/500000) (δ := 171/12500000) (ψ := 162891/500000) 271 184
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t72 : ((-60922220299/625000000000 : ℚ) : ℝ) ≤ stT271 72 := by
  have hc : ((-827107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60922220299/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-827107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c73 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -691/5000000) (δ := 1363/100000000) (ψ := 162891/500000) 271 185
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t73 : ((23407049589/200000000000 : ℚ) : ℝ) ≤ stT271 73 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23407049589/200000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c74 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-427571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6491551/10000000) (δ := 13737/1000000000) (ψ := 162891/500000) 271 186
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t74 : ((-124267628823/1250000000000 : ℚ) : ℝ) ≤ stT271 74 := by
  have hc : ((-106899/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124267628823/1250000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-106899/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c75 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((505323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2602599/10000000) (δ := 13637/1000000000) (ψ := 162891/500000) 271 186
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t75 : ((5834387331/100000000000 : ℚ) : ℝ) ≤ stT271 75 := by
  have hc : ((505273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5834387331/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((505273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c76 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-81809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4131741/10000000) (δ := 859/62500000) (ψ := 162891/500000) 271 187
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t76 : ((-93898739861/10000000000000 : ℚ) : ℝ) ≤ stT271 76 := by
  have hc : ((-81859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93898739861/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-81859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c77 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-313661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2362303/5000000) (δ := 13659/1000000000) (ψ := 162891/500000) 271 187
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t77 : ((-178753468933/5000000000000 : ℚ) : ℝ) ≤ stT271 77 := by
  have hc : ((-313711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178753468933/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-313711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c78 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((624331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2241303/10000000) (δ := 13751/1000000000) (ψ := 162891/500000) 271 188
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t78 : ((706859017837/10000000000000 : ℚ) : ℝ) ≤ stT271 78 := by
  have hc : ((624281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((706859017837/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((624281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c79 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-166649/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6389369/10000000) (δ := 847/62500000) (ψ := 162891/500000) 271 188
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t79 : ((-5859563781/62500000000 : ℚ) : ℝ) ≤ stT271 79 := by
  have hc : ((-166659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5859563781/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-166659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c80 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((11871/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -796457/10000000) (δ := 6829/500000000) (ψ := 162891/500000) 271 189
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t80 : ((106171767779/1000000000000 : ℚ) : ℝ) ≤ stT271 80 := by
  have hc : ((94963/100000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106171767779/1000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((94963/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c81 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-199123/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3809893/5000000) (δ := 2749/200000000) (ψ := 162891/500000) 271 189
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t81 : ((-27657383237/250000000000 : ℚ) : ℝ) ≤ stT271 81 := by
  have hc : ((-199133/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27657383237/250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-199133/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c82 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((995959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14051/625000) (δ := 6783/500000000) (ψ := 162891/500000) 271 190
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t82 : ((219959449467/2000000000000 : ℚ) : ℝ) ≤ stT271 82 := by
  have hc : ((995909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219959449467/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((995909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c83 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-243231/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7270899/10000000) (δ := 1363/100000000) (ψ := 162891/500000) 271 191
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t83 : ((-533989050141/5000000000000 : ℚ) : ℝ) ≤ stT271 83 := by
  have hc : ((-486487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-533989050141/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-486487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c84 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((235923/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 842943/10000000) (δ := 27173/1000000000) (ψ := 162891/500000) 271 191
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t84 : ((514798703069/5000000000000 : ℚ) : ℝ) ≤ stT271 84 := by
  have hc : ((471821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((514798703069/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((471821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c85 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-459999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6847181/10000000) (δ := 13723/1000000000) (ψ := 162891/500000) 271 192
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t85 : ((-62370801459/625000000000 : ℚ) : ℝ) ≤ stT271 85 := by
  have hc : ((-57503/62500 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62370801459/625000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-57503/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c86 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((56791/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076859/10000000) (δ := 13723/1000000000) (ψ := 162891/500000) 271 192
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t86 : ((489887191081/5000000000000 : ℚ) : ℝ) ≤ stT271 86 := by
  have hc : ((454303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489887191081/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((454303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c87 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-57013/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3399297/5000000) (δ := 13587/1000000000) (ψ := 162891/500000) 271 193
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t87 : ((-489021830577/5000000000000 : ℚ) : ℝ) ≤ stT271 87 := by
  have hc : ((-456129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489021830577/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-456129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c88 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((929501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18887/200000) (δ := 851/62500000) (ψ := 162891/500000) 271 193
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t88 : ((990797554353/10000000000000 : ℚ) : ℝ) ≤ stT271 88 := by
  have hc : ((929451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((990797554353/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((929451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c89 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-477917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3554101/5000000) (δ := 13609/1000000000) (ψ := 162891/500000) 271 194
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t89 : ((-126654391029/1250000000000 : ℚ) : ℝ) ≤ stT271 89 := by
  have hc : ((-238971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126654391029/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-238971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c90 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((491497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461709/10000000) (δ := 6797/500000000) (ψ := 162891/500000) 271 194
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t90 : ((8094635991/78125000000 : ℚ) : ℝ) ≤ stT271 90 := by
  have hc : ((30717/31250 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8094635991/78125000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((30717/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c91 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-999293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7759981/10000000) (δ := 13551/500000000) (ψ := 162891/500000) 271 195
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t91 : ((-209519255351/2000000000000 : ℚ) : ℝ) ≤ stT271 91 := by
  have hc : ((-999343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209519255351/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-999343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c92 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((61869/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7111/200000) (δ := 13701/1000000000) (ψ := 162891/500000) 271 195
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t92 : ((128999258061/1250000000000 : ℚ) : ℝ) ≤ stT271 92 := by
  have hc : ((494927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128999258061/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((494927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c93 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-937973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1393767/2000000) (δ := 13601/1000000000) (ψ := 162891/500000) 271 195
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t93 : ((-121585603237/1250000000000 : ℚ) : ℝ) ≤ stT271 93 := by
  have hc : ((-938023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121585603237/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-938023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c94 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((826899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -746531/5000000) (δ := 13709/1000000000) (ψ := 162891/500000) 271 196
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t94 : ((852829422429/10000000000000 : ℚ) : ℝ) ≤ stT271 94 := by
  have hc : ((826849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((852829422429/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((826849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c95 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-644009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 567631/1000000) (δ := 6847/500000000) (ψ := 162891/500000) 271 196
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t95 : ((-660791008761/10000000000000 : ℚ) : ℝ) ≤ stT271 95 := by
  have hc : ((-644059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660791008761/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-644059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c96 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((241/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2937347/10000000) (δ := 851/62500000) (ψ := 162891/500000) 271 197
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t96 : ((393500041/10000000000 : ℚ) : ℝ) ≤ stT271 96 := by
  have hc : ((7711/20000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((393500041/10000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((7711/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c97 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-62543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81669/200000) (δ := 851/62500000) (ψ := 162891/500000) 271 197
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t97 : ((-63553614771/10000000000000 : ℚ) : ℝ) ≤ stT271 97 := by
  have hc : ((-62593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63553614771/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-62593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c98 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-922/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -935147/2000000) (δ := 171/12500000) (ψ := 162891/500000) 271 198
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t98 : ((-29808604877/1000000000000 : ℚ) : ℝ) ≤ stT271 98 := by
  have hc : ((-29509/100000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29808604877/1000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-29509/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c99 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((5091/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 550629/2500000) (δ := 171/12500000) (ψ := 162891/500000) 271 198
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t99 : ((25581206761/400000000000 : ℚ) : ℝ) ≤ stT271 99 := by
  have hc : ((25453/40000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25581206761/400000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((25453/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c100 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-894697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6696369/10000000) (δ := 13673/1000000000) (ψ := 162891/500000) 271 199
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t100 : ((-894747/10000000 : ℚ) : ℝ) ≤ stT271 100 := by
  have hc : ((-894747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-894747/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-894747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c101 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((499919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45027/10000000) (δ := 13673/1000000000) (ψ := 162891/500000) 271 199
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t101 : ((248706513039/2500000000000 : ℚ) : ℝ) ≤ stT271 101 := by
  have hc : ((249947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248706513039/2500000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((249947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c102 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-112359/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6719961/10000000) (δ := 1373/100000000) (ψ := 162891/500000) 271 199
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t102 : ((-111258227557/1250000000000 : ℚ) : ℝ) ≤ stT271 102 := by
  have hc : ((-449461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111258227557/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-449461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c103 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((580627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -475649/2000000) (δ := 6783/500000000) (ψ := 162891/500000) 271 200
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t103 : ((572059354833/10000000000000 : ℚ) : ℝ) ≤ stT271 103 := by
  have hc : ((580577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((572059354833/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((580577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c104 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-24033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1041923/2500000) (δ := 6833/500000000) (ψ := 162891/500000) 271 200
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t104 : ((-47157120871/5000000000000 : ℚ) : ℝ) ≤ stT271 104 := by
  have hc : ((-48091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47157120871/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-48091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c105 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-87349/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011387/2000000) (δ := 6829/500000000) (ψ := 162891/500000) 271 201
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t105 : ((-85253735459/2000000000000 : ℚ) : ℝ) ≤ stT271 105 := by
  have hc : ((-87359/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85253735459/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-87359/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c106 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((106829/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272977/2000000) (δ := 2749/200000000) (ψ := 162891/500000) 271 201
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t106 : ((83004267787/1000000000000 : ℚ) : ℝ) ≤ stT271 106 := by
  have hc : ((427291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83004267787/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((427291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c107 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-9987/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3863237/5000000) (δ := 6779/500000000) (ψ := 162891/500000) 271 201
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t107 : ((-772422863/8000000000 : ℚ) : ℝ) ≤ stT271 107 := by
  have hc : ((-799/800 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772422863/8000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-799/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c108 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((782799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1679113/10000000) (δ := 3413/250000000) (ψ := 162891/500000) 271 202
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t108 : ((3012800901/40000000000 : ℚ) : ℝ) ≤ stT271 108 := by
  have hc : ((782749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3012800901/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((782749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c109 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-126247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4565133/10000000) (δ := 13651/1000000000) (ψ := 162891/500000) 271 202
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t109 : ((-1889792671/78125000000 : ℚ) : ℝ) ≤ stT271 109 := by
  have hc : ((-3946/15625 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1889792671/78125000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-3946/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c110 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-399919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4955561/10000000) (δ := 13659/1000000000) (ψ := 162891/500000) 271 203
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t110 : ((-381355642647/10000000000000 : ℚ) : ℝ) ≤ stT271 110 := by
  have hc : ((-399969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381355642647/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-399969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c111 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((891433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587873/5000000) (δ := 13559/1000000000) (ψ := 162891/500000) 271 203
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t111 : ((846062414131/10000000000000 : ℚ) : ℝ) ≤ stT271 111 := by
  have hc : ((891383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((846062414131/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((891383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c112 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-971147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1812993/2500000) (δ := 859/62500000) (ψ := 162891/500000) 271 203
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t112 : ((-57355981229/625000000000 : ℚ) : ℝ) ≤ stT271 112 := by
  have hc : ((-971197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57355981229/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-971197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c113 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((140607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2433693/10000000) (δ := 6833/500000000) (ψ := 162891/500000) 271 204
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t113 : ((3306501451/62500000000 : ℚ) : ℝ) ≤ stT271 113 := by
  have hc : ((281189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3306501451/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((281189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c114 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((77981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27621/78125) (δ := 13637/1000000000) (ψ := 162891/500000) 271 204
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t114 : ((3650621013/250000000000 : ℚ) : ℝ) ≤ stT271 114 := by
  have hc : ((19489/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3650621013/250000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((19489/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c115 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-802433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6255393/10000000) (δ := 13673/1000000000) (ψ := 162891/500000) 271 205
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t115 : ((-149663881983/2000000000000 : ℚ) : ℝ) ≤ stT271 115 := by
  have hc : ((-802483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149663881983/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-802483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c116 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((493941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194799/5000000) (δ := 13673/1000000000) (ψ := 162891/500000) 271 205
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t116 : ((28661822001/312500000000 : ℚ) : ℝ) ≤ stT271 116 := by
  have hc : ((123479/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28661822001/312500000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((123479/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c117 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-564291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2712963/5000000) (δ := 1363/100000000) (ψ := 162891/500000) 271 205
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t117 : ((-521733818841/10000000000000 : ℚ) : ℝ) ≤ stT271 117 := by
  have hc : ((-564341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521733818841/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-564341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c118 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-46689/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2258019/5000000) (δ := 13623/1000000000) (ψ := 162891/500000) 271 206
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t118 : ((-1719597277/80000000000 : ℚ) : ℝ) ≤ stT271 118 := by
  have hc : ((-46699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1719597277/80000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-46699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c119 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((221691/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1201249/10000000) (δ := 13623/1000000000) (ψ := 162891/500000) 271 206
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t119 : ((203212237593/2500000000000 : ℚ) : ℝ) ≤ stT271 119 := by
  have hc : ((443357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203212237593/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((443357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c120 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-115457/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1717693/2500000) (δ := 13723/1000000000) (ψ := 162891/500000) 271 206
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t120 : ((-421612209963/5000000000000 : ℚ) : ℝ) ≤ stT271 120 := by
  have hc : ((-461853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421612209963/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-461853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c121 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((8783/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1607377/5000000) (δ := 2723/200000000) (ψ := 162891/500000) 271 207
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t121 : ((12772987227/500000000000 : ℚ) : ℝ) ≤ stT271 121 := by
  have hc : ((140503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12772987227/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((140503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c122 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((36631/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236141/1000000) (δ := 3397/250000000) (ψ := 162891/500000) 271 207
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t122 : ((265290424211/5000000000000 : ℚ) : ℝ) ≤ stT271 122 := by
  have hc : ((293023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265290424211/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((293023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c123 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-249971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3907959/5000000) (δ := 3427/250000000) (ψ := 162891/500000) 271 208
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t123 : ((-45080524489/500000000000 : ℚ) : ℝ) ≤ stT271 123 := by
  have hc : ((-499967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45080524489/500000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-499967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c124 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((596209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -466013/2000000) (δ := 3427/250000000) (ψ := 162891/500000) 271 208
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t124 : ((267683141067/5000000000000 : ℚ) : ℝ) ≤ stT271 124 := by
  have hc : ((596159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267683141067/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((596159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c125 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((320347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3111751/10000000) (δ := 2719/200000000) (ψ := 162891/500000) 271 208
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t125 : ((286482284819/10000000000000 : ℚ) : ℝ) ≤ stT271 125 := by
  have hc : ((320297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286482284819/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((320297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c126 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-965747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7197757/10000000) (δ := 13601/1000000000) (ψ := 162891/500000) 271 209
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t126 : ((-860400539187/10000000000000 : ℚ) : ℝ) ≤ stT271 126 := by
  have hc : ((-965797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-860400539187/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-965797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c127 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((740609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460513/2500000) (δ := 13701/1000000000) (ψ := 162891/500000) 271 209
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t127 : ((164284868001/2500000000000 : ℚ) : ℝ) ≤ stT271 127 := by
  have hc : ((740559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164284868001/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((740559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c128 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((36221/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 867929/2500000) (δ := 13701/1000000000) (ψ := 162891/500000) 271 209
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t128 : ((32006287313/2000000000000 : ℚ) : ℝ) ≤ stT271 128 := by
  have hc : ((36211/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32006287313/2000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((36211/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c129 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-468637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3481903/5000000) (δ := 13709/1000000000) (ψ := 162891/500000) 271 210
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t129 : ((-206316963281/2500000000000 : ℚ) : ℝ) ≤ stT271 129 := by
  have hc : ((-234331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206316963281/2500000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-234331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c130 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((384711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1732151/10000000) (δ := 13709/1000000000) (ψ := 162891/500000) 271 210
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t130 : ((84347983447/1250000000000 : ℚ) : ℝ) ≤ stT271 130 := by
  have hc : ((192343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84347983447/1250000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((192343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c131 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((185923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3459463/10000000) (δ := 6847/500000000) (ψ := 162891/500000) 271 210
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t131 : ((20299747949/1250000000000 : ℚ) : ℝ) ≤ stT271 131 := by
  have hc : ((185873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20299747949/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((185873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c132 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-477217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7096383/10000000) (δ := 3429/250000000) (ψ := 162891/500000) 271 211
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t132 : ((-207693093569/2500000000000 : ℚ) : ℝ) ≤ stT271 132 := by
  have hc : ((-238621/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207693093569/2500000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-238621/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c133 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((175381/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -396631/2000000) (δ := 3429/250000000) (ψ := 162891/500000) 271 211
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t133 : ((304127209333/5000000000000 : ℚ) : ℝ) ≤ stT271 133 := by
  have hc : ((350737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304127209333/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((350737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c134 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((40989/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38647/125000) (δ := 6779/250000000) (ψ := 162891/500000) 271 211
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t134 : ((35403686277/1250000000000 : ℚ) : ℝ) ≤ stT271 134 := by
  have hc : ((163931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35403686277/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((163931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c135 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-496979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303161/400000) (δ := 13679/1000000000) (ψ := 162891/500000) 271 212
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t135 : ((-106938238413/1250000000000 : ℚ) : ℝ) ≤ stT271 135 := by
  have hc : ((-124251/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106938238413/1250000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-124251/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c136 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((128361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2579007/10000000) (δ := 13579/1000000000) (ψ := 162891/500000) 271 212
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t136 : ((55028905981/1250000000000 : ℚ) : ℝ) ≤ stT271 136 := by
  have hc : ((256697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55028905981/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((256697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c137 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((144653/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1192213/5000000) (δ := 1703/125000000) (ψ := 162891/500000) 271 212
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t137 : ((247149247317/5000000000000 : ℚ) : ℝ) ≤ stT271 137 := by
  have hc : ((289281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247149247317/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((289281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c138 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-195313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22849/31250) (δ := 13579/1000000000) (ψ := 162891/500000) 271 212
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t138 : ((-166270071011/2000000000000 : ℚ) : ℝ) ≤ stT271 138 := by
  have hc : ((-195323/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166270071011/2000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-195323/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c139 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((168181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -350453/1000000) (δ := 3393/250000000) (ψ := 162891/500000) 271 213
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t139 : ((35651674157/2500000000000 : ℚ) : ℝ) ≤ stT271 139 := by
  have hc : ((168131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35651674157/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((168131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c140 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((857271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1352129/10000000) (δ := 13631/1000000000) (ψ := 162891/500000) 271 213
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t140 : ((362241878517/5000000000000 : ℚ) : ℝ) ≤ stT271 140 := by
  have hc : ((857221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362241878517/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((857221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c141 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-24457/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6174167/10000000) (δ := 1709/125000000) (ψ := 162891/500000) 271 213
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t141 : ((-41195654653/625000000000 : ℚ) : ℝ) ≤ stT271 141 := by
  have hc : ((-391337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41195654653/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-391337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c142 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-321687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -593221/1250000) (δ := 2713/200000000) (ψ := 162891/500000) 271 214
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t142 : ((-134997949567/5000000000000 : ℚ) : ℝ) ≤ stT271 142 := by
  have hc : ((-321737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134997949567/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-321737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c143 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((499997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 541/625000) (δ := 2713/200000000) (ψ := 162891/500000) 271 214
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t143 : ((52262198153/625000000000 : ℚ) : ℝ) ≤ stT271 143 := by
  have hc : ((124993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52262198153/625000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((124993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c144 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-19729/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4729883/10000000) (δ := 6869/500000000) (ψ := 162891/500000) 271 214
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t144 : ((-65773802619/2500000000000 : ℚ) : ℝ) ≤ stT271 144 := by
  have hc : ((-157857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65773802619/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-157857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c145 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-162097/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3144721/5000000) (δ := 6779/500000000) (ψ := 162891/500000) 271 215
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t145 : ((-26924513737/400000000000 : ℚ) : ℝ) ≤ stT271 145 := by
  have hc : ((-162107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26924513737/400000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-162107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c146 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((79413/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -408263/2500000) (δ := 2729/200000000) (ψ := 162891/500000) 271 215
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t146 : ((821480723/12500000000 : ℚ) : ℝ) ≤ stT271 146 := by
  have hc : ((4963/6250 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((821480723/12500000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((4963/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c147 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((182763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 598299/2000000) (δ := 6779/500000000) (ψ := 162891/500000) 271 215
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t147 : ((37679936017/1250000000000 : ℚ) : ℝ) ≤ stT271 147 := by
  have hc : ((91369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37679936017/1250000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((91369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c148 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-497103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3792371/5000000) (δ := 2729/200000000) (ψ := 162891/500000) 271 215
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t148 : ((-10215918259/125000000000 : ℚ) : ℝ) ≤ stT271 148 := by
  have hc : ((-62141/62500 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10215918259/125000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-62141/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c149 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((72963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3560869/10000000) (δ := 13651/1000000000) (ψ := 162891/500000) 271 216
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t149 : ((29876535339/2500000000000 : ℚ) : ℝ) ≤ stT271 149 := by
  have hc : ((36469/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29876535339/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((36469/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c150 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((925537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970861/10000000) (δ := 847/62500000) (ψ := 162891/500000) 271 216
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t150 : ((47228527097/625000000000 : ℚ) : ℝ) ≤ stT271 150 := by
  have hc : ((925487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47228527097/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((925487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c151 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-579597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5472577/10000000) (δ := 13751/1000000000) (ψ := 162891/500000) 271 216
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t151 : ((-471710352483/10000000000000 : ℚ) : ℝ) ≤ stT271 151 := by
  have hc : ((-579647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-471710352483/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-579647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c152 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-670267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1440853/2500000) (δ := 859/62500000) (ψ := 162891/500000) 271 217
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t152 : ((-135924870309/2500000000000 : ℚ) : ℝ) ≤ stT271 152 := by
  have hc : ((-670317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135924870309/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-670317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c153 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((863661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1320773/10000000) (δ := 13559/1000000000) (ψ := 162891/500000) 271 217
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t153 : ((174547010043/2500000000000 : ℚ) : ℝ) ≤ stT271 153 := by
  have hc : ((863611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174547010043/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((863611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c154 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((327467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 386617/1250000) (δ := 3411/250000000) (ψ := 162891/500000) 271 217
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t154 : ((131919910887/5000000000000 : ℚ) : ℝ) ≤ stT271 154 := by
  have hc : ((327417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131919910887/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((327417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c155 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-247179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1495611/2000000) (δ := 13559/1000000000) (ψ := 162891/500000) 271 217
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t155 : ((-19854915663/250000000000 : ℚ) : ℝ) ≤ stT271 155 := by
  have hc : ((-494383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19854915663/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-494383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c156 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((4321/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1936487/5000000) (δ := 1717/125000000) (ψ := 162891/500000) 271 218
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t156 : ((5393061/3125000000 : ℚ) : ℝ) ≤ stT271 156 := by
  have hc : ((4311/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5393061/3125000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((4311/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c157 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((983403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114029/2500000) (δ := 13567/1000000000) (ψ := 162891/500000) 271 218
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t157 : ((392400131179/5000000000000 : ℚ) : ℝ) ≤ stT271 157 := by
  have hc : ((983353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392400131179/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((983353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c158 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-163101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4757699/10000000) (δ := 13567/1000000000) (ψ := 162891/500000) 271 218
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t158 : ((-32444048577/1250000000000 : ℚ) : ℝ) ≤ stT271 158 := by
  have hc : ((-81563/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32444048577/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-81563/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c159 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-222747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6675781/10000000) (δ := 6837/500000000) (ψ := 162891/500000) 271 219
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t159 : ((-88329933497/1250000000000 : ℚ) : ℝ) ≤ stT271 159 := by
  have hc : ((-445519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88329933497/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-445519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c160 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((564267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2428127/10000000) (δ := 6837/500000000) (ψ := 162891/500000) 271 219
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t160 : ((446052469473/10000000000000 : ℚ) : ℝ) ≤ stT271 160 := by
  have hc : ((564217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446052469473/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((564217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c161 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((18841/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448259/2500000) (δ := 13729/1000000000) (ψ := 162891/500000) 271 219
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t161 : ((5939118149/100000000000 : ℚ) : ℝ) ≤ stT271 161 := by
  have hc : ((75359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5939118149/100000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((75359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c162 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-29367/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1497029/2500000) (δ := 13729/1000000000) (ψ := 162891/500000) 271 219
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t162 : ((-922979563/16000000000 : ℚ) : ℝ) ≤ stT271 162 := by
  have hc : ((-29369/40000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-922979563/16000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-29369/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c163 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-604737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277529/500000) (δ := 6861/500000000) (ψ := 162891/500000) 271 220
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t163 : ((-473706070407/10000000000000 : ℚ) : ℝ) ≤ stT271 163 := by
  have hc : ((-604787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473706070407/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-604787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c164 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((211449/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703427/5000000) (δ := 13581/1000000000) (ψ := 162891/500000) 271 220
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t164 : ((82551998441/1250000000000 : ℚ) : ℝ) ≤ stT271 164 := by
  have hc : ((422873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82551998441/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((422873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c165 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((467207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677917/2500000) (δ := 6861/500000000) (ψ := 162891/500000) 271 220
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t165 : ((181840395093/5000000000000 : ℚ) : ℝ) ≤ stT271 165 := by
  have hc : ((467157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181840395093/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((467157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c166 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-228327/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6805327/10000000) (δ := 13681/1000000000) (ψ := 162891/500000) 271 220
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t166 : ((-354451862529/5000000000000 : ℚ) : ℝ) ≤ stT271 166 := by
  have hc : ((-456679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354451862529/5000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-456679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c167 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-354711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151047/312500) (δ := 2723/200000000) (ψ := 162891/500000) 271 221
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t167 : ((-4289415251/156250000000 : ℚ) : ℝ) ≤ stT271 167 := by
  have hc : ((-354761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4289415251/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-354761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c168 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((11883/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -788761/10000000) (δ := 3397/250000000) (ψ := 162891/500000) 271 221
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t168 : ((18334884861/250000000000 : ℚ) : ℝ) ≤ stT271 168 := by
  have hc : ((95059/100000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18334884861/250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((95059/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c169 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((68601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1616033/5000000) (δ := 3397/250000000) (ψ := 162891/500000) 271 221
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t169 : ((10552066371/500000000000 : ℚ) : ℝ) ≤ stT271 169 := by
  have hc : ((137177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10552066371/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((137177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c170 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-38757/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7229113/10000000) (δ := 1711/125000000) (ψ := 162891/500000) 271 221
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t170 : ((-5945359287/80000000000 : ℚ) : ℝ) ≤ stT271 170 := by
  have hc : ((-38759/40000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5945359287/80000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-38759/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c171 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-45849/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -901049/2000000) (δ := 2739/200000000) (ψ := 162891/500000) 271 222
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t171 : ((-438366181/25000000000 : ℚ) : ℝ) ≤ stT271 171 := by
  have hc : ((-45859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438366181/25000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-45859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c172 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((243869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -554811/10000000) (δ := 3427/250000000) (ψ := 162891/500000) 271 222
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t172 : ((92969315199/1250000000000 : ℚ) : ℝ) ≤ stT271 172 := by
  have hc : ((487713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92969315199/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((487713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c173 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((43979/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134909/400000) (δ := 2739/200000000) (ψ := 162891/500000) 271 222
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t173 : ((6685794233/400000000000 : ℚ) : ℝ) ≤ stT271 173 := by
  have hc : ((43969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6685794233/400000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((43969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c174 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-973543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7277631/10000000) (δ := 3427/250000000) (ψ := 162891/500000) 271 222
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t174 : ((-738079879707/10000000000000 : ℚ) : ℝ) ≤ stT271 174 := by
  have hc : ((-973593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-738079879707/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-973593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c175 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-245773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4547783/10000000) (δ := 137/10000000) (ψ := 162891/500000) 271 223
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t175 : ((-185824734567/10000000000000 : ℚ) : ℝ) ≤ stT271 175 := by
  have hc : ((-245823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185824734567/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-245823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c176 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((962437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171847/2500000) (δ := 137/10000000) (ψ := 162891/500000) 271 223
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t176 : ((362713074043/5000000000000 : ℚ) : ℝ) ≤ stT271 176 := by
  have hc : ((962387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362713074043/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((962387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c177 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((305363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393899/1250000) (δ := 13603/1000000000) (ψ := 162891/500000) 271 223
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t177 : ((114743647599/5000000000000 : ℚ) : ℝ) ≤ stT271 177 := by
  have hc : ((305313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114743647599/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((305313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c178 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-93787/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6968091/10000000) (δ := 137/10000000) (ψ := 162891/500000) 271 223
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t178 : ((-549219573/7812500000 : ℚ) : ℝ) ≤ stT271 178 := by
  have hc : ((-2931/3125 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-549219573/7812500000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-2931/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c179 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-395791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2472157/5000000) (δ := 13693/1000000000) (ψ := 162891/500000) 271 224
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t179 : ((-73966453419/2500000000000 : ℚ) : ℝ) ≤ stT271 179 := by
  have hc : ((-395841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73966453419/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-395841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c180 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((892479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1169961/10000000) (δ := 1361/100000000) (ψ := 162891/500000) 271 224
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t180 : ((133035283459/2000000000000 : ℚ) : ℝ) ≤ stT271 180 := by
  have hc : ((892429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133035283459/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((892429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c181 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((511893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645881/2500000) (δ := 13693/1000000000) (ψ := 162891/500000) 271 224
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t181 : ((190224915421/5000000000000 : ℚ) : ℝ) ≤ stT271 181 := by
  have hc : ((511843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190224915421/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((511843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c182 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-408363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3158139/5000000) (δ := 13693/1000000000) (ψ := 162891/500000) 271 224
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t182 : ((-60543521/1000000000 : ℚ) : ℝ) ≤ stT271 182 := by
  have hc : ((-102097/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60543521/1000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-102097/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c183 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-644931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1419831/2500000) (δ := 6843/500000000) (ψ := 162891/500000) 271 225
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t183 : ((-238392072391/5000000000000 : ℚ) : ℝ) ≤ stT271 183 := by
  have hc : ((-644981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238392072391/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-644981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c184 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((140073/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -99361/500000) (δ := 6843/500000000) (ψ := 162891/500000) 271 225
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t184 : ((103255704167/2000000000000 : ℚ) : ℝ) ≤ stT271 184 := by
  have hc : ((140063/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103255704167/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((140063/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c185 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((781357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 842449/5000000) (δ := 6793/500000000) (ψ := 162891/500000) 271 225
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t185 : ((287213922349/5000000000000 : ℚ) : ℝ) ≤ stT271 185 := by
  have hc : ((781307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287213922349/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((781307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c186 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-53463/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1067433/2000000) (δ := 6793/500000000) (ψ := 162891/500000) 271 225
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t186 : ((-2450291403/62500000000 : ℚ) : ℝ) ≤ stT271 186 := by
  have hc : ((-13367/25000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2450291403/62500000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-13367/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c187 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-451009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6738043/10000000) (δ := 1703/125000000) (ψ := 162891/500000) 271 226
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t187 : ((-164914493141/2500000000000 : ℚ) : ℝ) ≤ stT271 187 := by
  have hc : ((-225517/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164914493141/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-225517/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c188 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((9857/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781183/2500000) (δ := 3431/250000000) (ψ := 162891/500000) 271 226
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t188 : ((28751228397/1250000000000 : ℚ) : ℝ) ≤ stT271 188 := by
  have hc : ((157687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28751228397/1250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((157687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c189 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((982419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 469473/10000000) (δ := 1703/125000000) (ψ := 162891/500000) 271 226
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t189 : ((22330229739/312500000000 : ℚ) : ℝ) ≤ stT271 189 := by
  have hc : ((982369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22330229739/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((982369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c190 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-23521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25279/62500) (δ := 13679/1000000000) (ψ := 162891/500000) 271 226
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t190 : ((-8541040721/2500000000000 : ℚ) : ℝ) ≤ stT271 190 := by
  have hc : ((-11773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8541040721/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-11773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c191 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-994889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7601109/10000000) (δ := 1703/125000000) (ψ := 162891/500000) 271 226
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t191 : ((-28796519477/400000000000 : ℚ) : ℝ) ≤ stT271 191 := by
  have hc : ((-994939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28796519477/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-994939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c192 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-253997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4569017/10000000) (δ := 13631/1000000000) (ψ := 162891/500000) 271 227
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t192 : ((-22917833917/1250000000000 : ℚ) : ℝ) ≤ stT271 192 := by
  have hc : ((-254047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22917833917/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-254047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c193 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((228291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52477/500000) (δ := 13631/1000000000) (ψ := 162891/500000) 271 227
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t193 : ((65727315391/1000000000000 : ℚ) : ℝ) ≤ stT271 193 := by
  have hc : ((456557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65727315391/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((456557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c194 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((556431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122589/500000) (δ := 13631/1000000000) (ψ := 162891/500000) 271 227
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t194 : ((199729094999/5000000000000 : ℚ) : ℝ) ≤ stT271 194 := by
  have hc : ((556381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199729094999/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((556381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c195 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-359803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2967539/5000000) (δ := 1709/125000000) (ψ := 162891/500000) 271 227
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t195 : ((-12883911411/250000000000 : ℚ) : ℝ) ≤ stT271 195 := by
  have hc : ((-89957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12883911411/250000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-89957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c196 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-814673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1261481/2000000) (δ := 2733/200000000) (ψ := 162891/500000) 271 228
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t196 : ((-290972616389/5000000000000 : ℚ) : ℝ) ≤ stT271 196 := by
  have hc : ((-814723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290972616389/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-814723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c197 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((103531/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2859539/10000000) (δ := 6869/500000000) (ψ := 162891/500000) 271 228
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t197 : ((14750765139/500000000000 : ℚ) : ℝ) ≤ stT271 197 := by
  have hc : ((207037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14750765139/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((207037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c198 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((243511/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285423/5000000) (δ := 2733/200000000) (ψ := 162891/500000) 271 228
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t198 : ((346093670993/5000000000000 : ℚ) : ℝ) ≤ stT271 198 := by
  have hc : ((486997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346093670993/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((486997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c199 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-356/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 995989/2500000) (δ := 6819/500000000) (ψ := 162891/500000) 271 228
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t199 : ((-4046652897/2500000000000 : ℚ) : ℝ) ≤ stT271 199 := by
  have hc : ((-11417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4046652897/2500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-11417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c200 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-39283/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295197/400000) (δ := 6869/500000000) (ψ := 162891/500000) 271 228
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t200 : ((-5555739699/80000000000 : ℚ) : ℝ) ≤ stT271 200 := by
  have hc : ((-7857/8000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5555739699/80000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-7857/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c201 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-39749/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247447/500000) (δ := 13657/1000000000) (ψ := 162891/500000) 271 229
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t201 : ((-7010081221/250000000000 : ℚ) : ℝ) ≤ stT271 201 := by
  have hc : ((-19877/50000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7010081221/250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-19877/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c202 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((805259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158671/1000000) (δ := 6873/500000000) (ψ := 162891/500000) 271 229
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t202 : ((566542636773/10000000000000 : ℚ) : ℝ) ≤ stT271 202 := by
  have hc : ((805209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((566542636773/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((805209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c203 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((762521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 439747/2500000) (δ := 6823/500000000) (ψ := 162891/500000) 271 229
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t203 : ((267574710501/5000000000000 : ℚ) : ℝ) ≤ stT271 203 := by
  have hc : ((762471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267574710501/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((762471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c204 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-447969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5088223/10000000) (δ := 6823/500000000) (ψ := 162891/500000) 271 229
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t204 : ((-313676470679/10000000000000 : ℚ) : ℝ) ≤ stT271 204 := by
  have hc : ((-448019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313676470679/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-448019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c205 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-48807/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3653383/5000000) (δ := 11/800000) (ψ := 162891/500000) 271 230
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t205 : ((-68180135789/1000000000000 : ℚ) : ℝ) ≤ stT271 205 := by
  have hc : ((-97619/100000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68180135789/1000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-97619/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c206 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-8291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -801983/2000000) (δ := 13553/1000000000) (ψ := 162891/500000) 271 230
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t206 : ((-5785330769/2500000000000 : ℚ) : ℝ) ≤ stT271 206 := by
  have hc : ((-16607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5785330769/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-16607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c207 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((957779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -364527/5000000) (δ := 11/800000) (ψ := 162891/500000) 271 230
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t207 : ((83208453249/1250000000000 : ℚ) : ℝ) ≤ stT271 207 := by
  have hc : ((957729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83208453249/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((957729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c208 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((264061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1268011/5000000) (δ := 273/20000000) (ψ := 162891/500000) 271 230
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t208 : ((366151923/10000000000 : ℚ) : ℝ) ≤ stT271 208 := by
  have hc : ((66009/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366151923/10000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((66009/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c209 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-338391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 723181/1250000) (δ := 13653/1000000000) (ψ := 162891/500000) 271 230
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t209 : ((-2926092793/62500000000 : ℚ) : ℝ) ≤ stT271 209 := by
  have hc : ((-21151/31250 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2926092793/62500000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-21151/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c210 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-178661/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1337721/2000000) (δ := 13643/1000000000) (ψ := 162891/500000) 271 231
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t210 : ((-61647391143/1000000000000 : ℚ) : ℝ) ≤ stT271 210 := by
  have hc : ((-178671/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61647391143/1000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-178671/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c211 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((181751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3470073/10000000) (δ := 683/50000000) (ψ := 162891/500000) 271 231
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t211 : ((31272014007/2500000000000 : ℚ) : ℝ) ≤ stT271 211 := by
  have hc : ((181701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31272014007/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((181701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c212 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((994311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133393/5000000) (δ := 13743/1000000000) (ψ := 162891/500000) 271 231
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t212 : ((341430221661/5000000000000 : ℚ) : ℝ) ≤ stT271 212 := by
  have hc : ((994261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341430221661/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((994261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c213 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((195727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1460731/5000000) (δ := 683/50000000) (ψ := 162891/500000) 271 231
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t213 : ((16761582747/625000000000 : ℚ) : ℝ) ≤ stT271 213 := by
  have hc : ((97851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16761582747/625000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((97851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c214 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-95309/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1523701/2500000) (δ := 339/25000000) (ψ := 162891/500000) 271 231
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t214 : ((-130312340973/2500000000000 : ℚ) : ℝ) ≤ stT271 214 := by
  have hc : ((-381261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130312340973/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-381261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c215 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-423699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3227327/5000000) (δ := 13667/1000000000) (ψ := 162891/500000) 271 232
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t215 : ((-14448882469/250000000000 : ℚ) : ℝ) ≤ stT271 215 := by
  have hc : ((-105931/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14448882469/250000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-105931/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c216 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((48799/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3310783/10000000) (δ := 13667/1000000000) (ψ := 162891/500000) 271 232
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t216 : ((33196669857/2000000000000 : ℚ) : ℝ) ≤ stT271 216 := by
  have hc : ((48789/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33196669857/2000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((48789/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c217 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((498683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181479/10000000) (δ := 1717/125000000) (ψ := 162891/500000) 271 232
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t217 : ((42313873919/625000000000 : ℚ) : ℝ) ≤ stT271 217 := by
  have hc : ((249329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42313873919/625000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((249329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c218 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((387033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2933463/10000000) (δ := 3409/250000000) (ψ := 162891/500000) 271 232
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t218 : ((52419556231/2000000000000 : ℚ) : ℝ) ≤ stT271 218 := by
  have hc : ((386983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52419556231/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((386983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c219 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-746559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6034177/10000000) (δ := 1717/125000000) (ψ := 162891/500000) 271 232
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t219 : ((-252256036221/5000000000000 : ℚ) : ℝ) ≤ stT271 219 := by
  have hc : ((-746609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252256036221/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-746609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c220 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-874351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6587231/10000000) (δ := 6837/500000000) (ψ := 162891/500000) 271 233
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t220 : ((-2947605771/50000000000 : ℚ) : ℝ) ≤ stT271 220 := by
  have hc : ((-874401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2947605771/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-874401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c221 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((41049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3514633/10000000) (δ := 6837/500000000) (ψ := 162891/500000) 271 233
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t221 : ((1725256533/156250000000 : ℚ) : ℝ) ≤ stT271 221 := by
  have hc : ((82073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1725256533/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((82073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c222 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((245853/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56999/1250000) (δ := 13629/1000000000) (ψ := 162891/500000) 271 233
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t222 : ((82498663309/1250000000000 : ℚ) : ℝ) ≤ stT271 222 := by
  have hc : ((491681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82498663309/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((491681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c223 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((255011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 647241/2500000) (δ := 13629/1000000000) (ψ := 162891/500000) 271 233
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t223 : ((85375559957/2500000000000 : ℚ) : ℝ) ≤ stT271 223 := by
  have hc : ((127493/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85375559957/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((127493/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c224 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-62671/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2810151/5000000) (δ := 13729/1000000000) (ψ := 162891/500000) 271 233
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t224 : ((-5234652513/125000000000 : ℚ) : ℝ) ≤ stT271 224 := by
  have hc : ((-15669/25000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5234652513/125000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-15669/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c225 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-951207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1413961/2000000) (δ := 13621/1000000000) (ψ := 162891/500000) 271 234
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t225 : ((-634171650419/10000000000000 : ℚ) : ℝ) ≤ stT271 225 := by
  have hc : ((-951257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634171650419/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-951257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c226 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-27667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4065397/10000000) (δ := 13591/500000000) (ψ := 162891/500000) 271 234
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t226 : ((-4605117293/1250000000000 : ℚ) : ℝ) ≤ stT271 226 := by
  have hc : ((-6923/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4605117293/1250000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-6923/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c227 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((909099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1074201/10000000) (δ := 13621/1000000000) (ψ := 162891/500000) 271 234
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t227 : ((603356729427/10000000000000 : ℚ) : ℝ) ≤ stT271 227 := by
  have hc : ((909049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((603356729427/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((909049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c228 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((723783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 951909/5000000) (δ := 13621/1000000000) (ψ := 162891/500000) 271 234
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t228 : ((239651879489/5000000000000 : ℚ) : ℝ) ≤ stT271 228 := by
  have hc : ((723733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239651879489/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((723733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c229 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-367887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4868829/10000000) (δ := 13621/1000000000) (ψ := 162891/500000) 271 234
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t229 : ((-243139760403/10000000000000 : ℚ) : ℝ) ≤ stT271 229 := by
  have hc : ((-367937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243139760403/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-367937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c230 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-124989/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78209/100000) (δ := 6791/500000000) (ψ := 162891/500000) 271 234
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t230 : ((-329677971761/5000000000000 : ℚ) : ℝ) ≤ stT271 230 := by
  have hc : ((-499981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-329677971761/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-499981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c231 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-39707/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4947797/10000000) (δ := 13689/1000000000) (ψ := 162891/500000) 271 235
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t231 : ((-25516201/976562500 : ℚ) : ℝ) ≤ stT271 231 := by
  have hc : ((-1241/3125 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25516201/976562500 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-1241/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c232 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((690579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -505317/2500000) (δ := 13689/1000000000) (ψ := 162891/500000) 271 235
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t232 : ((113338596357/2500000000000 : ℚ) : ℝ) ≤ stT271 232 := by
  have hc : ((690529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113338596357/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((690529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c233 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((468459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 892727/10000000) (δ := 13589/1000000000) (ψ := 162891/500000) 271 235
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t233 : ((153440475257/2500000000000 : ℚ) : ℝ) ≤ stT271 233 := by
  have hc : ((234217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153440475257/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((234217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c234 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((53069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237141/625000) (δ := 6807/500000000) (ψ := 162891/500000) 271 235
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t234 : ((866489517/250000000000 : ℚ) : ℝ) ≤ stT271 234 := by
  have hc : ((53019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((866489517/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((53019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c235 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-178473/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6683387/10000000) (δ := 6807/500000000) (ψ := 162891/500000) 271 235
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t235 : ((-116429636907/2000000000000 : ℚ) : ℝ) ≤ stT271 235 := by
  have hc : ((-178483/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116429636907/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-178483/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c236 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-96999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1536927/2500000) (δ := 13607/1000000000) (ψ := 162891/500000) 271 236
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t236 : ((-50516065969/1000000000000 : ℚ) : ℝ) ≤ stT271 236 := by
  have hc : ((-388021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50516065969/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-388021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c237 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((254743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656607/2000000) (δ := 13707/1000000000) (ψ := 162891/500000) 271 236
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t237 : ((165440677317/10000000000000 : ℚ) : ℝ) ≤ stT271 237 := by
  have hc : ((254693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165440677317/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((254693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c238 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((15394/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430421/10000000) (δ := 13607/1000000000) (ψ := 162891/500000) 271 236
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t238 : ((319293778349/5000000000000 : ℚ) : ℝ) ≤ stT271 238 := by
  have hc : ((492583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319293778349/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((492583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c239 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((11403/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2410269/10000000) (δ := 3399/250000000) (ψ := 162891/500000) 271 236
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t239 : ((1843834523/50000000000 : ℚ) : ℝ) ≤ stT271 239 := by
  have hc : ((5701/10000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1843834523/50000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((5701/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c240 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-250539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2619551/5000000) (δ := 13707/1000000000) (ψ := 162891/500000) 271 236
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t240 : ((-20217320109/625000000000 : ℚ) : ℝ) ≤ stT271 240 := by
  have hc : ((-62641/125000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20217320109/625000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-62641/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c241 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-249183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -956477/1250000) (δ := 17/1250000) (ψ := 162891/500000) 271 237
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t241 : ((-321042051387/5000000000000 : ℚ) : ℝ) ≤ stT271 241 := by
  have hc : ((-498391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321042051387/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-498391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c242 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-179769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -605803/1250000) (δ := 17/1250000) (ψ := 162891/500000) 271 237
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t242 : ((-2311521561/100000000000 : ℚ) : ℝ) ≤ stT271 242 := by
  have hc : ((-89897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2311521561/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-89897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c243 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((136291/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2052617/10000000) (δ := 13603/1000000000) (ψ := 162891/500000) 271 237
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t243 : ((174848523/4000000000 : ℚ) : ℝ) ≤ stT271 243 := by
  have hc : ((136281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174848523/4000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((136281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c244 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((9577/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36487/500000) (δ := 13603/1000000000) (ψ := 162891/500000) 271 237
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t244 : ((1532680519/25000000000 : ℚ) : ℝ) ≤ stT271 244 := by
  have hc : ((19153/20000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1532680519/25000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((19153/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c245 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((169699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3500681/10000000) (δ := 27103/1000000000) (ψ := 162891/500000) 271 237
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t245 : ((27096168631/2500000000000 : ℚ) : ℝ) ≤ stT271 245 := by
  have hc : ((169649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27096168631/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((169649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c246 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-803621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 782547/1250000) (δ := 13703/1000000000) (ψ := 162891/500000) 271 237
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t246 : ((-512402145167/10000000000000 : ℚ) : ℝ) ≤ stT271 246 := by
  have hc : ((-803671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512402145167/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-803671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c247 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-179037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3349553/5000000) (δ := 13693/1000000000) (ψ := 162891/500000) 271 238
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t247 : ((-22784984079/400000000000 : ℚ) : ℝ) ≤ stT271 247 := by
  have hc : ((-179047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22784984079/400000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-179047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c248 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((-13897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -792347/2000000) (δ := 13693/1000000000) (ψ := 162891/500000) 271 238
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t248 : ((-8856358947/10000000000000 : ℚ) : ℝ) ≤ stT271 248 := by
  have hc : ((-13947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8856358947/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-13947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c249 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((440183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1235407/10000000) (δ := 13593/1000000000) (ψ := 162891/500000) 271 238
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t249 : ((34867336049/625000000000 : ℚ) : ℝ) ≤ stT271 249 := by
  have hc : ((220079/250000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34867336049/625000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((220079/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_c250 :
    |Real.cos (((271 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((51863/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1480081/10000000) (δ := 1361/100000000) (ψ := 162891/500000) 271 238
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st271_t250 : ((52478459589/1000000000000 : ℚ) : ℝ) ≤ stT271 250 := by
  have hc : ((414879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((271 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((162891/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st271_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52478459589/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((414879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st271_p1 : ((947351/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT271 (i+1) := by
  rw [Finset.sum_range_one]
  exact st271_t1

theorem st271_p2 : ((1677614876327/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT271 (i+1))
      = (∑ i ∈ Finset.range 1, stT271 (i+1)) + stT271 2 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 1
    simpa using h
  have hprev := st271_p1
  have hstep := st271_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p3 : ((5281881243497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT271 (i+1))
      = (∑ i ∈ Finset.range 2, stT271 (i+1)) + stT271 3 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 2
    simpa using h
  have hprev := st271_p2
  have hstep := st271_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p4 : ((2052403485329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT271 (i+1))
      = (∑ i ∈ Finset.range 3, stT271 (i+1)) + stT271 4 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 3
    simpa using h
  have hprev := st271_p3
  have hstep := st271_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p5 : ((7308498064573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT271 (i+1))
      = (∑ i ∈ Finset.range 4, stT271 (i+1)) + stT271 5 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 4
    simpa using h
  have hprev := st271_p4
  have hstep := st271_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p6 : ((1571580432441/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT271 (i+1))
      = (∑ i ∈ Finset.range 5, stT271 (i+1)) + stT271 6 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 5
    simpa using h
  have hprev := st271_p5
  have hstep := st271_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p7 : ((10566689864837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT271 (i+1))
      = (∑ i ∈ Finset.range 6, stT271 (i+1)) + stT271 7 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 6
    simpa using h
  have hprev := st271_p6
  have hstep := st271_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p8 : ((1650778402893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT271 (i+1))
      = (∑ i ∈ Finset.range 7, stT271 (i+1)) + stT271 8 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 7
    simpa using h
  have hprev := st271_p7
  have hstep := st271_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p9 : ((7559715208963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT271 (i+1))
      = (∑ i ∈ Finset.range 8, stT271 (i+1)) + stT271 9 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 8
    simpa using h
  have hprev := st271_p8
  have hstep := st271_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p10 : ((293708661213/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT271 (i+1))
      = (∑ i ∈ Finset.range 9, stT271 (i+1)) + stT271 10 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 9
    simpa using h
  have hprev := st271_p9
  have hstep := st271_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p11 : ((5254602344739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT271 (i+1))
      = (∑ i ∈ Finset.range 10, stT271 (i+1)) + stT271 11 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 10
    simpa using h
  have hprev := st271_p10
  have hstep := st271_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p12 : ((3650199738587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT271 (i+1))
      = (∑ i ∈ Finset.range 11, stT271 (i+1)) + stT271 12 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 11
    simpa using h
  have hprev := st271_p11
  have hstep := st271_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p13 : ((2422348657879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT271 (i+1))
      = (∑ i ∈ Finset.range 12, stT271 (i+1)) + stT271 13 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 12
    simpa using h
  have hprev := st271_p12
  have hstep := st271_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p14 : ((2617259578427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT271 (i+1))
      = (∑ i ∈ Finset.range 13, stT271 (i+1)) + stT271 14 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 13
    simpa using h
  have hprev := st271_p13
  have hstep := st271_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p15 : ((5218771605943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT271 (i+1))
      = (∑ i ∈ Finset.range 14, stT271 (i+1)) + stT271 15 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 14
    simpa using h
  have hprev := st271_p14
  have hstep := st271_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p16 : ((2771055626857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT271 (i+1))
      = (∑ i ∈ Finset.range 15, stT271 (i+1)) + stT271 16 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 15
    simpa using h
  have hprev := st271_p15
  have hstep := st271_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p17 : ((845565746153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT271 (i+1))
      = (∑ i ∈ Finset.range 16, stT271 (i+1)) + stT271 17 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 16
    simpa using h
  have hprev := st271_p16
  have hstep := st271_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p18 : ((152360400013/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT271 (i+1))
      = (∑ i ∈ Finset.range 17, stT271 (i+1)) + stT271 18 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 17
    simpa using h
  have hprev := st271_p17
  have hstep := st271_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p19 : ((4594790165533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT271 (i+1))
      = (∑ i ∈ Finset.range 18, stT271 (i+1)) + stT271 19 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 18
    simpa using h
  have hprev := st271_p18
  have hstep := st271_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p20 : ((116552958841/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT271 (i+1))
      = (∑ i ∈ Finset.range 19, stT271 (i+1)) + stT271 20 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 19
    simpa using h
  have hprev := st271_p19
  have hstep := st271_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p21 : ((5671144246349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT271 (i+1))
      = (∑ i ∈ Finset.range 20, stT271 (i+1)) + stT271 21 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 20
    simpa using h
  have hprev := st271_p20
  have hstep := st271_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p22 : ((5432158941597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT271 (i+1))
      = (∑ i ∈ Finset.range 21, stT271 (i+1)) + stT271 22 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 21
    simpa using h
  have hprev := st271_p21
  have hstep := st271_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p23 : ((6258722534061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT271 (i+1))
      = (∑ i ∈ Finset.range 22, stT271 (i+1)) + stT271 23 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 22
    simpa using h
  have hprev := st271_p22
  have hstep := st271_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p24 : ((4141262606099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT271 (i+1))
      = (∑ i ∈ Finset.range 23, stT271 (i+1)) + stT271 24 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 23
    simpa using h
  have hprev := st271_p23
  have hstep := st271_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p25 : ((4337540606099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT271 (i+1))
      = (∑ i ∈ Finset.range 24, stT271 (i+1)) + stT271 25 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 24
    simpa using h
  have hprev := st271_p24
  have hstep := st271_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p26 : ((3370905429081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT271 (i+1))
      = (∑ i ∈ Finset.range 25, stT271 (i+1)) + stT271 26 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 25
    simpa using h
  have hprev := st271_p25
  have hstep := st271_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p27 : ((4146284554581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT271 (i+1))
      = (∑ i ∈ Finset.range 26, stT271 (i+1)) + stT271 27 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 26
    simpa using h
  have hprev := st271_p26
  have hstep := st271_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p28 : ((3688059171771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT271 (i+1))
      = (∑ i ∈ Finset.range 27, stT271 (i+1)) + stT271 28 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 27
    simpa using h
  have hprev := st271_p27
  have hstep := st271_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p29 : ((4067687215279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT271 (i+1))
      = (∑ i ∈ Finset.range 28, stT271 (i+1)) + stT271 29 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 28
    simpa using h
  have hprev := st271_p28
  have hstep := st271_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p30 : ((140354052949/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT271 (i+1))
      = (∑ i ∈ Finset.range 29, stT271 (i+1)) + stT271 30 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 29
    simpa using h
  have hprev := st271_p29
  have hstep := st271_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p31 : ((1737988946779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT271 (i+1))
      = (∑ i ∈ Finset.range 30, stT271 (i+1)) + stT271 31 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 30
    simpa using h
  have hprev := st271_p30
  have hstep := st271_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p32 : ((3548095707037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT271 (i+1))
      = (∑ i ∈ Finset.range 31, stT271 (i+1)) + stT271 32 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 31
    simpa using h
  have hprev := st271_p31
  have hstep := st271_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p33 : ((3580752664797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT271 (i+1))
      = (∑ i ∈ Finset.range 32, stT271 (i+1)) + stT271 33 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 32
    simpa using h
  have hprev := st271_p32
  have hstep := st271_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p34 : ((8812540253929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT271 (i+1))
      = (∑ i ∈ Finset.range 33, stT271 (i+1)) + stT271 34 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 33
    simpa using h
  have hprev := st271_p33
  have hstep := st271_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p35 : ((522051365267/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT271 (i+1))
      = (∑ i ∈ Finset.range 34, stT271 (i+1)) + stT271 35 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 34
    simpa using h
  have hprev := st271_p34
  have hstep := st271_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p36 : ((3344329089053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT271 (i+1))
      = (∑ i ∈ Finset.range 35, stT271 (i+1)) + stT271 36 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 35
    simpa using h
  have hprev := st271_p35
  have hstep := st271_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p37 : ((1522322664979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT271 (i+1))
      = (∑ i ∈ Finset.range 36, stT271 (i+1)) + stT271 37 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 36
    simpa using h
  have hprev := st271_p36
  have hstep := st271_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p38 : ((1741414021177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT271 (i+1))
      = (∑ i ∈ Finset.range 37, stT271 (i+1)) + stT271 38 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 37
    simpa using h
  have hprev := st271_p37
  have hstep := st271_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p39 : ((8519483122273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT271 (i+1))
      = (∑ i ∈ Finset.range 38, stT271 (i+1)) + stT271 39 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 38
    simpa using h
  have hprev := st271_p38
  have hstep := st271_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p40 : ((10013122526491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT271 (i+1))
      = (∑ i ∈ Finset.range 39, stT271 (i+1)) + stT271 40 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 39
    simpa using h
  have hprev := st271_p39
  have hstep := st271_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p41 : ((1116360263707/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT271 (i+1))
      = (∑ i ∈ Finset.range 40, stT271 (i+1)) + stT271 41 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 40
    simpa using h
  have hprev := st271_p40
  have hstep := st271_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p42 : ((3002588585021/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT271 (i+1))
      = (∑ i ∈ Finset.range 41, stT271 (i+1)) + stT271 42 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 41
    simpa using h
  have hprev := st271_p41
  have hstep := st271_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p43 : ((12724417891439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT271 (i+1))
      = (∑ i ∈ Finset.range 42, stT271 (i+1)) + stT271 43 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 42
    simpa using h
  have hprev := st271_p42
  have hstep := st271_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p44 : ((13499933341403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT271 (i+1))
      = (∑ i ∈ Finset.range 43, stT271 (i+1)) + stT271 44 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 43
    simpa using h
  have hprev := st271_p43
  have hstep := st271_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p45 : ((3624447485679/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT271 (i+1))
      = (∑ i ∈ Finset.range 44, stT271 (i+1)) + stT271 45 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 44
    simpa using h
  have hprev := st271_p44
  have hstep := st271_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p46 : ((197302314177/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT271 (i+1))
      = (∑ i ∈ Finset.range 45, stT271 (i+1)) + stT271 46 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 45
    simpa using h
  have hprev := st271_p45
  have hstep := st271_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p47 : ((4310129449887/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT271 (i+1))
      = (∑ i ∈ Finset.range 46, stT271 (i+1)) + stT271 47 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 46
    simpa using h
  have hprev := st271_p46
  have hstep := st271_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p48 : ((577856925939/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT271 (i+1))
      = (∑ i ∈ Finset.range 47, stT271 (i+1)) + stT271 48 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 47
    simpa using h
  have hprev := st271_p47
  have hstep := st271_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p49 : ((4635121037/2441406250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT271 (i+1))
      = (∑ i ∈ Finset.range 48, stT271 (i+1)) + stT271 49 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 48
    simpa using h
  have hprev := st271_p48
  have hstep := st271_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p50 : ((1836381961907/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT271 (i+1))
      = (∑ i ∈ Finset.range 49, stT271 (i+1)) + stT271 50 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 49
    simpa using h
  have hprev := st271_p49
  have hstep := st271_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p51 : ((16991119953927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT271 (i+1))
      = (∑ i ∈ Finset.range 50, stT271 (i+1)) + stT271 51 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 50
    simpa using h
  have hprev := st271_p50
  have hstep := st271_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p52 : ((8023413557369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT271 (i+1))
      = (∑ i ∈ Finset.range 51, stT271 (i+1)) + stT271 52 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 51
    simpa using h
  have hprev := st271_p51
  have hstep := st271_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p53 : ((16546224563773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT271 (i+1))
      = (∑ i ∈ Finset.range 52, stT271 (i+1)) + stT271 53 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 52
    simpa using h
  have hprev := st271_p52
  have hstep := st271_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p54 : ((17906738573563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT271 (i+1))
      = (∑ i ∈ Finset.range 53, stT271 (i+1)) + stT271 54 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 53
    simpa using h
  have hprev := st271_p53
  have hstep := st271_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p55 : ((9114406556753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT271 (i+1))
      = (∑ i ∈ Finset.range 54, stT271 (i+1)) + stT271 55 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 54
    simpa using h
  have hprev := st271_p54
  have hstep := st271_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p56 : ((4251046658681/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT271 (i+1))
      = (∑ i ∈ Finset.range 55, stT271 (i+1)) + stT271 56 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 55
    simpa using h
  have hprev := st271_p55
  have hstep := st271_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p57 : ((511677576127/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT271 (i+1))
      = (∑ i ∈ Finset.range 56, stT271 (i+1)) + stT271 57 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 56
    simpa using h
  have hprev := st271_p56
  have hstep := st271_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p58 : ((273873640037/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT271 (i+1))
      = (∑ i ∈ Finset.range 57, stT271 (i+1)) + stT271 58 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 57
    simpa using h
  have hprev := st271_p57
  have hstep := st271_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p59 : ((9027598116907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT271 (i+1))
      = (∑ i ∈ Finset.range 58, stT271 (i+1)) + stT271 59 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 58
    simpa using h
  have hprev := st271_p58
  have hstep := st271_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p60 : ((4201830762201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT271 (i+1))
      = (∑ i ∈ Finset.range 59, stT271 (i+1)) + stT271 60 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 59
    simpa using h
  have hprev := st271_p59
  have hstep := st271_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p61 : ((16773415036577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT271 (i+1))
      = (∑ i ∈ Finset.range 60, stT271 (i+1)) + stT271 61 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 60
    simpa using h
  have hprev := st271_p60
  have hstep := st271_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p62 : ((224926480097/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT271 (i+1))
      = (∑ i ∈ Finset.range 61, stT271 (i+1)) + stT271 62 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 61
    simpa using h
  have hprev := st271_p61
  have hstep := st271_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p63 : ((1722594945413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT271 (i+1))
      = (∑ i ∈ Finset.range 62, stT271 (i+1)) + stT271 63 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 62
    simpa using h
  have hprev := st271_p62
  have hstep := st271_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p64 : ((2082394562587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT271 (i+1))
      = (∑ i ∈ Finset.range 63, stT271 (i+1)) + stT271 64 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 63
    simpa using h
  have hprev := st271_p63
  have hstep := st271_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p65 : ((1789843928297/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT271 (i+1))
      = (∑ i ∈ Finset.range 64, stT271 (i+1)) + stT271 65 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 64
    simpa using h
  have hprev := st271_p64
  have hstep := st271_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p66 : ((3437620324771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT271 (i+1))
      = (∑ i ∈ Finset.range 65, stT271 (i+1)) + stT271 66 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 65
    simpa using h
  have hprev := st271_p65
  have hstep := st271_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p67 : ((840268633967/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT271 (i+1))
      = (∑ i ∈ Finset.range 66, stT271 (i+1)) + stT271 67 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 66
    simpa using h
  have hprev := st271_p66
  have hstep := st271_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p68 : ((8965986791111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT271 (i+1))
      = (∑ i ∈ Finset.range 67, stT271 (i+1)) + stT271 68 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 67
    simpa using h
  have hprev := st271_p67
  have hstep := st271_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p69 : ((3368112687967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT271 (i+1))
      = (∑ i ∈ Finset.range 68, stT271 (i+1)) + stT271 69 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 68
    simpa using h
  have hprev := st271_p68
  have hstep := st271_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p70 : ((3456162744271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT271 (i+1))
      = (∑ i ∈ Finset.range 69, stT271 (i+1)) + stT271 70 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 69
    simpa using h
  have hprev := st271_p69
  have hstep := st271_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p71 : ((17659881067003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT271 (i+1))
      = (∑ i ∈ Finset.range 70, stT271 (i+1)) + stT271 71 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 70
    simpa using h
  have hprev := st271_p70
  have hstep := st271_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p72 : ((16685125542219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT271 (i+1))
      = (∑ i ∈ Finset.range 71, stT271 (i+1)) + stT271 72 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 71
    simpa using h
  have hprev := st271_p71
  have hstep := st271_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p73 : ((17855478021669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT271 (i+1))
      = (∑ i ∈ Finset.range 72, stT271 (i+1)) + stT271 73 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 72
    simpa using h
  have hprev := st271_p72
  have hstep := st271_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p74 : ((3372267398217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT271 (i+1))
      = (∑ i ∈ Finset.range 73, stT271 (i+1)) + stT271 74 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 73
    simpa using h
  have hprev := st271_p73
  have hstep := st271_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p75 : ((3488955144837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT271 (i+1))
      = (∑ i ∈ Finset.range 74, stT271 (i+1)) + stT271 75 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 74
    simpa using h
  have hprev := st271_p74
  have hstep := st271_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p76 : ((4337719246081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT271 (i+1))
      = (∑ i ∈ Finset.range 75, stT271 (i+1)) + stT271 76 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 75
    simpa using h
  have hprev := st271_p75
  have hstep := st271_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p77 : ((8496685023229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT271 (i+1))
      = (∑ i ∈ Finset.range 76, stT271 (i+1)) + stT271 77 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 76
    simpa using h
  have hprev := st271_p76
  have hstep := st271_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p78 : ((3540045812859/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT271 (i+1))
      = (∑ i ∈ Finset.range 77, stT271 (i+1)) + stT271 78 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 77
    simpa using h
  have hprev := st271_p77
  have hstep := st271_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p79 : ((3352539771867/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT271 (i+1))
      = (∑ i ∈ Finset.range 78, stT271 (i+1)) + stT271 79 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 78
    simpa using h
  have hprev := st271_p78
  have hstep := st271_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p80 : ((142595332297/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT271 (i+1))
      = (∑ i ∈ Finset.range 79, stT271 (i+1)) + stT271 80 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 79
    simpa using h
  have hprev := st271_p79
  have hstep := st271_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p81 : ((3343624241529/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT271 (i+1))
      = (∑ i ∈ Finset.range 80, stT271 (i+1)) + stT271 81 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 80
    simpa using h
  have hprev := st271_p80
  have hstep := st271_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p82 : ((890895922749/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT271 (i+1))
      = (∑ i ∈ Finset.range 81, stT271 (i+1)) + stT271 82 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 81
    simpa using h
  have hprev := st271_p81
  have hstep := st271_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p83 : ((8374970177349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT271 (i+1))
      = (∑ i ∈ Finset.range 82, stT271 (i+1)) + stT271 83 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 82
    simpa using h
  have hprev := st271_p82
  have hstep := st271_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p84 : ((4444884440209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT271 (i+1))
      = (∑ i ∈ Finset.range 83, stT271 (i+1)) + stT271 84 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 83
    simpa using h
  have hprev := st271_p83
  have hstep := st271_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p85 : ((4195401234373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT271 (i+1))
      = (∑ i ∈ Finset.range 84, stT271 (i+1)) + stT271 85 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 84
    simpa using h
  have hprev := st271_p84
  have hstep := st271_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p86 : ((8880689659827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT271 (i+1))
      = (∑ i ∈ Finset.range 85, stT271 (i+1)) + stT271 86 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 85
    simpa using h
  have hprev := st271_p85
  have hstep := st271_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p87 : ((33566671317/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT271 (i+1))
      = (∑ i ∈ Finset.range 86, stT271 (i+1)) + stT271 87 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 86
    simpa using h
  have hprev := st271_p86
  have hstep := st271_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p88 : ((17774133212853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT271 (i+1))
      = (∑ i ∈ Finset.range 87, stT271 (i+1)) + stT271 88 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 87
    simpa using h
  have hprev := st271_p87
  have hstep := st271_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p89 : ((16760898084621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT271 (i+1))
      = (∑ i ∈ Finset.range 88, stT271 (i+1)) + stT271 89 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 88
    simpa using h
  have hprev := st271_p88
  have hstep := st271_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p90 : ((17797011491469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT271 (i+1))
      = (∑ i ∈ Finset.range 89, stT271 (i+1)) + stT271 90 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 89
    simpa using h
  have hprev := st271_p89
  have hstep := st271_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p91 : ((8374707607357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT271 (i+1))
      = (∑ i ∈ Finset.range 90, stT271 (i+1)) + stT271 91 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 90
    simpa using h
  have hprev := st271_p90
  have hstep := st271_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p92 : ((8890704639601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT271 (i+1))
      = (∑ i ∈ Finset.range 91, stT271 (i+1)) + stT271 92 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 91
    simpa using h
  have hprev := st271_p91
  have hstep := st271_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p93 : ((8404362226653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT271 (i+1))
      = (∑ i ∈ Finset.range 92, stT271 (i+1)) + stT271 93 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 92
    simpa using h
  have hprev := st271_p92
  have hstep := st271_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p94 : ((3532310775147/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT271 (i+1))
      = (∑ i ∈ Finset.range 93, stT271 (i+1)) + stT271 94 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 93
    simpa using h
  have hprev := st271_p93
  have hstep := st271_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p95 : ((8500381433487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT271 (i+1))
      = (∑ i ∈ Finset.range 94, stT271 (i+1)) + stT271 95 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 94
    simpa using h
  have hprev := st271_p94
  have hstep := st271_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p96 : ((8697131453987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT271 (i+1))
      = (∑ i ∈ Finset.range 95, stT271 (i+1)) + stT271 96 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 95
    simpa using h
  have hprev := st271_p95
  have hstep := st271_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p97 : ((17330709293203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT271 (i+1))
      = (∑ i ∈ Finset.range 96, stT271 (i+1)) + stT271 97 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 96
    simpa using h
  have hprev := st271_p96
  have hstep := st271_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p98 : ((17032623244433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT271 (i+1))
      = (∑ i ∈ Finset.range 97, stT271 (i+1)) + stT271 98 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 97
    simpa using h
  have hprev := st271_p97
  have hstep := st271_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p99 : ((8836076706729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT271 (i+1))
      = (∑ i ∈ Finset.range 98, stT271 (i+1)) + stT271 99 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 98
    simpa using h
  have hprev := st271_p98
  have hstep := st271_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p100 : ((8388703206729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT271 (i+1))
      = (∑ i ∈ Finset.range 99, stT271 (i+1)) + stT271 100 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 99
    simpa using h
  have hprev := st271_p99
  have hstep := st271_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p101 : ((8886116232807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT271 (i+1))
      = (∑ i ∈ Finset.range 100, stT271 (i+1)) + stT271 101 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 100
    simpa using h
  have hprev := st271_p100
  have hstep := st271_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p102 : ((8441083322579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT271 (i+1))
      = (∑ i ∈ Finset.range 101, stT271 (i+1)) + stT271 102 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 101
    simpa using h
  have hprev := st271_p101
  have hstep := st271_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p103 : ((17454225999991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT271 (i+1))
      = (∑ i ∈ Finset.range 102, stT271 (i+1)) + stT271 103 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 102
    simpa using h
  have hprev := st271_p102
  have hstep := st271_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p104 : ((17359911758249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT271 (i+1))
      = (∑ i ∈ Finset.range 103, stT271 (i+1)) + stT271 104 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 103
    simpa using h
  have hprev := st271_p103
  have hstep := st271_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p105 : ((8466821540477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT271 (i+1))
      = (∑ i ∈ Finset.range 104, stT271 (i+1)) + stT271 105 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 104
    simpa using h
  have hprev := st271_p104
  have hstep := st271_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p106 : ((2220460719853/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT271 (i+1))
      = (∑ i ∈ Finset.range 105, stT271 (i+1)) + stT271 106 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 105
    simpa using h
  have hprev := st271_p105
  have hstep := st271_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p107 : ((8399078590037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT271 (i+1))
      = (∑ i ∈ Finset.range 106, stT271 (i+1)) + stT271 107 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 106
    simpa using h
  have hprev := st271_p106
  have hstep := st271_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p108 : ((4387839351331/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT271 (i+1))
      = (∑ i ∈ Finset.range 107, stT271 (i+1)) + stT271 108 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 107
    simpa using h
  have hprev := st271_p107
  have hstep := st271_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p109 : ((4327365985859/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT271 (i+1))
      = (∑ i ∈ Finset.range 108, stT271 (i+1)) + stT271 109 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 108
    simpa using h
  have hprev := st271_p108
  have hstep := st271_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p110 : ((16928108300789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT271 (i+1))
      = (∑ i ∈ Finset.range 109, stT271 (i+1)) + stT271 110 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 109
    simpa using h
  have hprev := st271_p109
  have hstep := st271_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p111 : ((444354267873/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT271 (i+1))
      = (∑ i ∈ Finset.range 110, stT271 (i+1)) + stT271 111 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 110
    simpa using h
  have hprev := st271_p110
  have hstep := st271_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p112 : ((2107059376907/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT271 (i+1))
      = (∑ i ∈ Finset.range 111, stT271 (i+1)) + stT271 112 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 111
    simpa using h
  have hprev := st271_p111
  have hstep := st271_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p113 : ((2173189405927/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT271 (i+1))
      = (∑ i ∈ Finset.range 112, stT271 (i+1)) + stT271 113 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 112
    simpa using h
  have hprev := st271_p112
  have hstep := st271_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p114 : ((136965156937/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT271 (i+1))
      = (∑ i ∈ Finset.range 113, stT271 (i+1)) + stT271 114 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 113
    simpa using h
  have hprev := st271_p113
  have hstep := st271_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p115 : ((16783220678021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT271 (i+1))
      = (∑ i ∈ Finset.range 114, stT271 (i+1)) + stT271 115 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 114
    simpa using h
  have hprev := st271_p114
  have hstep := st271_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p116 : ((17700398982053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT271 (i+1))
      = (∑ i ∈ Finset.range 115, stT271 (i+1)) + stT271 116 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 115
    simpa using h
  have hprev := st271_p115
  have hstep := st271_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p117 : ((4294666290803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT271 (i+1))
      = (∑ i ∈ Finset.range 116, stT271 (i+1)) + stT271 117 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 116
    simpa using h
  have hprev := st271_p116
  have hstep := st271_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p118 : ((16963715503587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT271 (i+1))
      = (∑ i ∈ Finset.range 117, stT271 (i+1)) + stT271 118 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 117
    simpa using h
  have hprev := st271_p117
  have hstep := st271_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p119 : ((17776564453959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT271 (i+1))
      = (∑ i ∈ Finset.range 118, stT271 (i+1)) + stT271 119 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 118
    simpa using h
  have hprev := st271_p118
  have hstep := st271_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p120 : ((16933340034033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT271 (i+1))
      = (∑ i ∈ Finset.range 119, stT271 (i+1)) + stT271 120 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 119
    simpa using h
  have hprev := st271_p119
  have hstep := st271_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p121 : ((17188799778573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT271 (i+1))
      = (∑ i ∈ Finset.range 120, stT271 (i+1)) + stT271 121 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 120
    simpa using h
  have hprev := st271_p120
  have hstep := st271_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p122 : ((3543876125399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT271 (i+1))
      = (∑ i ∈ Finset.range 121, stT271 (i+1)) + stT271 122 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 121
    simpa using h
  have hprev := st271_p121
  have hstep := st271_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p123 : ((3363554027443/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT271 (i+1))
      = (∑ i ∈ Finset.range 122, stT271 (i+1)) + stT271 123 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 122
    simpa using h
  have hprev := st271_p122
  have hstep := st271_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p124 : ((17353136419349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT271 (i+1))
      = (∑ i ∈ Finset.range 123, stT271 (i+1)) + stT271 124 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 123
    simpa using h
  have hprev := st271_p123
  have hstep := st271_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p125 : ((2204952338021/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT271 (i+1))
      = (∑ i ∈ Finset.range 124, stT271 (i+1)) + stT271 125 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 124
    simpa using h
  have hprev := st271_p124
  have hstep := st271_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p126 : ((16779218164981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT271 (i+1))
      = (∑ i ∈ Finset.range 125, stT271 (i+1)) + stT271 126 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 125
    simpa using h
  have hprev := st271_p125
  have hstep := st271_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p127 : ((3487271527397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT271 (i+1))
      = (∑ i ∈ Finset.range 126, stT271 (i+1)) + stT271 127 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 126
    simpa using h
  have hprev := st271_p126
  have hstep := st271_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p128 : ((351927781471/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT271 (i+1))
      = (∑ i ∈ Finset.range 127, stT271 (i+1)) + stT271 128 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 127
    simpa using h
  have hprev := st271_p127
  have hstep := st271_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p129 : ((8385560610213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT271 (i+1))
      = (∑ i ∈ Finset.range 128, stT271 (i+1)) + stT271 129 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 128
    simpa using h
  have hprev := st271_p128
  have hstep := st271_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p130 : ((8722952544001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT271 (i+1))
      = (∑ i ∈ Finset.range 129, stT271 (i+1)) + stT271 130 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 129
    simpa using h
  have hprev := st271_p129
  have hstep := st271_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p131 : ((8804151535797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT271 (i+1))
      = (∑ i ∈ Finset.range 130, stT271 (i+1)) + stT271 131 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 130
    simpa using h
  have hprev := st271_p130
  have hstep := st271_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p132 : ((8388765348659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT271 (i+1))
      = (∑ i ∈ Finset.range 131, stT271 (i+1)) + stT271 132 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 131
    simpa using h
  have hprev := st271_p131
  have hstep := st271_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p133 : ((1086611569749/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT271 (i+1))
      = (∑ i ∈ Finset.range 132, stT271 (i+1)) + stT271 133 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 132
    simpa using h
  have hprev := st271_p132
  have hstep := st271_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p134 : ((88345073031/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT271 (i+1))
      = (∑ i ∈ Finset.range 133, stT271 (i+1)) + stT271 134 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 133
    simpa using h
  have hprev := st271_p133
  have hstep := st271_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p135 : ((1050844293681/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT271 (i+1))
      = (∑ i ∈ Finset.range 134, stT271 (i+1)) + stT271 135 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 134
    simpa using h
  have hprev := st271_p134
  have hstep := st271_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p136 : ((2156717493343/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT271 (i+1))
      = (∑ i ∈ Finset.range 135, stT271 (i+1)) + stT271 136 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 135
    simpa using h
  have hprev := st271_p135
  have hstep := st271_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p137 : ((8874019220689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT271 (i+1))
      = (∑ i ∈ Finset.range 136, stT271 (i+1)) + stT271 137 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 136
    simpa using h
  have hprev := st271_p136
  have hstep := st271_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p138 : ((16916688086323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT271 (i+1))
      = (∑ i ∈ Finset.range 137, stT271 (i+1)) + stT271 138 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 137
    simpa using h
  have hprev := st271_p137
  have hstep := st271_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p139 : ((17059294782951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT271 (i+1))
      = (∑ i ∈ Finset.range 138, stT271 (i+1)) + stT271 139 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 138
    simpa using h
  have hprev := st271_p138
  have hstep := st271_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p140 : ((3556755707997/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT271 (i+1))
      = (∑ i ∈ Finset.range 139, stT271 (i+1)) + stT271 140 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 139
    simpa using h
  have hprev := st271_p139
  have hstep := st271_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p141 : ((17124648065537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT271 (i+1))
      = (∑ i ∈ Finset.range 140, stT271 (i+1)) + stT271 141 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 140
    simpa using h
  have hprev := st271_p140
  have hstep := st271_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p142 : ((16854652166403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT271 (i+1))
      = (∑ i ∈ Finset.range 141, stT271 (i+1)) + stT271 142 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 141
    simpa using h
  have hprev := st271_p141
  have hstep := st271_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p143 : ((17690847336851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT271 (i+1))
      = (∑ i ∈ Finset.range 142, stT271 (i+1)) + stT271 143 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 142
    simpa using h
  have hprev := st271_p142
  have hstep := st271_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p144 : ((139422017011/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT271 (i+1))
      = (∑ i ∈ Finset.range 143, stT271 (i+1)) + stT271 144 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 143
    simpa using h
  have hprev := st271_p143
  have hstep := st271_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p145 : ((335092785659/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT271 (i+1))
      = (∑ i ∈ Finset.range 144, stT271 (i+1)) + stT271 145 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 144
    simpa using h
  have hprev := st271_p144
  have hstep := st271_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p146 : ((348236477227/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT271 (i+1))
      = (∑ i ∈ Finset.range 145, stT271 (i+1)) + stT271 146 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 145
    simpa using h
  have hprev := st271_p145
  have hstep := st271_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p147 : ((8856631674743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT271 (i+1))
      = (∑ i ∈ Finset.range 146, stT271 (i+1)) + stT271 147 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 146
    simpa using h
  have hprev := st271_p146
  have hstep := st271_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p148 : ((8447994944383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT271 (i+1))
      = (∑ i ∈ Finset.range 147, stT271 (i+1)) + stT271 148 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 147
    simpa using h
  have hprev := st271_p147
  have hstep := st271_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p149 : ((8507748015061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT271 (i+1))
      = (∑ i ∈ Finset.range 148, stT271 (i+1)) + stT271 149 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 148
    simpa using h
  have hprev := st271_p148
  have hstep := st271_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p150 : ((8885576231837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT271 (i+1))
      = (∑ i ∈ Finset.range 149, stT271 (i+1)) + stT271 150 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 149
    simpa using h
  have hprev := st271_p149
  have hstep := st271_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p151 : ((17299442111191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT271 (i+1))
      = (∑ i ∈ Finset.range 150, stT271 (i+1)) + stT271 151 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 150
    simpa using h
  have hprev := st271_p150
  have hstep := st271_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p152 : ((3351148525991/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT271 (i+1))
      = (∑ i ∈ Finset.range 151, stT271 (i+1)) + stT271 152 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 151
    simpa using h
  have hprev := st271_p151
  have hstep := st271_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p153 : ((17453930670127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT271 (i+1))
      = (∑ i ∈ Finset.range 152, stT271 (i+1)) + stT271 153 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 152
    simpa using h
  have hprev := st271_p152
  have hstep := st271_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p154 : ((17717770491901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT271 (i+1))
      = (∑ i ∈ Finset.range 153, stT271 (i+1)) + stT271 154 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 153
    simpa using h
  have hprev := st271_p153
  have hstep := st271_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p155 : ((16923573865381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT271 (i+1))
      = (∑ i ∈ Finset.range 154, stT271 (i+1)) + stT271 155 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 154
    simpa using h
  have hprev := st271_p154
  have hstep := st271_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p156 : ((16940831660581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT271 (i+1))
      = (∑ i ∈ Finset.range 155, stT271 (i+1)) + stT271 156 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 155
    simpa using h
  have hprev := st271_p155
  have hstep := st271_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p157 : ((17725631922939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT271 (i+1))
      = (∑ i ∈ Finset.range 156, stT271 (i+1)) + stT271 157 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 156
    simpa using h
  have hprev := st271_p156
  have hstep := st271_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p158 : ((17466079534323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT271 (i+1))
      = (∑ i ∈ Finset.range 157, stT271 (i+1)) + stT271 158 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 157
    simpa using h
  have hprev := st271_p157
  have hstep := st271_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p159 : ((16759440066347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT271 (i+1))
      = (∑ i ∈ Finset.range 158, stT271 (i+1)) + stT271 159 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 158
    simpa using h
  have hprev := st271_p158
  have hstep := st271_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p160 : ((860274626791/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT271 (i+1))
      = (∑ i ∈ Finset.range 159, stT271 (i+1)) + stT271 160 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 159
    simpa using h
  have hprev := st271_p159
  have hstep := st271_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p161 : ((13905784649/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT271 (i+1))
      = (∑ i ∈ Finset.range 160, stT271 (i+1)) + stT271 161 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 160
    simpa using h
  have hprev := st271_p160
  have hstep := st271_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p162 : ((3444508424769/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT271 (i+1))
      = (∑ i ∈ Finset.range 161, stT271 (i+1)) + stT271 162 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 161
    simpa using h
  have hprev := st271_p161
  have hstep := st271_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p163 : ((8374418026719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT271 (i+1))
      = (∑ i ∈ Finset.range 162, stT271 (i+1)) + stT271 163 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 162
    simpa using h
  have hprev := st271_p162
  have hstep := st271_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p164 : ((8704626020483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT271 (i+1))
      = (∑ i ∈ Finset.range 163, stT271 (i+1)) + stT271 164 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 163
    simpa using h
  have hprev := st271_p163
  have hstep := st271_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p165 : ((1110808301947/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT271 (i+1))
      = (∑ i ∈ Finset.range 164, stT271 (i+1)) + stT271 165 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 164
    simpa using h
  have hprev := st271_p164
  have hstep := st271_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p166 : ((8532014553047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT271 (i+1))
      = (∑ i ∈ Finset.range 165, stT271 (i+1)) + stT271 166 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 165
    simpa using h
  have hprev := st271_p165
  have hstep := st271_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p167 : ((1678950653003/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT271 (i+1))
      = (∑ i ∈ Finset.range 166, stT271 (i+1)) + stT271 167 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 166
    simpa using h
  have hprev := st271_p166
  have hstep := st271_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p168 : ((1752290192447/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT271 (i+1))
      = (∑ i ∈ Finset.range 167, stT271 (i+1)) + stT271 168 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 167
    simpa using h
  have hprev := st271_p167
  have hstep := st271_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p169 : ((1773394325189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT271 (i+1))
      = (∑ i ∈ Finset.range 168, stT271 (i+1)) + stT271 169 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 168
    simpa using h
  have hprev := st271_p168
  have hstep := st271_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p170 : ((3398154668203/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT271 (i+1))
      = (∑ i ∈ Finset.range 169, stT271 (i+1)) + stT271 170 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 169
    simpa using h
  have hprev := st271_p169
  have hstep := st271_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p171 : ((3363085373723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT271 (i+1))
      = (∑ i ∈ Finset.range 170, stT271 (i+1)) + stT271 171 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 170
    simpa using h
  have hprev := st271_p170
  have hstep := st271_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p172 : ((17559181390207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT271 (i+1))
      = (∑ i ∈ Finset.range 171, stT271 (i+1)) + stT271 172 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 171
    simpa using h
  have hprev := st271_p171
  have hstep := st271_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p173 : ((1107895390377/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT271 (i+1))
      = (∑ i ∈ Finset.range 172, stT271 (i+1)) + stT271 173 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 172
    simpa using h
  have hprev := st271_p172
  have hstep := st271_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p174 : ((679529854653/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT271 (i+1))
      = (∑ i ∈ Finset.range 173, stT271 (i+1)) + stT271 174 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 173
    simpa using h
  have hprev := st271_p173
  have hstep := st271_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p175 : ((8401210815879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT271 (i+1))
      = (∑ i ∈ Finset.range 174, stT271 (i+1)) + stT271 175 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 174
    simpa using h
  have hprev := st271_p174
  have hstep := st271_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p176 : ((4381961944961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT271 (i+1))
      = (∑ i ∈ Finset.range 175, stT271 (i+1)) + stT271 176 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 175
    simpa using h
  have hprev := st271_p175
  have hstep := st271_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p177 : ((8878667537521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT271 (i+1))
      = (∑ i ∈ Finset.range 176, stT271 (i+1)) + stT271 177 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 176
    simpa using h
  have hprev := st271_p176
  have hstep := st271_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p178 : ((8527167010801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT271 (i+1))
      = (∑ i ∈ Finset.range 177, stT271 (i+1)) + stT271 178 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 177
    simpa using h
  have hprev := st271_p177
  have hstep := st271_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p179 : ((8379234103963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT271 (i+1))
      = (∑ i ∈ Finset.range 178, stT271 (i+1)) + stT271 179 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 178
    simpa using h
  have hprev := st271_p178
  have hstep := st271_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p180 : ((17423644625221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT271 (i+1))
      = (∑ i ∈ Finset.range 179, stT271 (i+1)) + stT271 180 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 179
    simpa using h
  have hprev := st271_p179
  have hstep := st271_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p181 : ((17804094456063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT271 (i+1))
      = (∑ i ∈ Finset.range 180, stT271 (i+1)) + stT271 181 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 180
    simpa using h
  have hprev := st271_p180
  have hstep := st271_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p182 : ((17198659246063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT271 (i+1))
      = (∑ i ∈ Finset.range 181, stT271 (i+1)) + stT271 182 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 181
    simpa using h
  have hprev := st271_p181
  have hstep := st271_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p183 : ((16721875101281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT271 (i+1))
      = (∑ i ∈ Finset.range 182, stT271 (i+1)) + stT271 183 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 182
    simpa using h
  have hprev := st271_p182
  have hstep := st271_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p184 : ((4309538405529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT271 (i+1))
      = (∑ i ∈ Finset.range 183, stT271 (i+1)) + stT271 184 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 183
    simpa using h
  have hprev := st271_p183
  have hstep := st271_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p185 : ((8906290733407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT271 (i+1))
      = (∑ i ∈ Finset.range 184, stT271 (i+1)) + stT271 185 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 184
    simpa using h
  have hprev := st271_p184
  have hstep := st271_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p186 : ((8710267421167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT271 (i+1))
      = (∑ i ∈ Finset.range 185, stT271 (i+1)) + stT271 186 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 185
    simpa using h
  have hprev := st271_p185
  have hstep := st271_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p187 : ((1676087686977/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT271 (i+1))
      = (∑ i ∈ Finset.range 186, stT271 (i+1)) + stT271 187 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 186
    simpa using h
  have hprev := st271_p186
  have hstep := st271_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p188 : ((8495443348473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT271 (i+1))
      = (∑ i ∈ Finset.range 187, stT271 (i+1)) + stT271 188 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 187
    simpa using h
  have hprev := st271_p187
  have hstep := st271_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p189 : ((8852727024297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT271 (i+1))
      = (∑ i ∈ Finset.range 188, stT271 (i+1)) + stT271 189 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 188
    simpa using h
  have hprev := st271_p188
  have hstep := st271_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p190 : ((1767128988571/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT271 (i+1))
      = (∑ i ∈ Finset.range 189, stT271 (i+1)) + stT271 190 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 189
    simpa using h
  have hprev := st271_p189
  have hstep := st271_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p191 : ((3390275379757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT271 (i+1))
      = (∑ i ∈ Finset.range 190, stT271 (i+1)) + stT271 191 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 190
    simpa using h
  have hprev := st271_p190
  have hstep := st271_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p192 : ((16768034227449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT271 (i+1))
      = (∑ i ∈ Finset.range 191, stT271 (i+1)) + stT271 192 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 191
    simpa using h
  have hprev := st271_p191
  have hstep := st271_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p193 : ((17425307381359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT271 (i+1))
      = (∑ i ∈ Finset.range 192, stT271 (i+1)) + stT271 193 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 192
    simpa using h
  have hprev := st271_p192
  have hstep := st271_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p194 : ((17824765571357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT271 (i+1))
      = (∑ i ∈ Finset.range 193, stT271 (i+1)) + stT271 194 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 193
    simpa using h
  have hprev := st271_p193
  have hstep := st271_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p195 : ((17309409114917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT271 (i+1))
      = (∑ i ∈ Finset.range 194, stT271 (i+1)) + stT271 195 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 194
    simpa using h
  have hprev := st271_p194
  have hstep := st271_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p196 : ((16727463882139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT271 (i+1))
      = (∑ i ∈ Finset.range 195, stT271 (i+1)) + stT271 196 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 195
    simpa using h
  have hprev := st271_p195
  have hstep := st271_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p197 : ((17022479184919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT271 (i+1))
      = (∑ i ∈ Finset.range 196, stT271 (i+1)) + stT271 197 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 196
    simpa using h
  have hprev := st271_p196
  have hstep := st271_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p198 : ((3542933305381/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT271 (i+1))
      = (∑ i ∈ Finset.range 197, stT271 (i+1)) + stT271 198 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 197
    simpa using h
  have hprev := st271_p197
  have hstep := st271_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p199 : ((17698479915317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT271 (i+1))
      = (∑ i ∈ Finset.range 198, stT271 (i+1)) + stT271 199 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 198
    simpa using h
  have hprev := st271_p198
  have hstep := st271_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p200 : ((8502006226471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT271 (i+1))
      = (∑ i ∈ Finset.range 199, stT271 (i+1)) + stT271 200 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 199
    simpa using h
  have hprev := st271_p199
  have hstep := st271_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p201 : ((8361804602051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT271 (i+1))
      = (∑ i ∈ Finset.range 200, stT271 (i+1)) + stT271 201 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 200
    simpa using h
  have hprev := st271_p200
  have hstep := st271_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p202 : ((138321214727/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT271 (i+1))
      = (∑ i ∈ Finset.range 201, stT271 (i+1)) + stT271 202 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 201
    simpa using h
  have hprev := st271_p201
  have hstep := st271_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p203 : ((17825301261877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT271 (i+1))
      = (∑ i ∈ Finset.range 202, stT271 (i+1)) + stT271 203 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 202
    simpa using h
  have hprev := st271_p202
  have hstep := st271_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p204 : ((8755812395599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT271 (i+1))
      = (∑ i ∈ Finset.range 203, stT271 (i+1)) + stT271 204 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 203
    simpa using h
  have hprev := st271_p203
  have hstep := st271_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p205 : ((4207455858327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT271 (i+1))
      = (∑ i ∈ Finset.range 204, stT271 (i+1)) + stT271 205 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 204
    simpa using h
  have hprev := st271_p204
  have hstep := st271_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p206 : ((2100835263779/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT271 (i+1))
      = (∑ i ∈ Finset.range 205, stT271 (i+1)) + stT271 206 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 205
    simpa using h
  have hprev := st271_p205
  have hstep := st271_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p207 : ((546010929257/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT271 (i+1))
      = (∑ i ∈ Finset.range 206, stT271 (i+1)) + stT271 207 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 206
    simpa using h
  have hprev := st271_p206
  have hstep := st271_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p208 : ((2229812707403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT271 (i+1))
      = (∑ i ∈ Finset.range 207, stT271 (i+1)) + stT271 208 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 207
    simpa using h
  have hprev := st271_p207
  have hstep := st271_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p209 : ((2171290851543/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT271 (i+1))
      = (∑ i ∈ Finset.range 208, stT271 (i+1)) + stT271 209 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 208
    simpa using h
  have hprev := st271_p208
  have hstep := st271_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p210 : ((8376926450457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT271 (i+1))
      = (∑ i ∈ Finset.range 209, stT271 (i+1)) + stT271 210 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 209
    simpa using h
  have hprev := st271_p209
  have hstep := st271_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p211 : ((8439470478471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT271 (i+1))
      = (∑ i ∈ Finset.range 210, stT271 (i+1)) + stT271 211 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 210
    simpa using h
  have hprev := st271_p210
  have hstep := st271_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p212 : ((2195225175033/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT271 (i+1))
      = (∑ i ∈ Finset.range 211, stT271 (i+1)) + stT271 212 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 211
    simpa using h
  have hprev := st271_p211
  have hstep := st271_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p213 : ((2228748340527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT271 (i+1))
      = (∑ i ∈ Finset.range 212, stT271 (i+1)) + stT271 213 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 212
    simpa using h
  have hprev := st271_p212
  have hstep := st271_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p214 : ((4327184340081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT271 (i+1))
      = (∑ i ∈ Finset.range 213, stT271 (i+1)) + stT271 214 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 213
    simpa using h
  have hprev := st271_p213
  have hstep := st271_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p215 : ((4182695515391/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT271 (i+1))
      = (∑ i ∈ Finset.range 214, stT271 (i+1)) + stT271 215 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 214
    simpa using h
  have hprev := st271_p214
  have hstep := st271_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p216 : ((16896765410849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT271 (i+1))
      = (∑ i ∈ Finset.range 215, stT271 (i+1)) + stT271 216 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 215
    simpa using h
  have hprev := st271_p215
  have hstep := st271_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p217 : ((17573787393553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT271 (i+1))
      = (∑ i ∈ Finset.range 216, stT271 (i+1)) + stT271 217 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 216
    simpa using h
  have hprev := st271_p216
  have hstep := st271_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p218 : ((4458971293677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT271 (i+1))
      = (∑ i ∈ Finset.range 217, stT271 (i+1)) + stT271 218 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 217
    simpa using h
  have hprev := st271_p217
  have hstep := st271_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p219 : ((8665686551133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT271 (i+1))
      = (∑ i ∈ Finset.range 218, stT271 (i+1)) + stT271 219 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 218
    simpa using h
  have hprev := st271_p218
  have hstep := st271_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p220 : ((8370925974033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT271 (i+1))
      = (∑ i ∈ Finset.range 219, stT271 (i+1)) + stT271 220 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 219
    simpa using h
  have hprev := st271_p219
  have hstep := st271_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p221 : ((8426134183089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT271 (i+1))
      = (∑ i ∈ Finset.range 220, stT271 (i+1)) + stT271 221 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 220
    simpa using h
  have hprev := st271_p220
  have hstep := st271_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p222 : ((350245153453/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT271 (i+1))
      = (∑ i ∈ Finset.range 221, stT271 (i+1)) + stT271 222 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 221
    simpa using h
  have hprev := st271_p221
  have hstep := st271_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p223 : ((8926879956239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT271 (i+1))
      = (∑ i ∈ Finset.range 222, stT271 (i+1)) + stT271 223 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 222
    simpa using h
  have hprev := st271_p222
  have hstep := st271_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p224 : ((8717493855719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT271 (i+1))
      = (∑ i ∈ Finset.range 223, stT271 (i+1)) + stT271 224 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 223
    simpa using h
  have hprev := st271_p223
  have hstep := st271_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p225 : ((16800816061019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT271 (i+1))
      = (∑ i ∈ Finset.range 224, stT271 (i+1)) + stT271 225 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 224
    simpa using h
  have hprev := st271_p224
  have hstep := st271_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p226 : ((670559004907/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT271 (i+1))
      = (∑ i ∈ Finset.range 225, stT271 (i+1)) + stT271 226 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 225
    simpa using h
  have hprev := st271_p225
  have hstep := st271_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p227 : ((8683665926051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT271 (i+1))
      = (∑ i ∈ Finset.range 226, stT271 (i+1)) + stT271 227 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 226
    simpa using h
  have hprev := st271_p226
  have hstep := st271_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p228 : ((446165890277/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT271 (i+1))
      = (∑ i ∈ Finset.range 227, stT271 (i+1)) + stT271 228 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 227
    simpa using h
  have hprev := st271_p227
  have hstep := st271_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p229 : ((17603495850677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT271 (i+1))
      = (∑ i ∈ Finset.range 228, stT271 (i+1)) + stT271 229 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 228
    simpa using h
  have hprev := st271_p228
  have hstep := st271_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p230 : ((3388827981431/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT271 (i+1))
      = (∑ i ∈ Finset.range 229, stT271 (i+1)) + stT271 230 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 229
    simpa using h
  have hprev := st271_p229
  have hstep := st271_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p231 : ((3336570801783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT271 (i+1))
      = (∑ i ∈ Finset.range 230, stT271 (i+1)) + stT271 231 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 230
    simpa using h
  have hprev := st271_p230
  have hstep := st271_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p232 : ((17136208394343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT271 (i+1))
      = (∑ i ∈ Finset.range 231, stT271 (i+1)) + stT271 232 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 231
    simpa using h
  have hprev := st271_p231
  have hstep := st271_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p233 : ((17749970295371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT271 (i+1))
      = (∑ i ∈ Finset.range 232, stT271 (i+1)) + stT271 233 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 232
    simpa using h
  have hprev := st271_p232
  have hstep := st271_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p234 : ((17784629876051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT271 (i+1))
      = (∑ i ∈ Finset.range 233, stT271 (i+1)) + stT271 234 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 233
    simpa using h
  have hprev := st271_p233
  have hstep := st271_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p235 : ((4300620422879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT271 (i+1))
      = (∑ i ∈ Finset.range 234, stT271 (i+1)) + stT271 235 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 234
    simpa using h
  have hprev := st271_p234
  have hstep := st271_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p236 : ((8348660515913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT271 (i+1))
      = (∑ i ∈ Finset.range 235, stT271 (i+1)) + stT271 236 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 235
    simpa using h
  have hprev := st271_p235
  have hstep := st271_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p237 : ((16862761709143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT271 (i+1))
      = (∑ i ∈ Finset.range 236, stT271 (i+1)) + stT271 237 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 236
    simpa using h
  have hprev := st271_p236
  have hstep := st271_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p238 : ((17501349265841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT271 (i+1))
      = (∑ i ∈ Finset.range 237, stT271 (i+1)) + stT271 238 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 237
    simpa using h
  have hprev := st271_p237
  have hstep := st271_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p239 : ((17870116170441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT271 (i+1))
      = (∑ i ∈ Finset.range 238, stT271 (i+1)) + stT271 239 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 238
    simpa using h
  have hprev := st271_p238
  have hstep := st271_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p240 : ((17546639048697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT271 (i+1))
      = (∑ i ∈ Finset.range 239, stT271 (i+1)) + stT271 240 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 239
    simpa using h
  have hprev := st271_p239
  have hstep := st271_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p241 : ((16904554945923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT271 (i+1))
      = (∑ i ∈ Finset.range 240, stT271 (i+1)) + stT271 241 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 240
    simpa using h
  have hprev := st271_p240
  have hstep := st271_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p242 : ((16673402789823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT271 (i+1))
      = (∑ i ∈ Finset.range 241, stT271 (i+1)) + stT271 242 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 241
    simpa using h
  have hprev := st271_p241
  have hstep := st271_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p243 : ((17110524097323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT271 (i+1))
      = (∑ i ∈ Finset.range 242, stT271 (i+1)) + stT271 243 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 242
    simpa using h
  have hprev := st271_p242
  have hstep := st271_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p244 : ((17723596304923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT271 (i+1))
      = (∑ i ∈ Finset.range 243, stT271 (i+1)) + stT271 244 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 243
    simpa using h
  have hprev := st271_p243
  have hstep := st271_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p245 : ((17831980979447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT271 (i+1))
      = (∑ i ∈ Finset.range 244, stT271 (i+1)) + stT271 245 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 244
    simpa using h
  have hprev := st271_p244
  have hstep := st271_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p246 : ((432989470857/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT271 (i+1))
      = (∑ i ∈ Finset.range 245, stT271 (i+1)) + stT271 246 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 245
    simpa using h
  have hprev := st271_p245
  have hstep := st271_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p247 : ((3349990846461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT271 (i+1))
      = (∑ i ∈ Finset.range 246, stT271 (i+1)) + stT271 247 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 246
    simpa using h
  have hprev := st271_p246
  have hstep := st271_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p248 : ((8370548936679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT271 (i+1))
      = (∑ i ∈ Finset.range 247, stT271 (i+1)) + stT271 248 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 247
    simpa using h
  have hprev := st271_p247
  have hstep := st271_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p249 : ((8649487625071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT271 (i+1))
      = (∑ i ∈ Finset.range 248, stT271 (i+1)) + stT271 249 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 248
    simpa using h
  have hprev := st271_p248
  have hstep := st271_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_p250 : ((1113984990377/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT271 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT271 (i+1))
      = (∑ i ∈ Finset.range 249, stT271 (i+1)) + stT271 250 := by
    have h := Finset.sum_range_succ (fun i => stT271 (i+1)) 249
    simpa using h
  have hprev := st271_p249
  have hstep := st271_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st271_s250 :
    |Real.sin (((271 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((162891/500000 : ℚ) : ℝ))
      - ((558049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1480081/10000000) (δ := 1361/100000000) (ψ := 162891/500000) 271 238
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 271`** (evaluated boundary). -/
theorem station_271_sign : hardyG ((((271:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 271 250 (by norm_num) (by norm_num)
    ((162891/500000 : ℚ) : ℝ)
  have hchain := st271_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT271 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((271 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((162891/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st271_c250
  have hsinb := abs_le.mp st271_s250
  have hbdy_lo : ((-5994882744103/183603125000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((271 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((162891/500000 : ℚ) : ℝ))) / 2
          - ((((271:ℕ)):ℝ))
            * Real.sin (((271 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((162891/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((271:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((271:ℝ) * Real.log (250:ℝ) - ((162891/500000 : ℚ) : ℝ))) / 2
        - ((271:ℝ)) * Real.sin ((271:ℝ) * Real.log (250:ℝ) - ((162891/500000 : ℚ) : ℝ))
        ≥ ((-75829879/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((271:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-75829879/500000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-75829879/500000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-75829879/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((271:ℕ)):ℝ))+1) * (((((271:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((31376379331/19531250000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1113984990377/625000000000 : ℚ) : ℝ) + ((-5994882744103/183603125000000 : ℚ) : ℝ)
      - ((31376379331/19531250000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((162891/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((271:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((162891/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((271:ℕ)):ℝ)))).re
      - Real.sin ((162891/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((271:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((271:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((271:ℕ)):ℝ))
      = (((((271:ℕ)):ℝ)) * (Real.log ((((271:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((271:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_271
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
  have hθwin : |(((162891/500000 : ℚ) : ℝ) + ((60:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((271:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((271:ℕ)):ℝ)))
    (φ := ((162891/500000 : ℚ) : ℝ) + ((60:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((162891/500000 : ℚ) : ℝ) + ((60:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((162891/500000 : ℚ)) : ℝ) - Real.pi) + ((60:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((162891/500000 : ℚ)) : ℝ) - Real.pi) 60).1,
    (cos_sin_shift ((((162891/500000 : ℚ)) : ℝ) - Real.pi) 60).2]
  exact cos_sin_flip ((162891/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_271_sign
end AxiomAudit
