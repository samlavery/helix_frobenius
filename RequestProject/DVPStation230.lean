import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 230` (rung-235.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT230 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((230 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((96253/500000 : ℚ) : ℝ))

theorem st230_c1 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((122691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96253/2000000) (δ := 1/1000000000) (ψ := 96253/500000) 230 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t1 : ((490739/500000 : ℚ) : ℝ) ≤ stT230 1 := by
  have hc : ((490739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((490739/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((490739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c2 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-109757/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1075853/2000000) (δ := 11681/1000000000) (ψ := 96253/500000) 230 25
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t2 : ((-194042480289/500000000000 : ℚ) : ℝ) ≤ stT230 2 := by
  have hc : ((-109767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194042480289/500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-109767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c3 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((79703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 362781/1250000) (δ := 5757/500000000) (ψ := 96253/500000) 230 40
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t3 : ((230053847443/1000000000000 : ℚ) : ℝ) ≤ stT230 3 := by
  have hc : ((79693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230053847443/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((79693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c4 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-214773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223407/500000) (δ := 2917/250000000) (ψ := 96253/500000) 230 51
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t4 : ((-1074115214823/10000000000000 : ℚ) : ℝ) ≤ stT230 4 := by
  have hc : ((-214823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1074115214823/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-214823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c5 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((745367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1824277/10000000) (δ := 5839/500000000) (ψ := 96253/500000) 230 59
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t5 : ((666631648359/2000000000000 : ℚ) : ℝ) ≤ stT230 5 := by
  have hc : ((745317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((666631648359/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((745317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c6 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-116831/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6945157/10000000) (δ := 1441/125000000) (ψ := 96253/500000) 230 66
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t6 : ((-1907944347567/5000000000000 : ℚ) : ℝ) ≤ stT230 6 := by
  have hc : ((-467349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1907944347567/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-467349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c7 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((305177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3151679/10000000) (δ := 1449/125000000) (ψ := 96253/500000) 230 71
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t7 : ((288317858697/2500000000000 : ℚ) : ℝ) ≤ stT230 7 := by
  have hc : ((305127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((288317858697/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((305127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c8 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((424431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 696209/5000000) (δ := 11547/1000000000) (ψ := 96253/500000) 230 76
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t8 : ((750250709199/2500000000000 : ℚ) : ℝ) ≤ stT230 8 := by
  have hc : ((212203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((750250709199/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((212203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c9 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-809629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 628579/1000000) (δ := 1447/125000000) (ψ := 96253/500000) 230 80
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t9 : ((-1349465269893/5000000000000 : ℚ) : ℝ) ≤ stT230 9 := by
  have hc : ((-809679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1349465269893/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-809679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c10 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-43679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31533/78125) (δ := 5799/500000000) (ψ := 96253/500000) 230 84
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t10 : ((-69141627331/5000000000000 : ℚ) : ℝ) ≤ stT230 10 := by
  have hc : ((-43729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69141627331/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-43729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c11 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-13053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -499033/1250000) (δ := 1157/100000000) (ψ := 96253/500000) 230 88
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t11 : ((-9857915223/1250000000000 : ℚ) : ℝ) ≤ stT230 11 := by
  have hc : ((-6539/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9857915223/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-6539/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c12 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((453679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1084599/10000000) (δ := 91/7812500) (ψ := 96253/500000) 230 91
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t12 : ((654793069077/2500000000000 : ℚ) : ℝ) ≤ stT230 12 := by
  have hc : ((226827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((654793069077/2500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((226827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c13 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((64209/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17062/78125) (δ := 11527/1000000000) (ψ := 96253/500000) 230 94
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t13 : ((89034897/500000000 : ℚ) : ℝ) ≤ stT230 13 := by
  have hc : ((16051/25000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89034897/500000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((16051/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c14 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-447291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3347863/5000000) (δ := 2321/200000000) (ψ := 96253/500000) 230 97
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t14 : ((-298875639177/1250000000000 : ℚ) : ℝ) ≤ stT230 14 := by
  have hc : ((-111829/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298875639177/1250000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-111829/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c15 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((20293/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311853/2000000) (δ := 11591/1000000000) (ψ := 96253/500000) 230 99
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t15 : ((52393054999/250000000000 : ℚ) : ℝ) ≤ stT230 15 := by
  have hc : ((81167/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52393054999/250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((81167/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c16 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-485621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 453311/625000) (δ := 1447/125000000) (ψ := 96253/500000) 230 101
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t16 : ((-607057742823/2500000000000 : ℚ) : ℝ) ≤ stT230 16 := by
  have hc : ((-242823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-607057742823/2500000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-242823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c17 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-420423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5011769/10000000) (δ := 2331/200000000) (ψ := 96253/500000) 230 104
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t17 : ((-1019797133861/10000000000000 : ℚ) : ℝ) ≤ stT230 17 := by
  have hc : ((-420473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1019797133861/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-420473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c18 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((145631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -712323/2000000) (δ := 11563/1000000000) (ψ := 96253/500000) 230 106
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t18 : ((171568809891/5000000000000 : ℚ) : ℝ) ≤ stT230 18 := by
  have hc : ((145581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171568809891/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((145581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c19 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((3047/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1944451/5000000) (δ := 5813/500000000) (ψ := 96253/500000) 230 108
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t19 : ((6967354809/2000000000000 : ℚ) : ℝ) ≤ stT230 19 := by
  have hc : ((3037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6967354809/2000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((3037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c20 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-171081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5811181/10000000) (δ := 2903/250000000) (ψ := 96253/500000) 230 110
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t20 : ((-191288350179/1250000000000 : ℚ) : ℝ) ≤ stT230 20 := by
  have hc : ((-342187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191288350179/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-342187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c21 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-432033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6535221/10000000) (δ := 2301/200000000) (ψ := 96253/500000) 230 111
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t21 : ((-471413947191/2500000000000 : ℚ) : ℝ) ≤ stT230 21 := by
  have hc : ((-216029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-471413947191/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-216029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c22 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((146703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934147/5000000) (δ := 1169/100000000) (ψ := 96253/500000) 230 113
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t22 : ((312750502851/2000000000000 : ℚ) : ℝ) ≤ stT230 22 := by
  have hc : ((146693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312750502851/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((146693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c23 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-1217/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3987847/10000000) (δ := 11527/1000000000) (ψ := 96253/500000) 230 115
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t23 : ((-1017133731/200000000000 : ℚ) : ℝ) ≤ stT230 23 := by
  have hc : ((-2439/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1017133731/200000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-2439/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c24 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-166549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119399/250000) (δ := 5817/500000000) (ψ := 96253/500000) 230 116
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t24 : ((-85004461227/1250000000000 : ℚ) : ℝ) ≤ stT230 24 := by
  have hc : ((-83287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85004461227/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-83287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c25 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((59843/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3167317/10000000) (δ := 5777/500000000) (ψ := 96253/500000) 230 118
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t25 : ((59833/1000000 : ℚ) : ℝ) ≤ stT230 25 := by
  have hc : ((59833/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59833/1000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((59833/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c26 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((4999/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1838311/5000000) (δ := 11647/1000000000) (ψ := 96253/500000) 230 119
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t26 : ((19597881873/1000000000000 : ℚ) : ℝ) ≤ stT230 26 := by
  have hc : ((9993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19597881873/1000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((9993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c27 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-747743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -754829/1250000) (δ := 11633/1000000000) (ψ := 96253/500000) 230 121
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t27 : ((-1439128376293/10000000000000 : ℚ) : ℝ) ≤ stT230 27 := by
  have hc : ((-747793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1439128376293/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-747793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c28 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((944717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -835167/10000000) (δ := 11677/1000000000) (ψ := 96253/500000) 230 122
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t28 : ((892626239637/5000000000000 : ℚ) : ℝ) ≤ stT230 28 := by
  have hc : ((944667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((892626239637/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((944667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c29 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((58391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3634367/10000000) (δ := 2317/200000000) (ψ := 96253/500000) 230 123
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t29 : ((54191459399/2500000000000 : ℚ) : ℝ) ≤ stT230 29 := by
  have hc : ((29183/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54191459399/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((29183/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c30 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-492477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3709883/5000000) (δ := 11511/1000000000) (ψ := 96253/500000) 230 124
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t30 : ((-224795396621/1250000000000 : ℚ) : ℝ) ≤ stT230 30 := by
  have hc : ((-246251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224795396621/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-246251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c31 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-93417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321373/625000) (δ := 5753/500000000) (ψ := 96253/500000) 230 126
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t31 : ((-83899968529/1000000000000 : ℚ) : ℝ) ≤ stT230 31 := by
  have hc : ((-93427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83899968529/1000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-93427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c32 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((508141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2594429/10000000) (δ := 1159/100000000) (ψ := 96253/500000) 230 127
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t32 : ((449092997353/5000000000000 : ℚ) : ℝ) ≤ stT230 32 := by
  have hc : ((508091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449092997353/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((508091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c33 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((970503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -304361/5000000) (δ := 9/781250) (ψ := 96253/500000) 230 128
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t33 : ((211167661441/1250000000000 : ℚ) : ℝ) ≤ stT230 33 := by
  have hc : ((970453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211167661441/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((970453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c34 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((235729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84879/1000000) (δ := 2907/250000000) (ψ := 96253/500000) 230 129
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t34 : ((161700104701/1000000000000 : ℚ) : ℝ) ≤ stT230 34 := by
  have hc : ((471433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161700104701/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((471433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c35 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((749523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1808639/10000000) (δ := 2307/200000000) (ψ := 96253/500000) 230 130
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t35 : ((316710051921/2500000000000 : ℚ) : ℝ) ≤ stT230 35 := by
  have hc : ((749473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316710051921/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((749473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c36 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((151539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2298943/10000000) (δ := 11561/1000000000) (ψ := 96253/500000) 230 131
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t36 : ((252544065649/2500000000000 : ℚ) : ℝ) ≤ stT230 36 := by
  have hc : ((303053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252544065649/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((303053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c37 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((591271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 469081/2000000) (δ := 11549/1000000000) (ψ := 96253/500000) 230 132
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t37 : ((971960820569/10000000000000 : ℚ) : ℝ) ≤ stT230 37 := by
  have hc : ((591221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((971960820569/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((591221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c38 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((140959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1971657/10000000) (δ := 1457/125000000) (ψ := 96253/500000) 230 133
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t38 : ((114324720543/1000000000000 : ℚ) : ℝ) ≤ stT230 38 := by
  have hc : ((140949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114324720543/1000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((140949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c39 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((221767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 599803/5000000) (δ := 2891/250000000) (ψ := 96253/500000) 230 134
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t39 : ((710182535029/5000000000000 : ℚ) : ℝ) ≤ stT230 39 := by
  have hc : ((443509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((710182535029/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((443509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c40 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((199961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24689/5000000) (δ := 11671/1000000000) (ψ := 96253/500000) 230 135
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t40 : ((158075062119/1000000000000 : ℚ) : ℝ) ≤ stT230 40 := by
  have hc : ((199951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158075062119/1000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((199951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c41 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((834189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1460341/10000000) (δ := 93/8000000) (ψ := 96253/500000) 230 136
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t41 : ((1302705739443/10000000000000 : ℚ) : ℝ) ≤ stT230 41 := by
  have hc : ((834139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1302705739443/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((834139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c42 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((243451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414023/1250000) (δ := 5759/500000000) (ψ := 96253/500000) 230 137
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t42 : ((375575775233/10000000000000 : ℚ) : ℝ) ≤ stT230 42 := by
  have hc : ((243401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375575775233/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((243401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c43 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-292649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -549011/1000000) (δ := 11611/1000000000) (ψ := 96253/500000) 230 138
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t43 : ((-111580938141/1250000000000 : ℚ) : ℝ) ≤ stT230 43 := by
  have hc : ((-146337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111580938141/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-146337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c44 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-249687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7728853/10000000) (δ := 1449/125000000) (ψ := 96253/500000) 230 138
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t44 : ((-752872458243/5000000000000 : ℚ) : ℝ) ≤ stT230 44 := by
  have hc : ((-499399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-752872458243/5000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-499399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c45 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-395217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19771/40000) (δ := 11699/1000000000) (ψ := 96253/500000) 230 139
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t45 : ((-73653657513/1250000000000 : ℚ) : ℝ) ≤ stT230 45 := by
  have hc : ((-395267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73653657513/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-395267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c46 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((91541/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 936327/5000000) (δ := 11607/1000000000) (ψ := 96253/500000) 230 140
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t46 : ((539842298241/5000000000000 : ℚ) : ℝ) ≤ stT230 46 := by
  have hc : ((366139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539842298241/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((366139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c47 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((104029/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1469187/10000000) (δ := 5757/500000000) (ψ := 96253/500000) 230 141
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t47 : ((606930721059/5000000000000 : ℚ) : ℝ) ≤ stT230 47 := by
  have hc : ((416091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606930721059/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((416091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c48 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-441959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1014289/2000000) (δ := 11621/1000000000) (ψ := 96253/500000) 230 142
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t48 : ((-39874073899/625000000000 : ℚ) : ℝ) ≤ stT230 48 := by
  have hc : ((-442009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39874073899/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-442009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c49 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-909899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1356919/2000000) (δ := 11621/1000000000) (ψ := 96253/500000) 230 142
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t49 : ((-324981915707/2500000000000 : ℚ) : ℝ) ≤ stT230 49 := by
  have hc : ((-909949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324981915707/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-909949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c50 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((473711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2693241/10000000) (δ := 467/40000000) (ψ := 96253/500000) 230 143
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t50 : ((669857543793/10000000000000 : ℚ) : ℝ) ≤ stT230 50 := by
  have hc : ((473661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((669857543793/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((473661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c51 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((397651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1628227/10000000) (δ := 723/62500000) (ψ := 96253/500000) 230 144
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t51 : ((6959846691/62500000000 : ℚ) : ℝ) ≤ stT230 51 := by
  have hc : ((198813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6959846691/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((198813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c52 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-781781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6170783/10000000) (δ := 583/50000000) (ψ := 96253/500000) 230 145
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t52 : ((-1084204921081/10000000000000 : ℚ) : ℝ) ≤ stT230 52 := by
  have hc : ((-781831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1084204921081/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-781831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c53 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-6707/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195483/2500000) (δ := 583/50000000) (ψ := 96253/500000) 230 145
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t53 : ((-1151768631/25000000000 : ℚ) : ℝ) ≤ stT230 53 := by
  have hc : ((-1677/5000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1151768631/25000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-1677/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c54 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((124683/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -178073/10000000) (δ := 233/20000000) (ψ := 96253/500000) 230 146
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t54 : ((678653950689/5000000000000 : ℚ) : ℝ) ≤ stT230 54 := by
  have hc : ((498707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((678653950689/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((498707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c55 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-534001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -666913/1250000) (δ := 11557/1000000000) (ψ := 96253/500000) 230 147
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t55 : ((-1800285921/25000000000 : ℚ) : ℝ) ≤ stT230 55 := by
  have hc : ((-534051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1800285921/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-534051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c56 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-425339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5025333/10000000) (δ := 5823/500000000) (ψ := 96253/500000) 230 147
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t56 : ((-568450298423/10000000000000 : ℚ) : ℝ) ≤ stT230 56 := by
  have hc : ((-425389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568450298423/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-425389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c57 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((489819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6317/125000) (δ := 11539/1000000000) (ψ := 96253/500000) 230 148
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t57 : ((81093478301/625000000000 : ℚ) : ℝ) ≤ stT230 57 := by
  have hc : ((244897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81093478301/625000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((244897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c58 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-49513/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3106519/5000000) (δ := 11571/1000000000) (ψ := 96253/500000) 230 149
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t58 : ((-104028625077/1000000000000 : ℚ) : ℝ) ≤ stT230 58 := by
  have hc : ((-396129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104028625077/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-396129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c59 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((6199/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1808121/5000000) (δ := 11571/1000000000) (ψ := 96253/500000) 230 149
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t59 : ((16134310377/1000000000000 : ℚ) : ℝ) ≤ stT230 59 := by
  have hc : ((12393/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16134310377/1000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((12393/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c60 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((141107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2427639/10000000) (δ := 461/40000000) (ψ := 96253/500000) 230 150
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t60 : ((182152152933/2500000000000 : ℚ) : ℝ) ≤ stT230 60 := by
  have hc : ((282189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182152152933/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((282189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c61 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-119007/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7076709/10000000) (δ := 5839/500000000) (ψ := 96253/500000) 230 150
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t61 : ((-609523503557/5000000000000 : ℚ) : ℝ) ≤ stT230 61 := by
  have hc : ((-476053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-609523503557/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-476053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c62 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((47949/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 718533/10000000) (δ := 5793/500000000) (ψ := 96253/500000) 230 151
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t62 : ((121784205893/1000000000000 : ℚ) : ℝ) ≤ stT230 62 := by
  have hc : ((95893/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121784205893/1000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((95893/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c63 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-338943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14473/25000) (δ := 11693/1000000000) (ψ := 96253/500000) 230 152
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t63 : ((-26691230111/312500000000 : ℚ) : ℝ) ≤ stT230 63 := by
  have hc : ((-42371/62500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26691230111/312500000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-42371/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c64 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((261299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 408259/1250000) (δ := 1151/100000000) (ψ := 96253/500000) 230 152
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t64 : ((261249/8000000 : ℚ) : ℝ) ≤ stT230 64 := by
  have hc : ((261249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261249/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((261249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c65 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((39831/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55109/156250) (δ := 29/2500000) (ψ := 96253/500000) 230 153
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t65 : ((98777514039/5000000000000 : ℚ) : ℝ) ≤ stT230 65 := by
  have hc : ((79637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98777514039/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((79637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c66 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-12637/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1312959/2500000) (δ := 11603/1000000000) (ψ := 96253/500000) 230 153
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t66 : ((-12445289199/200000000000 : ℚ) : ℝ) ≤ stT230 66 := by
  have hc : ((-50553/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12445289199/200000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-50553/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c67 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((374669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361867/2000000) (δ := 731/62500000) (ψ := 96253/500000) 230 154
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t67 : ((57212540867/625000000000 : ℚ) : ℝ) ≤ stT230 67 := by
  have hc : ((93661/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57212540867/625000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((93661/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c68 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-897003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1677337/2500000) (δ := 11507/1000000000) (ψ := 96253/500000) 230 154
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t68 : ((-1087837334987/10000000000000 : ℚ) : ℝ) ≤ stT230 68 := by
  have hc : ((-897053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1087837334987/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-897053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c69 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((970927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120861/2000000) (δ := 5807/500000000) (ψ := 96253/500000) 230 155
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t69 : ((584399021733/5000000000000 : ℚ) : ℝ) ≤ stT230 69 := by
  have hc : ((970877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584399021733/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((970877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c70 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-99727/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7669197/10000000) (δ := 11589/1000000000) (ψ := 96253/500000) 230 155
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t70 : ((-29800644657/250000000000 : ℚ) : ℝ) ≤ stT230 70 := by
  have hc : ((-24933/25000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29800644657/250000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-24933/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c71 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((499449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117379/10000000) (δ := 5761/500000000) (ψ := 96253/500000) 230 156
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t71 : ((18522091067/156250000000 : ℚ) : ℝ) ≤ stT230 71 := by
  have hc : ((15607/15625 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18522091067/156250000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((15607/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c72 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-496271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3774231/5000000) (δ := 5787/500000000) (ψ := 96253/500000) 230 157
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t72 : ((-4569459309/39062500000 : ℚ) : ℝ) ≤ stT230 72 := by
  have hc : ((-62037/62500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4569459309/39062500000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-62037/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c73 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((988307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191343/5000000) (δ := 11629/1000000000) (ψ := 96253/500000) 230 157
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t73 : ((1156666863627/10000000000000 : ℚ) : ℝ) ≤ stT230 73 := by
  have hc : ((988257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1156666863627/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((988257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c74 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-247527/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3751029/5000000) (δ := 11667/1000000000) (ψ := 96253/500000) 230 158
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t74 : ((-575517950683/5000000000000 : ℚ) : ℝ) ≤ stT230 74 := by
  have hc : ((-495079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575517950683/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-495079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c75 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((498131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8649/400000) (δ := 721/62500000) (ψ := 96253/500000) 230 158
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t75 : ((2875814991/25000000000 : ℚ) : ℝ) ≤ stT230 75 := by
  have hc : ((249053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2875814991/25000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((249053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c76 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-499981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1566443/2000000) (δ := 721/62500000) (ψ := 96253/500000) 230 158
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t76 : ((-286773191237/2500000000000 : ℚ) : ℝ) ≤ stT230 76 := by
  have hc : ((-250003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286773191237/2500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-250003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c77 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((989691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -359291/10000000) (δ := 289/25000000) (ψ := 96253/500000) 230 159
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t77 : ((225559966361/2000000000000 : ℚ) : ℝ) ≤ stT230 77 := by
  have hc : ((989641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225559966361/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((989641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c78 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-95001/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1765041/2500000) (δ := 289/25000000) (ψ := 96253/500000) 230 159
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t78 : ((-26893300917/250000000000 : ℚ) : ℝ) ≤ stT230 78 := by
  have hc : ((-47503/50000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26893300917/250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-47503/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c79 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((863237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -661437/5000000) (δ := 231/20000000) (ψ := 96253/500000) 230 160
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t79 : ((971160472269/10000000000000 : ℚ) : ℝ) ≤ stT230 79 := by
  have hc : ((863187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((971160472269/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((863187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c80 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-712587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 369371/625000) (δ := 231/20000000) (ψ := 96253/500000) 230 160
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t80 : ((-398376197829/5000000000000 : ℚ) : ℝ) ≤ stT230 80 := by
  have hc : ((-712637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-398376197829/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-712637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c81 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((97419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265509/1000000) (δ := 5773/500000000) (ψ := 96253/500000) 230 161
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t81 : ((108232211399/2000000000000 : ℚ) : ℝ) ≤ stT230 81 := by
  have hc : ((97409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108232211399/2000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((97409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c82 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-94081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2200109/5000000) (δ := 11657/1000000000) (ψ := 96253/500000) 230 161
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t82 : ((-12990345187/625000000000 : ℚ) : ℝ) ≤ stT230 82 := by
  have hc : ((-47053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12990345187/625000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-47053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c83 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-163641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4337941/10000000) (δ := 5819/500000000) (ψ := 96253/500000) 230 162
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t83 : ((-179674280313/10000000000000 : ℚ) : ℝ) ≤ stT230 83 := by
  have hc : ((-163691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179674280313/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-163691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c84 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((52393/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1274173/5000000) (δ := 4633/200000000) (ψ := 96253/500000) 230 162
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t84 : ((14289992633/250000000000 : ℚ) : ℝ) ≤ stT230 84 := by
  have hc : ((13097/25000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14289992633/250000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((13097/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c85 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-412761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6354809/10000000) (δ := 11531/1000000000) (ψ := 96253/500000) 230 163
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t85 : ((-223864786629/2500000000000 : ℚ) : ℝ) ≤ stT230 85 := by
  have hc : ((-206393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223864786629/2500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-206393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c86 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((197809/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370391/10000000) (δ := 11531/1000000000) (ψ := 96253/500000) 230 163
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t86 : ((213292002273/2000000000000 : ℚ) : ℝ) ≤ stT230 86 := by
  have hc : ((197799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213292002273/2000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((197799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c87 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-472299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7017909/10000000) (δ := 1459/125000000) (ψ := 96253/500000) 230 163
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t87 : ((-126596175153/1250000000000 : ℚ) : ℝ) ≤ stT230 87 := by
  have hc : ((-118081/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126596175153/1250000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-118081/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c88 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((661919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264819/1250000) (δ := 11579/1000000000) (ψ := 96253/500000) 230 164
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t88 : ((705554339607/10000000000000 : ℚ) : ℝ) ≤ stT230 88 := by
  have hc : ((661869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((705554339607/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((661869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c89 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-89843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 218933/500000) (δ := 1453/125000000) (ψ := 96253/500000) 230 164
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t89 : ((-11907487533/625000000000 : ℚ) : ℝ) ≤ stT230 89 := by
  have hc : ((-22467/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11907487533/625000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-22467/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c90 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-190587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -980931/2000000) (δ := 5843/500000000) (ψ := 96253/500000) 230 165
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t90 : ((-50230693729/1250000000000 : ℚ) : ℝ) ≤ stT230 90 := by
  have hc : ((-47653/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50230693729/1250000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-47653/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c91 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((20917/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90563/625000) (δ := 23117/1000000000) (ψ := 96253/500000) 230 165
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t91 : ((21925646073/250000000000 : ℚ) : ℝ) ≤ stT230 91 := by
  have hc : ((83663/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21925646073/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((83663/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c92 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-998833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1933303/2500000) (δ := 11517/1000000000) (ψ := 96253/500000) 230 165
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t92 : ((-1041408445959/10000000000000 : ℚ) : ℝ) ≤ stT230 92 := by
  have hc : ((-998883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1041408445959/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-998883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c93 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((190663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -439621/2500000) (δ := 1161/100000000) (ψ := 96253/500000) 230 166
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t93 : ((395390453251/5000000000000 : ℚ) : ℝ) ≤ stT230 93 := by
  have hc : ((381301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((395390453251/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((381301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c94 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-184663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2195657/5000000) (δ := 11593/1000000000) (ψ := 96253/500000) 230 166
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t94 : ((-95258525943/5000000000000 : ℚ) : ℝ) ≤ stT230 94 := by
  have hc : ((-184713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95258525943/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-184713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c95 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-249299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2615971/5000000) (δ := 11503/1000000000) (ψ := 96253/500000) 230 167
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t95 : ((-63950297049/1250000000000 : ℚ) : ℝ) ≤ stT230 95 := by
  have hc : ((-62331/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63950297049/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-62331/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c96 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((950603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12329/156250) (δ := 117/10000000) (ψ := 96253/500000) 230 167
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t96 : ((48507670143/500000000000 : ℚ) : ℝ) ≤ stT230 96 := by
  have hc : ((950553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48507670143/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((950553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c97 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-903673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3373833/5000000) (δ := 117/10000000) (ψ := 96253/500000) 230 167
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t97 : ((-917592436881/10000000000000 : ℚ) : ℝ) ≤ stT230 97 := by
  have hc : ((-903723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-917592436881/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-903723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c98 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((338829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -306281/1000000) (δ := 1451/125000000) (ψ := 96253/500000) 230 168
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t98 : ((42777285551/1250000000000 : ℚ) : ℝ) ≤ stT230 98 := by
  have hc : ((338779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42777285551/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((338779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c99 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((222363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 138741/500000) (δ := 1451/125000000) (ψ := 96253/500000) 230 168
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t99 : ((111728958253/2500000000000 : ℚ) : ℝ) ≤ stT230 99 := by
  have hc : ((111169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111728958253/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((111169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c100 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-480541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7154221/10000000) (δ := 2303/200000000) (ψ := 96253/500000) 230 169
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t100 : ((-240283/2500000 : ℚ) : ℝ) ≤ stT230 100 := by
  have hc : ((-240283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240283/2500000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-240283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c101 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((420113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1432741/10000000) (δ := 2303/200000000) (ψ := 96253/500000) 230 169
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t101 : ((52250387907/625000000000 : ℚ) : ℝ) ≤ stT230 101 := by
  have hc : ((52511/62500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52250387907/625000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((52511/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c102 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-121833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4232331/10000000) (δ := 1461/125000000) (ψ := 96253/500000) 230 169
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t102 : ((-30170552171/2500000000000 : ℚ) : ℝ) ≤ stT230 102 := by
  have hc : ((-121883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30170552171/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-121883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c103 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-700111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2932937/5000000) (δ := 5811/500000000) (ψ := 96253/500000) 230 170
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t103 : ((-68988963813/1000000000000 : ℚ) : ℝ) ≤ stT230 103 := by
  have hc : ((-700161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68988963813/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-700161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c104 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((248077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155141/5000000) (δ := 11581/1000000000) (ψ := 96253/500000) 230 170
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t104 : ((24324708741/250000000000 : ℚ) : ℝ) ≤ stT230 104 := by
  have hc : ((496129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24324708741/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((496129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c105 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-484749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5192181/10000000) (δ := 5811/500000000) (ψ := 96253/500000) 230 170
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t105 : ((-473115828899/10000000000000 : ℚ) : ℝ) ≤ stT230 105 := by
  have hc : ((-484799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473115828899/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-484799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c106 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-109959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -506553/1000000) (δ := 11529/1000000000) (ψ := 96253/500000) 230 171
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t106 : ((-106813778349/2500000000000 : ℚ) : ℝ) ≤ stT230 106 := by
  have hc : ((-219943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106813778349/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-219943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c107 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((99111/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66721/2000000) (δ := 11529/1000000000) (ψ := 96253/500000) 230 171
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t107 : ((2994041813/31250000000 : ℚ) : ℝ) ≤ stT230 107 := by
  have hc : ((49553/50000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2994041813/31250000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((49553/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c108 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-645897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1136497/2000000) (δ := 11529/1000000000) (ψ := 96253/500000) 230 171
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t108 : ((-621563146697/10000000000000 : ℚ) : ℝ) ≤ stT230 108 := by
  have hc : ((-645947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-621563146697/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-645947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c109 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-62833/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4725933/10000000) (δ := 2909/250000000) (ψ := 96253/500000) 230 172
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t109 : ((-60192722161/2000000000000 : ℚ) : ℝ) ≤ stT230 109 := by
  have hc : ((-62843/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60192722161/2000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-62843/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c110 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((97801/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262627/5000000) (δ := 11567/1000000000) (ψ := 96253/500000) 230 172
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t110 : ((11655596219/125000000000 : ℚ) : ℝ) ≤ stT230 110 := by
  have hc : ((24449/25000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11655596219/125000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((24449/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c111 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-659973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5728947/10000000) (δ := 2909/250000000) (ψ := 96253/500000) 230 172
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t111 : ((-313233055317/5000000000000 : ℚ) : ℝ) ≤ stT230 111 := by
  have hc : ((-660023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313233055317/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-660023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c112 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-10951/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602759/1250000) (δ := 11659/1000000000) (ψ := 96253/500000) 230 173
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t112 : ((-10349207737/312500000000 : ℚ) : ℝ) ≤ stT230 112 := by
  have hc : ((-175241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10349207737/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-175241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c113 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((993321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289103/10000000) (δ := 11659/1000000000) (ψ := 96253/500000) 230 173
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t113 : ((11679873689/125000000000 : ℚ) : ℝ) ≤ stT230 113 := by
  have hc : ((993271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11679873689/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((993271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c114 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-67589/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2677599/5000000) (δ := 11659/1000000000) (ψ := 96253/500000) 230 173
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t114 : ((-126617529633/2500000000000 : ℚ) : ℝ) ≤ stT230 114 := by
  have hc : ((-270381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126617529633/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-270381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c115 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-266253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5330887/10000000) (δ := 11651/1000000000) (ψ := 96253/500000) 230 174
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t115 : ((-24830556639/500000000000 : ℚ) : ℝ) ≤ stT230 115 := by
  have hc : ((-133139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24830556639/500000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-133139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c116 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((495037/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -352537/10000000) (δ := 11651/1000000000) (ψ := 96253/500000) 230 174
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t116 : ((28725422607/312500000000 : ℚ) : ℝ) ≤ stT230 116 := by
  have hc : ((123753/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28725422607/312500000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((123753/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c117 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-12973/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145787/2500000) (δ := 11651/1000000000) (ψ := 96253/500000) 230 174
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t117 : ((-23991725451/1000000000000 : ℚ) : ℝ) ≤ stT230 117 := by
  have hc : ((-25951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23991725451/1000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-25951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c118 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-199153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6231163/10000000) (δ := 5779/500000000) (ψ := 96253/500000) 230 175
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t118 : ((-14667742413/200000000000 : ℚ) : ℝ) ≤ stT230 118 := by
  have hc : ((-398331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14667742413/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-398331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c119 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((425859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1378853/10000000) (δ := 5779/500000000) (ψ := 96253/500000) 230 175
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t119 : ((97590294033/1250000000000 : ℚ) : ℝ) ≤ stT230 119 := by
  have hc : ((212917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97590294033/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((212917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c120 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((39269/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3432919/10000000) (δ := 2329/200000000) (ψ := 96253/500000) 230 175
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t120 : ((3583836333/200000000000 : ℚ) : ℝ) ≤ stT230 120 := by
  have hc : ((39259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3583836333/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((39259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c121 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-495087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3751617/5000000) (δ := 5769/500000000) (ψ := 96253/500000) 230 176
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t121 : ((-56262732899/625000000000 : ℚ) : ℝ) ≤ stT230 121 := by
  have hc : ((-61889/62500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56262732899/625000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-61889/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c122 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((446203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -346337/1250000) (δ := 2333/200000000) (ψ := 96253/500000) 230 176
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t122 : ((403927741621/10000000000000 : ℚ) : ℝ) ≤ stT230 122 := by
  have hc : ((446153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((403927741621/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((446153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c123 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((718411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1923201/10000000) (δ := 5769/500000000) (ψ := 96253/500000) 230 176
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t123 : ((647723844509/10000000000000 : ℚ) : ℝ) ≤ stT230 123 := by
  have hc : ((718361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((647723844509/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((718361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c124 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-436383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6579091/10000000) (δ := 5769/500000000) (ψ := 96253/500000) 230 176
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t124 : ((-48988270877/625000000000 : ℚ) : ℝ) ≤ stT230 124 := by
  have hc : ((-54551/62500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48988270877/625000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-54551/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c125 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-46247/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4510357/10000000) (δ := 2893/250000000) (ψ := 96253/500000) 230 177
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t125 : ((-10343388999/500000000000 : ℚ) : ℝ) ≤ stT230 125 := by
  have hc : ((-46257/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10343388999/500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-46257/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c126 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((999593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35679/5000000) (δ := 2893/250000000) (ψ := 96253/500000) 230 177
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t126 : ((89046287241/1000000000000 : ℚ) : ℝ) ≤ stT230 126 := by
  have hc : ((999543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89046287241/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((999543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c127 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-17027/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461679/1000000) (δ := 11631/1000000000) (ψ := 96253/500000) 230 177
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t127 : ((-120894405037/5000000000000 : ℚ) : ℝ) ≤ stT230 127 := by
  have hc : ((-136241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120894405037/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-136241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c128 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-873203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6581333/10000000) (δ := 2881/250000000) (ψ := 96253/500000) 230 178
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t128 : ((-192963588663/2500000000000 : ℚ) : ℝ) ≤ stT230 128 := by
  have hc : ((-873253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192963588663/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-873253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c129 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((20797/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -263321/1250000) (δ := 2881/250000000) (ψ := 96253/500000) 230 178
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t129 : ((5858989743/100000000000 : ℚ) : ℝ) ≤ stT230 129 := by
  have hc : ((332727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5858989743/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((332727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c130 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((595079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1166791/5000000) (δ := 2881/250000000) (ψ := 96253/500000) 230 178
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t130 : ((260937472341/5000000000000 : ℚ) : ℝ) ≤ stT230 130 := by
  have hc : ((595029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260937472341/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((595029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c131 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-112789/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26959/40000) (δ := 11679/1000000000) (ψ := 96253/500000) 230 178
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t131 : ((-78839819121/1000000000000 : ℚ) : ℝ) ≤ stT230 131 := by
  have hc : ((-451181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78839819121/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-451181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c132 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-52851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4595569/10000000) (δ := 363/31250000) (ψ := 96253/500000) 230 179
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t132 : ((-46009632929/2000000000000 : ℚ) : ℝ) ≤ stT230 132 := by
  have hc : ((-52861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46009632929/2000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-52861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c133 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((198953/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -255929/10000000) (δ := 363/31250000) (ψ := 96253/500000) 230 179
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t133 : ((172505265787/2000000000000 : ℚ) : ℝ) ≤ stT230 133 := by
  have hc : ((198943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172505265787/2000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((198943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c134 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-49661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 810239/2000000) (δ := 2877/125000000) (ψ := 96253/500000) 230 179
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t134 : ((-42943791859/10000000000000 : ℚ) : ℝ) ≤ stT230 134 := by
  have hc : ((-49711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42943791859/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-49711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c135 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-982207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922709/1250000) (δ := 11509/1000000000) (ψ := 96253/500000) 230 180
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t135 : ((-845392256391/10000000000000 : ℚ) : ℝ) ≤ stT230 135 := by
  have hc : ((-982257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-845392256391/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-982257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c136 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((15517/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1569057/5000000) (δ := 5847/500000000) (ψ := 96253/500000) 230 180
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t136 : ((6651779817/250000000000 : ℚ) : ℝ) ≤ stT230 136 := by
  have hc : ((31029/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6651779817/250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((31029/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c137 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((909067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1074393/10000000) (δ := 11509/1000000000) (ψ := 96253/500000) 230 180
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t137 : ((776625037069/10000000000000 : ℚ) : ℝ) ≤ stT230 137 := by
  have hc : ((909017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((776625037069/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((909017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c138 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-63373/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1314049/2500000) (δ := 5847/500000000) (ψ := 96253/500000) 230 180
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t138 : ((-215808120869/5000000000000 : ℚ) : ℝ) ≤ stT230 138 := by
  have hc : ((-253517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215808120869/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-253517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c139 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-406487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1260019/2000000) (δ := 11601/1000000000) (ψ := 96253/500000) 230 181
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t139 : ((-21549937923/312500000000 : ℚ) : ℝ) ≤ stT230 139 := by
  have hc : ((-25407/31250 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21549937923/312500000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-25407/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c140 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((128769/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68069/312500) (δ := 5801/500000000) (ψ := 96253/500000) 230 181
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t140 : ((54410591943/1000000000000 : ℚ) : ℝ) ≤ stT230 140 := by
  have hc : ((128759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54410591943/1000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((128759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c141 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((180221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1914297/10000000) (δ := 5801/500000000) (ψ := 96253/500000) 230 181
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t141 : ((303525536967/5000000000000 : ℚ) : ℝ) ≤ stT230 141 := by
  have hc : ((360417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303525536967/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((360417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c142 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-182851/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5977937/10000000) (δ := 5801/500000000) (ψ := 96253/500000) 230 181
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t142 : ((-153455757657/2500000000000 : ℚ) : ℝ) ≤ stT230 142 := by
  have hc : ((-365727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153455757657/2500000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-365727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c143 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-324841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2847453/5000000) (δ := 2877/250000000) (ψ := 96253/500000) 230 182
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t143 : ((-135833459219/2500000000000 : ℚ) : ℝ) ≤ stT230 143 := by
  have hc : ((-162433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135833459219/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-162433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c144 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((48787/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1687961/10000000) (δ := 2877/250000000) (ψ := 96253/500000) 230 182
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t144 : ((325225703243/5000000000000 : ℚ) : ℝ) ≤ stT230 144 := by
  have hc : ((390271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325225703243/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((390271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c145 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((608577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145663/5000000) (δ := 2339/200000000) (ψ := 96253/500000) 230 182
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t145 : ((252676840629/5000000000000 : ℚ) : ℝ) ≤ stT230 145 := by
  have hc : ((608527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252676840629/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((608527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c146 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-799523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1560811/2500000) (δ := 2877/250000000) (ψ := 96253/500000) 230 182
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t146 : ((-330865706119/5000000000000 : ℚ) : ℝ) ≤ stT230 146 := by
  have hc : ((-799573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330865706119/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-799573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c147 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-300653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5539827/10000000) (δ := 2897/250000000) (ψ := 96253/500000) 230 183
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t147 : ((-123997652793/2500000000000 : ℚ) : ℝ) ≤ stT230 147 := by
  have hc : ((-150339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123997652793/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-150339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c148 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((792073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1641499/10000000) (δ := 2323/200000000) (ψ := 96253/500000) 230 183
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t148 : ((325519076931/5000000000000 : ℚ) : ℝ) ≤ stT230 148 := by
  have hc : ((792023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325519076931/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((792023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c149 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((627667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139413/625000) (δ := 2897/250000000) (ψ := 96253/500000) 230 183
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t149 : ((514163302527/10000000000000 : ℚ) : ℝ) ≤ stT230 149 := by
  have hc : ((627617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((514163302527/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((627617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c150 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-757773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3038363/5000000) (δ := 2323/200000000) (ψ := 96253/500000) 230 183
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t150 : ((-618760206031/10000000000000 : ℚ) : ℝ) ≤ stT230 150 := by
  have hc : ((-757823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618760206031/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-757823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c151 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-85519/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5810593/10000000) (δ := 73/6250000) (ψ := 96253/500000) 230 184
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t151 : ((-278398030689/5000000000000 : ℚ) : ℝ) ≤ stT230 151 := by
  have hc : ((-342101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278398030689/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-342101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c152 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((138467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -201519/1000000) (δ := 11523/1000000000) (ψ := 96253/500000) 230 184
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t152 : ((112303441899/2000000000000 : ℚ) : ℝ) ≤ stT230 152 := by
  have hc : ((138457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112303441899/2000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((138457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c153 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((763471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 351063/2000000) (δ := 11523/1000000000) (ψ := 96253/500000) 230 184
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t153 : ((154297308573/2500000000000 : ℚ) : ℝ) ≤ stT230 153 := by
  have hc : ((763421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154297308573/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((763421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c154 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-588911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5501267/10000000) (δ := 73/6250000) (ψ := 96253/500000) 230 184
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t154 : ((-474598319903/10000000000000 : ℚ) : ℝ) ≤ stT230 154 := by
  have hc : ((-588961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474598319903/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-588961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c155 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-426891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405313/625000) (δ := 1163/100000000) (ψ := 96253/500000) 230 185
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t155 : ((-4286343369/62500000000 : ℚ) : ℝ) ≤ stT230 155 := by
  have hc : ((-106729/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4286343369/62500000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-106729/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c156 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((440271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2787241/10000000) (δ := 11573/1000000000) (ψ := 96253/500000) 230 185
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t156 : ((550716471/15625000000 : ℚ) : ℝ) ≤ stT230 156 := by
  have hc : ((440221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((550716471/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((440221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c157 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((937731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443447/5000000) (δ := 11573/1000000000) (ψ := 96253/500000) 230 185
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t157 : ((374175039283/5000000000000 : ℚ) : ℝ) ≤ stT230 157 := by
  have hc : ((937681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374175039283/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((937681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c158 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-48371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1134421/2500000) (δ := 11573/1000000000) (ψ := 96253/500000) 230 185
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t158 : ((-19244945799/1000000000000 : ℚ) : ℝ) ≤ stT230 158 := by
  have hc : ((-48381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19244945799/1000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-48381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c159 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-124031/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7542489/10000000) (δ := 11537/1000000000) (ψ := 96253/500000) 230 186
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t159 : ((-98367989187/1250000000000 : ℚ) : ℝ) ≤ stT230 159 := by
  have hc : ((-496149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98367989187/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-496149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c160 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-4191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3937469/10000000) (δ := 11537/1000000000) (ψ := 96253/500000) 230 186
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t160 : ((-335280737/1000000000000 : ℚ) : ℝ) ≤ stT230 160 := by
  have hc : ((-4241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335280737/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-4241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c161 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((989939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88733/2500000) (δ := 5833/500000000) (ψ := 96253/500000) 230 186
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t161 : ((78014141979/1000000000000 : ℚ) : ℝ) ≤ stT230 161 := by
  have hc : ((989889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78014141979/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((989889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c162 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((284619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 801367/2500000) (δ := 5833/500000000) (ψ := 96253/500000) 230 186
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t162 : ((111789232253/5000000000000 : ℚ) : ℝ) ≤ stT230 162 := by
  have hc : ((284569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111789232253/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((284569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c163 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-903037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6743961/10000000) (δ := 11537/1000000000) (ψ := 96253/500000) 230 186
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t163 : ((-707352826707/10000000000000 : ℚ) : ℝ) ≤ stT230 163 := by
  have hc : ((-903087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-707352826707/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-903087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c164 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-571291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5447187/10000000) (δ := 2911/250000000) (ψ := 96253/500000) 230 187
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t164 : ((-446142475329/10000000000000 : ℚ) : ℝ) ≤ stT230 164 := by
  have hc : ((-571341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-446142475329/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-571341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c165 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((355209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -975881/5000000) (δ := 2911/250000000) (ψ := 96253/500000) 230 187
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t165 : ((8640938551/156250000000 : ℚ) : ℝ) ≤ stT230 165 := by
  have hc : ((22199/31250 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8640938551/156250000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((22199/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c166 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((820207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2379/15625) (δ := 11559/1000000000) (ψ := 96253/500000) 230 187
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t166 : ((12731297111/200000000000 : ℚ) : ℝ) ≤ stT230 166 := by
  have hc : ((820157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12731297111/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((820157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c167 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-407423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1244017/2500000) (δ := 2911/250000000) (ψ := 96253/500000) 230 187
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t167 : ((-4926756043/156250000000 : ℚ) : ℝ) ≤ stT230 167 := by
  have hc : ((-407473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4926756043/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-407473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c168 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-243867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -456193/625000) (δ := 11551/1000000000) (ψ := 96253/500000) 230 188
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t168 : ((-376314360403/5000000000000 : ℚ) : ℝ) ≤ stT230 168 := by
  have hc : ((-487759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376314360403/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-487759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c169 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((4041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1943289/5000000) (δ := 11551/1000000000) (ψ := 96253/500000) 230 188
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t169 : ((619768611/500000000000 : ℚ) : ℝ) ≤ stT230 169 := by
  have hc : ((8057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((619768611/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((8057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c170 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((980521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -494251/10000000) (δ := 2913/250000000) (ψ := 96253/500000) 230 188
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t170 : ((187996490011/2500000000000 : ℚ) : ℝ) ≤ stT230 170 := by
  have hc : ((980471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187996490011/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((980471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c171 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((16293/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1439091/5000000) (δ := 11551/1000000000) (ψ := 96253/500000) 230 188
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t171 : ((12458037229/400000000000 : ℚ) : ℝ) ≤ stT230 171 := by
  have hc : ((16291/40000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12458037229/400000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((16291/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c172 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-9957/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6230949/10000000) (δ := 2913/250000000) (ψ := 96253/500000) 230 188
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t172 : ((-60740954873/1000000000000 : ℚ) : ℝ) ≤ stT230 172 := by
  have hc : ((-79661/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60740954873/1000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-79661/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c173 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-30999/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6143681/10000000) (δ := 5829/500000000) (ψ := 96253/500000) 230 189
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t173 : ((-11784813143/200000000000 : ℚ) : ℝ) ≤ stT230 173 := by
  have hc : ((-31001/40000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11784813143/200000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-31001/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c174 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((106253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414777/5000000) (δ := 2309/200000000) (ψ := 96253/500000) 230 189
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t174 : ((80540710569/2500000000000 : ℚ) : ℝ) ≤ stT230 174 := by
  have hc : ((212481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80540710569/2500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((212481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c175 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((982707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465599/10000000) (δ := 5829/500000000) (ψ := 96253/500000) 230 189
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t175 : ((92852242587/1250000000000 : ℚ) : ℝ) ≤ stT230 175 := by
  have hc : ((982657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92852242587/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((982657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c176 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((73949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3741949/10000000) (δ := 5829/500000000) (ψ := 96253/500000) 230 189
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t176 : ((27851720211/5000000000000 : ℚ) : ℝ) ≤ stT230 176 := by
  have hc : ((73899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27851720211/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((73899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c177 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-942193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 874973/1250000) (δ := 5829/500000000) (ψ := 96253/500000) 230 189
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t177 : ((-708234124221/10000000000000 : ℚ) : ℝ) ≤ stT230 177 := by
  have hc : ((-942243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-708234124221/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-942243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c178 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-144587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1093749/2000000) (δ := 11637/1000000000) (ψ := 96253/500000) 230 190
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t178 : ((-54190976217/1250000000000 : ℚ) : ℝ) ≤ stT230 178 := by
  have hc : ((-289199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54190976217/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-289199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c179 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((622417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1123711/5000000) (δ := 5783/500000000) (ψ := 96253/500000) 230 190
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t179 : ((93035775729/2000000000000 : ℚ) : ℝ) ≤ stT230 179 := by
  have hc : ((622367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93035775729/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((622367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c180 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((463893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955903/10000000) (δ := 5783/500000000) (ψ := 96253/500000) 230 190
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t180 : ((17287316657/250000000000 : ℚ) : ℝ) ≤ stT230 180 := by
  have hc : ((115967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17287316657/250000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((115967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c181 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-42853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2070759/5000000) (δ := 5783/500000000) (ψ := 96253/500000) 230 190
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t181 : ((-3187100301/500000000000 : ℚ) : ℝ) ≤ stT230 181 := by
  have hc : ((-21439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3187100301/500000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-21439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c182 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-48819/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3654769/5000000) (δ := 5783/500000000) (ψ := 96253/500000) 230 190
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t182 : ((-57902299/800000000 : ℚ) : ℝ) ≤ stT230 182 := by
  have hc : ((-97643/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57902299/800000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-97643/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c183 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-63007/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5247713/10000000) (δ := 1153/100000000) (ψ := 96253/500000) 230 191
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t183 : ((-93161561383/2500000000000 : ℚ) : ℝ) ≤ stT230 183 := by
  have hc : ((-252053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93161561383/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-252053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c184 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((26529/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2114193/10000000) (δ := 1153/100000000) (ψ := 96253/500000) 230 191
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t184 : ((19555943143/400000000000 : ℚ) : ℝ) ≤ stT230 184 := by
  have hc : ((26527/40000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19555943143/400000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((26527/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c185 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((230173/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200473/2000000) (δ := 11673/1000000000) (ψ := 96253/500000) 230 191
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t185 : ((169217221847/2500000000000 : ℚ) : ℝ) ≤ stT230 185 := by
  have hc : ((460321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169217221847/2500000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((460321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c186 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-8747/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164083/400000) (δ := 11673/1000000000) (ψ := 96253/500000) 230 191
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t186 : ((-6418198017/1250000000000 : ℚ) : ℝ) ≤ stT230 186 := by
  have hc : ((-35013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6418198017/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-35013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c187 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-482217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287409/400000) (δ := 11673/1000000000) (ψ := 96253/500000) 230 191
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t187 : ((-176325277033/2500000000000 : ℚ) : ℝ) ≤ stT230 187 := by
  have hc : ((-241121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176325277033/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-241121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c188 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-574211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5456091/10000000) (δ := 579/50000000) (ψ := 96253/500000) 230 192
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t188 : ((-16752916153/400000000000 : ℚ) : ℝ) ≤ stT230 188 := by
  have hc : ((-574261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16752916153/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-574261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c189 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((35729/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2405659/10000000) (δ := 11623/1000000000) (ψ := 96253/500000) 230 192
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t189 : ((6496678917/156250000000 : ℚ) : ℝ) ≤ stT230 189 := by
  have hc : ((285807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6496678917/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((285807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c190 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((484277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78577/1250000) (δ := 11623/1000000000) (ψ := 96253/500000) 230 192
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t190 : ((21957075247/312500000000 : ℚ) : ℝ) ≤ stT230 190 := by
  have hc : ((121063/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21957075247/312500000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((121063/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c191 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((55877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3647021/10000000) (δ := 11623/1000000000) (ψ := 96253/500000) 230 192
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t191 : ((5051631881/625000000000 : ℚ) : ℝ) ≤ stT230 191 := by
  have hc : ((13963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5051631881/625000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((13963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c192 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-886187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3324807/5000000) (δ := 579/50000000) (ψ := 96253/500000) 230 192
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t192 : ((-79948326007/1250000000000 : ℚ) : ℝ) ≤ stT230 192 := by
  have hc : ((-886237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79948326007/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-886237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c193 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-378183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6071339/10000000) (δ := 11687/1000000000) (ψ := 96253/500000) 230 193
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t193 : ((-1063438163/19531250000 : ℚ) : ℝ) ≤ stT230 193 := by
  have hc : ((-11819/15625 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1063438163/19531250000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-11819/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c194 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((64979/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3099739/10000000) (δ := 11687/1000000000) (ψ := 96253/500000) 230 193
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t194 : ((23322506651/1000000000000 : ℚ) : ℝ) ≤ stT230 194 := by
  have hc : ((64969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23322506651/1000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((64969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c195 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((199671/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71717/5000000) (δ := 11687/1000000000) (ψ := 96253/500000) 230 193
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t195 : ((71490018677/1000000000000 : ℚ) : ℝ) ≤ stT230 195 := by
  have hc : ((199661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71490018677/1000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((199661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c196 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((436493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 699437/2500000) (δ := 2879/250000000) (ψ := 96253/500000) 230 193
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t196 : ((62348937651/2000000000000 : ℚ) : ℝ) ≤ stT230 196 := by
  have hc : ((436443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62348937651/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((436443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c197 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-658479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5723981/10000000) (δ := 11687/1000000000) (ψ := 96253/500000) 230 193
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t197 : ((-469182815159/10000000000000 : ℚ) : ℝ) ≤ stT230 197 := by
  have hc : ((-658529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469182815159/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-658529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c198 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-19031/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414517/2000000) (δ := 5797/500000000) (ψ := 96253/500000) 230 194
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t198 : ((-169068393/2500000000 : ℚ) : ℝ) ≤ stT230 198 := by
  have hc : ((-2379/2500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169068393/2500000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-2379/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c199 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-99379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83517/200000) (δ := 5797/500000000) (ψ := 96253/500000) 230 194
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t199 : ((-35241714189/5000000000000 : ℚ) : ℝ) ≤ stT230 199 := by
  have hc : ((-99429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35241714189/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-99429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c200 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((217269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1293663/10000000) (δ := 11609/1000000000) (ψ := 96253/500000) 230 194
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t200 : ((153623374689/2500000000000 : ℚ) : ℝ) ≤ stT230 200 := by
  have hc : ((434513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153623374689/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((434513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c201 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((404107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1574207/10000000) (δ := 11609/1000000000) (ψ := 96253/500000) 230 194
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t201 : ((28501721829/500000000000 : ℚ) : ℝ) ≤ stT230 201 := by
  have hc : ((202041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28501721829/500000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((202041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c202 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-198971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55347/125000) (δ := 5797/500000000) (ψ := 96253/500000) 230 194
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t202 : ((-70015388779/5000000000000 : ℚ) : ℝ) ≤ stT230 202 := by
  have hc : ((-199021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70015388779/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-199021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c203 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-972589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3633641/5000000) (δ := 11609/1000000000) (ψ := 96253/500000) 230 194
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t203 : ((-682659326457/10000000000000 : ℚ) : ℝ) ≤ stT230 203 := by
  have hc : ((-972639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682659326457/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-972639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c204 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-625097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5615131/10000000) (δ := 5751/500000000) (ψ := 96253/500000) 230 195
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t204 : ((-437691045727/10000000000000 : ℚ) : ℝ) ≤ stT230 204 := by
  have hc : ((-625147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437691045727/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-625147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c205 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((86893/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2803381/10000000) (δ := 5751/500000000) (ψ := 96253/500000) 230 195
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t205 : ((6068169369/200000000000 : ℚ) : ℝ) ≤ stT230 205 := by
  have hc : ((86883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6068169369/200000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((86883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c206 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((499999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1329/2500000) (δ := 5751/500000000) (ψ := 96253/500000) 230 195
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t206 : ((174174192471/2500000000000 : ℚ) : ℝ) ≤ stT230 206 := by
  have hc : ((249987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174174192471/2500000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((249987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c207 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((110791/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2779179/10000000) (δ := 5751/500000000) (ψ := 96253/500000) 230 195
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t207 : ((19249093717/625000000000 : ℚ) : ℝ) ≤ stT230 207 := by
  have hc : ((221557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19249093717/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((221557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c208 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-3779/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1387569/2500000) (δ := 11701/1000000000) (ψ := 96253/500000) 230 195
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t208 : ((-327560573/7812500000 : ℚ) : ℝ) ≤ stT230 208 := by
  have hc : ((-60469/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327560573/7812500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-60469/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c209 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-245887/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115623/156250) (δ := 5797/500000000) (ψ := 96253/500000) 230 196
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t209 : ((-68036949057/1000000000000 : ℚ) : ℝ) ≤ stT230 209 := by
  have hc : ((-491799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68036949057/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-491799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c210 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-287191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581903/1250000) (δ := 11609/1000000000) (ψ := 96253/500000) 230 196
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t210 : ((-99107623953/5000000000000 : ℚ) : ℝ) ≤ stT230 210 := by
  have hc : ((-287241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99107623953/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-287241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c211 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((179573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923629/10000000) (δ := 11609/1000000000) (ψ := 96253/500000) 230 196
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t211 : ((61807237947/1250000000000 : ℚ) : ℝ) ≤ stT230 211 := by
  have hc : ((359121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61807237947/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((359121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c212 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((949859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 198757/2500000) (δ := 5797/500000000) (ψ := 96253/500000) 230 196
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t212 : ((326165360409/5000000000000 : ℚ) : ℝ) ≤ stT230 212 := by
  have hc : ((949809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326165360409/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((949809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c213 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((42401/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3500921/10000000) (δ := 11609/1000000000) (ψ := 96253/500000) 230 196
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t213 : ((14522045769/1250000000000 : ℚ) : ℝ) ≤ stT230 213 := by
  have hc : ((84777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14522045769/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((84777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c214 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-393789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6194163/10000000) (δ := 5797/500000000) (ψ := 96253/500000) 230 196
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t214 : ((-67301434251/1250000000000 : ℚ) : ℝ) ≤ stT230 214 := by
  have hc : ((-196907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67301434251/1250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-196907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c215 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-114723/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -136663/200000) (δ := 2879/250000000) (ψ := 96253/500000) 230 197
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t215 : ((-62595819883/1000000000000 : ℚ) : ℝ) ≤ stT230 215 := by
  have hc : ((-458917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62595819883/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-458917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c216 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-23757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104123/250000) (δ := 2879/250000000) (ψ := 96253/500000) 230 197
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t216 : ((-16173100573/2500000000000 : ℚ) : ℝ) ≤ stT230 216 := by
  have hc : ((-47539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16173100573/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-47539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c217 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((411643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509053/10000000) (δ := 11687/1000000000) (ψ := 96253/500000) 230 197
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t217 : ((34928051199/625000000000 : ℚ) : ℝ) ≤ stT230 217 := by
  have hc : ((205809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34928051199/625000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((205809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c218 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((449383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9077/80000) (δ := 2879/250000000) (ψ := 96253/500000) 230 197
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t218 : ((30434343303/500000000000 : ℚ) : ℝ) ≤ stT230 218 := by
  have hc : ((224679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30434343303/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((224679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c219 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((64261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3766227/10000000) (δ := 11687/1000000000) (ψ := 96253/500000) 230 197
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t219 : ((43389748507/10000000000000 : ℚ) : ℝ) ≤ stT230 219 := by
  have hc : ((64211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43389748507/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((64211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c220 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-416229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1596453/2500000) (δ := 11687/1000000000) (ψ := 96253/500000) 230 197
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t220 : ((-701596117/12500000000 : ℚ) : ℝ) ≤ stT230 220 := by
  have hc : ((-208127/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-701596117/12500000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-208127/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c221 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-897897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6714411/10000000) (δ := 579/50000000) (ψ := 96253/500000) 230 198
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t221 : ((-604024702331/10000000000000 : ℚ) : ℝ) ≤ stT230 221 := by
  have hc : ((-897947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604024702331/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-897947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c222 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-15307/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1029629/2500000) (δ := 579/50000000) (ψ := 96253/500000) 230 198
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t222 : ((-10280111769/2000000000000 : ℚ) : ℝ) ≤ stT230 222 := by
  have hc : ((-15317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10280111769/2000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-15317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c223 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((408763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -383559/2500000) (δ := 579/50000000) (ψ := 96253/500000) 230 198
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t223 : ((136855496481/2500000000000 : ℚ) : ℝ) ≤ stT230 223 := by
  have hc : ((204369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136855496481/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((204369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c224 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((914957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1038487/10000000) (δ := 11623/1000000000) (ψ := 96253/500000) 230 198
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t224 : ((611297856771/10000000000000 : ℚ) : ℝ) ≤ stT230 224 := by
  have hc : ((914907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((611297856771/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((914907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c225 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((32629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3599767/10000000) (δ := 11623/1000000000) (ψ := 96253/500000) 230 198
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t225 : ((21744311589/2500000000000 : ℚ) : ℝ) ≤ stT230 225 := by
  have hc : ((65233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21744311589/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((65233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c226 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-388239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6149633/10000000) (δ := 23023/1000000000) (ψ := 96253/500000) 230 198
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t226 : ((-32283714803/625000000000 : ℚ) : ℝ) ≤ stT230 226 := by
  have hc : ((-48533/62500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32283714803/625000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-48533/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c227 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-94483/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7019677/10000000) (δ := 11673/1000000000) (ψ := 96253/500000) 230 199
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t227 : ((-1959811041/31250000000 : ℚ) : ℝ) ≤ stT230 227 := by
  have hc : ((-11811/12500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1959811041/31250000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-11811/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c228 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-44833/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4492207/10000000) (δ := 11673/1000000000) (ψ := 96253/500000) 230 199
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t228 : ((-29698039081/2000000000000 : ℚ) : ℝ) ≤ stT230 228 := by
  have hc : ((-44843/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29698039081/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-44843/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c229 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((5629/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1975777/10000000) (δ := 11673/1000000000) (ψ := 96253/500000) 230 199
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t229 : ((9298700487/200000000000 : ℚ) : ℝ) ≤ stT230 229 := by
  have hc : ((28143/40000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9298700487/200000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((28143/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c230 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((24441/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529671/10000000) (δ := 1153/100000000) (ψ := 96253/500000) 230 199
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t230 : ((3223016471/50000000000 : ℚ) : ℝ) ≤ stT230 230 := by
  have hc : ((97759/100000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3223016471/50000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((97759/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c231 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((3533/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3024251/10000000) (δ := 1153/100000000) (ψ := 96253/500000) 230 199
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t231 : ((929684763/40000000000 : ℚ) : ℝ) ≤ stT230 231 := by
  have hc : ((1413/4000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((929684763/40000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((1413/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c232 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-147773/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5508021/10000000) (δ := 1153/100000000) (ψ := 96253/500000) 230 199
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t232 : ((-194052115343/5000000000000 : ℚ) : ℝ) ≤ stT230 232 := by
  have hc : ((-295571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194052115343/5000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-295571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c233 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-499353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772681/1000000) (δ := 5783/500000000) (ψ := 96253/500000) 230 200
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t233 : ((-81788378529/1250000000000 : ℚ) : ℝ) ≤ stT230 233 := by
  have hc : ((-249689/250000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81788378529/1250000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-249689/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c234 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-509761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5264257/10000000) (δ := 11637/1000000000) (ψ := 96253/500000) 230 200
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t234 : ((-333274156731/10000000000000 : ℚ) : ℝ) ≤ stT230 234 := by
  have hc : ((-509811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333274156731/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-509811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c235 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((17251/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2812227/10000000) (δ := 11637/1000000000) (ψ := 96253/500000) 230 200
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t235 : ((1406500709/50000000000 : ℚ) : ℝ) ≤ stT230 235 := by
  have hc : ((17249/40000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1406500709/50000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((17249/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c236 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((123629/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74121/2000000) (δ := 5783/500000000) (ψ := 96253/500000) 230 200
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t236 : ((5029467961/78125000000 : ℚ) : ℝ) ≤ stT230 236 := by
  have hc : ((494491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5029467961/78125000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((494491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c237 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((135819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 515167/2500000) (δ := 11637/1000000000) (ψ := 96253/500000) 230 200
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t237 : ((88217316321/2000000000000 : ℚ) : ℝ) ≤ stT230 237 := by
  have hc : ((135809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88217316321/2000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((135809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c238 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-220069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 896341/2000000) (δ := 5783/500000000) (ψ := 96253/500000) 230 200
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t238 : ((-35670504069/2500000000000 : ℚ) : ℝ) ≤ stT230 238 := by
  have hc : ((-220119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35670504069/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-220119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c239 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-92697/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6892623/10000000) (δ := 11637/1000000000) (ψ := 96253/500000) 230 200
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t239 : ((-29982005297/500000000000 : ℚ) : ℝ) ≤ stT230 239 := by
  have hc : ((-46351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29982005297/500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-46351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c240 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-419379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3207243/5000000) (δ := 5829/500000000) (ψ := 96253/500000) 230 201
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t240 : ((-33840555399/625000000000 : ℚ) : ℝ) ≤ stT230 240 := by
  have hc : ((-104851/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33840555399/625000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-104851/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c241 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-4831/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1005909/2500000) (δ := 5829/500000000) (ψ := 96253/500000) 230 201
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t241 : ((-12463793793/5000000000000 : ℚ) : ℝ) ≤ stT230 241 := by
  have hc : ((-19349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12463793793/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-19349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c242 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((158357/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -410669/2500000) (δ := 5829/500000000) (ψ := 96253/500000) 230 201
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t242 : ((12723656491/250000000000 : ℚ) : ℝ) ≤ stT230 242 := by
  have hc : ((158347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12723656491/250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((158347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c243 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((119731/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182113/2500000) (δ := 2309/200000000) (ψ := 96253/500000) 230 201
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t243 : ((614427417/10000000000 : ℚ) : ℝ) ≤ stT230 243 := by
  have hc : ((478899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614427417/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((478899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c244 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((328629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1544931/5000000) (δ := 2309/200000000) (ψ := 96253/500000) 230 201
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t244 : ((26293877317/1250000000000 : ℚ) : ℝ) ≤ stT230 244 := by
  have hc : ((328579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26293877317/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((328579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c245 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-11389/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5441583/10000000) (δ := 11529/500000000) (ψ := 96253/500000) 230 201
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t245 : ((-727680903/20000000000 : ℚ) : ℝ) ≤ stT230 245 := by
  have hc : ((-1139/2000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-727680903/20000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-1139/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c246 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-499803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7783759/10000000) (δ := 5829/500000000) (ψ := 96253/500000) 230 201
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t246 : ((-79669709189/1250000000000 : ℚ) : ℝ) ≤ stT230 246 := by
  have hc : ((-124957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79669709189/1250000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-124957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c247 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((-123541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -698943/1250000) (δ := 11551/1000000000) (ψ := 96253/500000) 230 202
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t247 : ((-15722729607/400000000000 : ℚ) : ℝ) ≤ stT230 247 := by
  have hc : ((-123551/200000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15722729607/400000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-123551/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c248 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((260433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1634157/5000000) (δ := 11551/1000000000) (ψ := 96253/500000) 230 202
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t248 : ((33068641/2000000000 : ℚ) : ℝ) ≤ stT230 248 := by
  have hc : ((260383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33068641/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((260383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c249 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((464001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119307/1250000) (δ := 2913/250000000) (ψ := 96253/500000) 230 202
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t249 : ((9188522707/156250000000 : ℚ) : ℝ) ≤ stT230 249 := by
  have hc : ((57997/62500 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9188522707/156250000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((57997/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_c250 :
    |Real.cos (((230 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((857667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1350201/10000000) (δ := 11551/1000000000) (ψ := 96253/500000) 230 202
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st230_t250 : ((108480831947/2000000000000 : ℚ) : ℝ) ≤ stT230 250 := by
  have hc : ((857617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((230 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((96253/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st230_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108480831947/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((857617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st230_p1 : ((490739/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT230 (i+1) := by
  rw [Finset.sum_range_one]
  exact st230_t1

theorem st230_p2 : ((296696519711/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT230 (i+1))
      = (∑ i ∈ Finset.range 1, stT230 (i+1)) + stT230 2 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 1
    simpa using h
  have hprev := st230_p1
  have hstep := st230_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p3 : ((164689377373/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT230 (i+1))
      = (∑ i ∈ Finset.range 2, stT230 (i+1)) + stT230 3 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 2
    simpa using h
  have hprev := st230_p2
  have hstep := st230_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p4 : ((7160353653827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT230 (i+1))
      = (∑ i ∈ Finset.range 3, stT230 (i+1)) + stT230 4 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 3
    simpa using h
  have hprev := st230_p3
  have hstep := st230_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p5 : ((5246755947811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT230 (i+1))
      = (∑ i ∈ Finset.range 4, stT230 (i+1)) + stT230 5 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 4
    simpa using h
  have hprev := st230_p4
  have hstep := st230_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p6 : ((834702900061/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT230 (i+1))
      = (∑ i ∈ Finset.range 5, stT230 (i+1)) + stT230 6 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 5
    simpa using h
  have hprev := st230_p5
  have hstep := st230_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p7 : ((1957723658819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT230 (i+1))
      = (∑ i ∈ Finset.range 6, stT230 (i+1)) + stT230 7 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 6
    simpa using h
  have hprev := st230_p6
  have hstep := st230_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p8 : ((1353987184009/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT230 (i+1))
      = (∑ i ∈ Finset.range 7, stT230 (i+1)) + stT230 8 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 7
    simpa using h
  have hprev := st230_p7
  have hstep := st230_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p9 : ((4066483466143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT230 (i+1))
      = (∑ i ∈ Finset.range 8, stT230 (i+1)) + stT230 9 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 8
    simpa using h
  have hprev := st230_p8
  have hstep := st230_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p10 : ((999335459703/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT230 (i+1))
      = (∑ i ∈ Finset.range 9, stT230 (i+1)) + stT230 10 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 9
    simpa using h
  have hprev := st230_p9
  have hstep := st230_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p11 : ((6184234653/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT230 (i+1))
      = (∑ i ∈ Finset.range 10, stT230 (i+1)) + stT230 11 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 10
    simpa using h
  have hprev := st230_p10
  have hstep := st230_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p12 : ((2633748158037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT230 (i+1))
      = (∑ i ∈ Finset.range 11, stT230 (i+1)) + stT230 12 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 11
    simpa using h
  have hprev := st230_p11
  have hstep := st230_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p13 : ((3078922643037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT230 (i+1))
      = (∑ i ∈ Finset.range 12, stT230 (i+1)) + stT230 13 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 12
    simpa using h
  have hprev := st230_p12
  have hstep := st230_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p14 : ((2481171364683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT230 (i+1))
      = (∑ i ∈ Finset.range 13, stT230 (i+1)) + stT230 14 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 13
    simpa using h
  have hprev := st230_p13
  have hstep := st230_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p15 : ((3005101914673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT230 (i+1))
      = (∑ i ∈ Finset.range 14, stT230 (i+1)) + stT230 15 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 14
    simpa using h
  have hprev := st230_p14
  have hstep := st230_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p16 : ((47960883437/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT230 (i+1))
      = (∑ i ∈ Finset.range 15, stT230 (i+1)) + stT230 16 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 15
    simpa using h
  have hprev := st230_p15
  have hstep := st230_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p17 : ((8572379553539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT230 (i+1))
      = (∑ i ∈ Finset.range 16, stT230 (i+1)) + stT230 17 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 16
    simpa using h
  have hprev := st230_p16
  have hstep := st230_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p18 : ((8915517173321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT230 (i+1))
      = (∑ i ∈ Finset.range 17, stT230 (i+1)) + stT230 18 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 17
    simpa using h
  have hprev := st230_p17
  have hstep := st230_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p19 : ((4475176973683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT230 (i+1))
      = (∑ i ∈ Finset.range 18, stT230 (i+1)) + stT230 19 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 18
    simpa using h
  have hprev := st230_p18
  have hstep := st230_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p20 : ((3710023572967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT230 (i+1))
      = (∑ i ∈ Finset.range 19, stT230 (i+1)) + stT230 20 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 19
    simpa using h
  have hprev := st230_p19
  have hstep := st230_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p21 : ((553439135717/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT230 (i+1))
      = (∑ i ∈ Finset.range 20, stT230 (i+1)) + stT230 21 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 20
    simpa using h
  have hprev := st230_p20
  have hstep := st230_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p22 : ((283925754857/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT230 (i+1))
      = (∑ i ∈ Finset.range 21, stT230 (i+1)) + stT230 22 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 21
    simpa using h
  have hprev := st230_p21
  have hstep := st230_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p23 : ((56378297479/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT230 (i+1))
      = (∑ i ∈ Finset.range 22, stT230 (i+1)) + stT230 23 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 22
    simpa using h
  have hprev := st230_p22
  have hstep := st230_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p24 : ((6367251495059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT230 (i+1))
      = (∑ i ∈ Finset.range 23, stT230 (i+1)) + stT230 24 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 23
    simpa using h
  have hprev := st230_p23
  have hstep := st230_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p25 : ((6965581495059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT230 (i+1))
      = (∑ i ∈ Finset.range 24, stT230 (i+1)) + stT230 25 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 24
    simpa using h
  have hprev := st230_p24
  have hstep := st230_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p26 : ((7161560313789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT230 (i+1))
      = (∑ i ∈ Finset.range 25, stT230 (i+1)) + stT230 26 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 25
    simpa using h
  have hprev := st230_p25
  have hstep := st230_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p27 : ((715303992187/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT230 (i+1))
      = (∑ i ∈ Finset.range 26, stT230 (i+1)) + stT230 27 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 26
    simpa using h
  have hprev := st230_p26
  have hstep := st230_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p28 : ((750768441677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT230 (i+1))
      = (∑ i ∈ Finset.range 27, stT230 (i+1)) + stT230 28 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 27
    simpa using h
  have hprev := st230_p27
  have hstep := st230_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p29 : ((3862225127183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT230 (i+1))
      = (∑ i ∈ Finset.range 28, stT230 (i+1)) + stT230 29 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 28
    simpa using h
  have hprev := st230_p28
  have hstep := st230_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p30 : ((2963043540699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT230 (i+1))
      = (∑ i ∈ Finset.range 29, stT230 (i+1)) + stT230 30 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 29
    simpa using h
  have hprev := st230_p29
  have hstep := st230_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p31 : ((1271771849027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT230 (i+1))
      = (∑ i ∈ Finset.range 30, stT230 (i+1)) + stT230 31 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 30
    simpa using h
  have hprev := st230_p30
  have hstep := st230_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p32 : ((2992636695407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT230 (i+1))
      = (∑ i ∈ Finset.range 31, stT230 (i+1)) + stT230 32 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 31
    simpa using h
  have hprev := st230_p31
  have hstep := st230_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p33 : ((3837307341171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT230 (i+1))
      = (∑ i ∈ Finset.range 32, stT230 (i+1)) + stT230 33 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 32
    simpa using h
  have hprev := st230_p32
  have hstep := st230_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p34 : ((1161451966169/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT230 (i+1))
      = (∑ i ∈ Finset.range 33, stT230 (i+1)) + stT230 34 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 33
    simpa using h
  have hprev := st230_p33
  have hstep := st230_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p35 : ((2639613984259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT230 (i+1))
      = (∑ i ∈ Finset.range 34, stT230 (i+1)) + stT230 35 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 34
    simpa using h
  have hprev := st230_p34
  have hstep := st230_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p36 : ((723039512477/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT230 (i+1))
      = (∑ i ∈ Finset.range 35, stT230 (i+1)) + stT230 36 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 35
    simpa using h
  have hprev := st230_p35
  have hstep := st230_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p37 : ((12540593020201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT230 (i+1))
      = (∑ i ∈ Finset.range 36, stT230 (i+1)) + stT230 37 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 36
    simpa using h
  have hprev := st230_p36
  have hstep := st230_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p38 : ((13683840225631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT230 (i+1))
      = (∑ i ∈ Finset.range 37, stT230 (i+1)) + stT230 38 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 37
    simpa using h
  have hprev := st230_p37
  have hstep := st230_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p39 : ((15104205295689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT230 (i+1))
      = (∑ i ∈ Finset.range 38, stT230 (i+1)) + stT230 39 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 38
    simpa using h
  have hprev := st230_p38
  have hstep := st230_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p40 : ((16684955916879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT230 (i+1))
      = (∑ i ∈ Finset.range 39, stT230 (i+1)) + stT230 40 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 39
    simpa using h
  have hprev := st230_p39
  have hstep := st230_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p41 : ((8993830828161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT230 (i+1))
      = (∑ i ∈ Finset.range 40, stT230 (i+1)) + stT230 41 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 40
    simpa using h
  have hprev := st230_p40
  have hstep := st230_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p42 : ((3672647486311/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT230 (i+1))
      = (∑ i ∈ Finset.range 41, stT230 (i+1)) + stT230 42 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 41
    simpa using h
  have hprev := st230_p41
  have hstep := st230_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p43 : ((17470589926427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT230 (i+1))
      = (∑ i ∈ Finset.range 42, stT230 (i+1)) + stT230 43 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 42
    simpa using h
  have hprev := st230_p42
  have hstep := st230_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p44 : ((15964845009941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT230 (i+1))
      = (∑ i ∈ Finset.range 43, stT230 (i+1)) + stT230 44 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 43
    simpa using h
  have hprev := st230_p43
  have hstep := st230_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p45 : ((15375615749837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT230 (i+1))
      = (∑ i ∈ Finset.range 44, stT230 (i+1)) + stT230 45 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 44
    simpa using h
  have hprev := st230_p44
  have hstep := st230_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p46 : ((16455300346319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT230 (i+1))
      = (∑ i ∈ Finset.range 45, stT230 (i+1)) + stT230 46 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 45
    simpa using h
  have hprev := st230_p45
  have hstep := st230_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p47 : ((17669161788437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT230 (i+1))
      = (∑ i ∈ Finset.range 46, stT230 (i+1)) + stT230 47 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 46
    simpa using h
  have hprev := st230_p46
  have hstep := st230_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p48 : ((17031176606053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT230 (i+1))
      = (∑ i ∈ Finset.range 47, stT230 (i+1)) + stT230 48 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 47
    simpa using h
  have hprev := st230_p47
  have hstep := st230_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p49 : ((629249957729/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT230 (i+1))
      = (∑ i ∈ Finset.range 48, stT230 (i+1)) + stT230 49 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 48
    simpa using h
  have hprev := st230_p48
  have hstep := st230_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p50 : ((8200553243509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT230 (i+1))
      = (∑ i ∈ Finset.range 49, stT230 (i+1)) + stT230 50 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 49
    simpa using h
  have hprev := st230_p49
  have hstep := st230_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p51 : ((8757340978789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT230 (i+1))
      = (∑ i ∈ Finset.range 50, stT230 (i+1)) + stT230 51 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 50
    simpa using h
  have hprev := st230_p50
  have hstep := st230_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p52 : ((16430477036497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT230 (i+1))
      = (∑ i ∈ Finset.range 51, stT230 (i+1)) + stT230 52 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 51
    simpa using h
  have hprev := st230_p51
  have hstep := st230_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p53 : ((15969769584097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT230 (i+1))
      = (∑ i ∈ Finset.range 52, stT230 (i+1)) + stT230 53 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 52
    simpa using h
  have hprev := st230_p52
  have hstep := st230_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p54 : ((693083099419/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT230 (i+1))
      = (∑ i ∈ Finset.range 53, stT230 (i+1)) + stT230 54 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 53
    simpa using h
  have hprev := st230_p53
  have hstep := st230_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p55 : ((664278524683/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT230 (i+1))
      = (∑ i ∈ Finset.range 54, stT230 (i+1)) + stT230 55 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 54
    simpa using h
  have hprev := st230_p54
  have hstep := st230_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p56 : ((4009628204663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT230 (i+1))
      = (∑ i ∈ Finset.range 55, stT230 (i+1)) + stT230 56 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 55
    simpa using h
  have hprev := st230_p55
  have hstep := st230_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p57 : ((4334002117867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT230 (i+1))
      = (∑ i ∈ Finset.range 56, stT230 (i+1)) + stT230 57 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 56
    simpa using h
  have hprev := st230_p56
  have hstep := st230_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p58 : ((8147861110349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT230 (i+1))
      = (∑ i ∈ Finset.range 57, stT230 (i+1)) + stT230 58 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 57
    simpa using h
  have hprev := st230_p57
  have hstep := st230_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p59 : ((4114266331117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT230 (i+1))
      = (∑ i ∈ Finset.range 58, stT230 (i+1)) + stT230 59 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 58
    simpa using h
  have hprev := st230_p58
  have hstep := st230_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p60 : ((85928369681/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT230 (i+1))
      = (∑ i ∈ Finset.range 59, stT230 (i+1)) + stT230 60 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 59
    simpa using h
  have hprev := st230_p59
  have hstep := st230_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p61 : ((7983313464543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT230 (i+1))
      = (∑ i ∈ Finset.range 60, stT230 (i+1)) + stT230 61 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 60
    simpa using h
  have hprev := st230_p60
  have hstep := st230_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p62 : ((1074029311751/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT230 (i+1))
      = (∑ i ∈ Finset.range 61, stT230 (i+1)) + stT230 62 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 61
    simpa using h
  have hprev := st230_p61
  have hstep := st230_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p63 : ((1020646851529/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT230 (i+1))
      = (∑ i ∈ Finset.range 62, stT230 (i+1)) + stT230 63 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 62
    simpa using h
  have hprev := st230_p62
  have hstep := st230_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p64 : ((520528464827/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT230 (i+1))
      = (∑ i ∈ Finset.range 63, stT230 (i+1)) + stT230 64 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 63
    simpa using h
  have hprev := st230_p63
  have hstep := st230_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p65 : ((8427232951271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT230 (i+1))
      = (∑ i ∈ Finset.range 64, stT230 (i+1)) + stT230 65 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 64
    simpa using h
  have hprev := st230_p64
  have hstep := st230_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p66 : ((507256295081/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT230 (i+1))
      = (∑ i ∈ Finset.range 65, stT230 (i+1)) + stT230 66 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 65
    simpa using h
  have hprev := st230_p65
  have hstep := st230_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p67 : ((1071725131029/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT230 (i+1))
      = (∑ i ∈ Finset.range 66, stT230 (i+1)) + stT230 67 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 66
    simpa using h
  have hprev := st230_p66
  have hstep := st230_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p68 : ((16059764761477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT230 (i+1))
      = (∑ i ∈ Finset.range 67, stT230 (i+1)) + stT230 68 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 67
    simpa using h
  have hprev := st230_p67
  have hstep := st230_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p69 : ((17228562804943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT230 (i+1))
      = (∑ i ∈ Finset.range 68, stT230 (i+1)) + stT230 69 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 68
    simpa using h
  have hprev := st230_p68
  have hstep := st230_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p70 : ((16036537018663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT230 (i+1))
      = (∑ i ∈ Finset.range 69, stT230 (i+1)) + stT230 70 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 69
    simpa using h
  have hprev := st230_p69
  have hstep := st230_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p71 : ((17221950846951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT230 (i+1))
      = (∑ i ∈ Finset.range 70, stT230 (i+1)) + stT230 71 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 70
    simpa using h
  have hprev := st230_p70
  have hstep := st230_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p72 : ((16052169263847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT230 (i+1))
      = (∑ i ∈ Finset.range 71, stT230 (i+1)) + stT230 72 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 71
    simpa using h
  have hprev := st230_p71
  have hstep := st230_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p73 : ((8604418063737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT230 (i+1))
      = (∑ i ∈ Finset.range 72, stT230 (i+1)) + stT230 73 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 72
    simpa using h
  have hprev := st230_p72
  have hstep := st230_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p74 : ((4014450056527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT230 (i+1))
      = (∑ i ∈ Finset.range 73, stT230 (i+1)) + stT230 74 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 73
    simpa using h
  have hprev := st230_p73
  have hstep := st230_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p75 : ((4302031555627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT230 (i+1))
      = (∑ i ∈ Finset.range 74, stT230 (i+1)) + stT230 75 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 74
    simpa using h
  have hprev := st230_p74
  have hstep := st230_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p76 : ((401525836439/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT230 (i+1))
      = (∑ i ∈ Finset.range 75, stT230 (i+1)) + stT230 76 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 75
    simpa using h
  have hprev := st230_p75
  have hstep := st230_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p77 : ((3437766657873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT230 (i+1))
      = (∑ i ∈ Finset.range 76, stT230 (i+1)) + stT230 77 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 76
    simpa using h
  have hprev := st230_p76
  have hstep := st230_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p78 : ((3222620250537/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT230 (i+1))
      = (∑ i ∈ Finset.range 77, stT230 (i+1)) + stT230 78 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 77
    simpa using h
  have hprev := st230_p77
  have hstep := st230_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p79 : ((8542130862477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT230 (i+1))
      = (∑ i ∈ Finset.range 78, stT230 (i+1)) + stT230 79 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 78
    simpa using h
  have hprev := st230_p78
  have hstep := st230_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p80 : ((1017969333081/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT230 (i+1))
      = (∑ i ∈ Finset.range 79, stT230 (i+1)) + stT230 80 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 79
    simpa using h
  have hprev := st230_p79
  have hstep := st230_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p81 : ((16828670386291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT230 (i+1))
      = (∑ i ∈ Finset.range 80, stT230 (i+1)) + stT230 81 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 80
    simpa using h
  have hprev := st230_p80
  have hstep := st230_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p82 : ((16620824863299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT230 (i+1))
      = (∑ i ∈ Finset.range 81, stT230 (i+1)) + stT230 82 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 81
    simpa using h
  have hprev := st230_p81
  have hstep := st230_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p83 : ((8220575291493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT230 (i+1))
      = (∑ i ∈ Finset.range 82, stT230 (i+1)) + stT230 83 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 82
    simpa using h
  have hprev := st230_p82
  have hstep := st230_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p84 : ((8506375144153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT230 (i+1))
      = (∑ i ∈ Finset.range 83, stT230 (i+1)) + stT230 84 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 83
    simpa using h
  have hprev := st230_p83
  have hstep := st230_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p85 : ((1611729114179/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT230 (i+1))
      = (∑ i ∈ Finset.range 84, stT230 (i+1)) + stT230 85 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 84
    simpa using h
  have hprev := st230_p84
  have hstep := st230_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p86 : ((3436750230631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT230 (i+1))
      = (∑ i ∈ Finset.range 85, stT230 (i+1)) + stT230 86 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 85
    simpa using h
  have hprev := st230_p85
  have hstep := st230_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p87 : ((16170981751931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT230 (i+1))
      = (∑ i ∈ Finset.range 86, stT230 (i+1)) + stT230 87 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 86
    simpa using h
  have hprev := st230_p86
  have hstep := st230_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p88 : ((8438268045769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT230 (i+1))
      = (∑ i ∈ Finset.range 87, stT230 (i+1)) + stT230 88 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 87
    simpa using h
  have hprev := st230_p87
  have hstep := st230_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p89 : ((1668601629101/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT230 (i+1))
      = (∑ i ∈ Finset.range 88, stT230 (i+1)) + stT230 89 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 88
    simpa using h
  have hprev := st230_p88
  have hstep := st230_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p90 : ((8142085370589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT230 (i+1))
      = (∑ i ∈ Finset.range 89, stT230 (i+1)) + stT230 90 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 89
    simpa using h
  have hprev := st230_p89
  have hstep := st230_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p91 : ((8580598292049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT230 (i+1))
      = (∑ i ∈ Finset.range 90, stT230 (i+1)) + stT230 91 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 90
    simpa using h
  have hprev := st230_p90
  have hstep := st230_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p92 : ((16119788138139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT230 (i+1))
      = (∑ i ∈ Finset.range 91, stT230 (i+1)) + stT230 92 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 91
    simpa using h
  have hprev := st230_p91
  have hstep := st230_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p93 : ((16910569044641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT230 (i+1))
      = (∑ i ∈ Finset.range 92, stT230 (i+1)) + stT230 93 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 92
    simpa using h
  have hprev := st230_p92
  have hstep := st230_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p94 : ((3344010398551/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT230 (i+1))
      = (∑ i ∈ Finset.range 93, stT230 (i+1)) + stT230 94 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 93
    simpa using h
  have hprev := st230_p93
  have hstep := st230_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p95 : ((16208449616363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT230 (i+1))
      = (∑ i ∈ Finset.range 94, stT230 (i+1)) + stT230 95 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 94
    simpa using h
  have hprev := st230_p94
  have hstep := st230_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p96 : ((17178603019223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT230 (i+1))
      = (∑ i ∈ Finset.range 95, stT230 (i+1)) + stT230 96 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 95
    simpa using h
  have hprev := st230_p95
  have hstep := st230_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p97 : ((8130505291171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT230 (i+1))
      = (∑ i ∈ Finset.range 96, stT230 (i+1)) + stT230 97 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 96
    simpa using h
  have hprev := st230_p96
  have hstep := st230_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p98 : ((66412915467/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT230 (i+1))
      = (∑ i ∈ Finset.range 97, stT230 (i+1)) + stT230 98 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 97
    simpa using h
  have hprev := st230_p97
  have hstep := st230_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p99 : ((8525072349881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT230 (i+1))
      = (∑ i ∈ Finset.range 98, stT230 (i+1)) + stT230 99 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 98
    simpa using h
  have hprev := st230_p98
  have hstep := st230_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p100 : ((8044506349881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT230 (i+1))
      = (∑ i ∈ Finset.range 99, stT230 (i+1)) + stT230 100 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 99
    simpa using h
  have hprev := st230_p99
  have hstep := st230_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p101 : ((8462509453137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT230 (i+1))
      = (∑ i ∈ Finset.range 100, stT230 (i+1)) + stT230 101 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 100
    simpa using h
  have hprev := st230_p100
  have hstep := st230_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p102 : ((1680433669759/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT230 (i+1))
      = (∑ i ∈ Finset.range 101, stT230 (i+1)) + stT230 102 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 101
    simpa using h
  have hprev := st230_p101
  have hstep := st230_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p103 : ((805722352973/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT230 (i+1))
      = (∑ i ∈ Finset.range 102, stT230 (i+1)) + stT230 103 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 102
    simpa using h
  have hprev := st230_p102
  have hstep := st230_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p104 : ((170874354091/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT230 (i+1))
      = (∑ i ∈ Finset.range 103, stT230 (i+1)) + stT230 104 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 103
    simpa using h
  have hprev := st230_p103
  have hstep := st230_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p105 : ((16614319580201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT230 (i+1))
      = (∑ i ∈ Finset.range 104, stT230 (i+1)) + stT230 105 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 104
    simpa using h
  have hprev := st230_p104
  have hstep := st230_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p106 : ((3237412893361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT230 (i+1))
      = (∑ i ∈ Finset.range 105, stT230 (i+1)) + stT230 106 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 105
    simpa using h
  have hprev := st230_p105
  have hstep := st230_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p107 : ((3429031569393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT230 (i+1))
      = (∑ i ∈ Finset.range 106, stT230 (i+1)) + stT230 107 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 106
    simpa using h
  have hprev := st230_p106
  have hstep := st230_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p108 : ((4130898675067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT230 (i+1))
      = (∑ i ∈ Finset.range 107, stT230 (i+1)) + stT230 108 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 107
    simpa using h
  have hprev := st230_p107
  have hstep := st230_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p109 : ((16222631089463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT230 (i+1))
      = (∑ i ∈ Finset.range 108, stT230 (i+1)) + stT230 109 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 108
    simpa using h
  have hprev := st230_p108
  have hstep := st230_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p110 : ((17155078786983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT230 (i+1))
      = (∑ i ∈ Finset.range 109, stT230 (i+1)) + stT230 110 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 109
    simpa using h
  have hprev := st230_p109
  have hstep := st230_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p111 : ((16528612676349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT230 (i+1))
      = (∑ i ∈ Finset.range 110, stT230 (i+1)) + stT230 111 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 110
    simpa using h
  have hprev := st230_p110
  have hstep := st230_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p112 : ((3239487605753/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT230 (i+1))
      = (∑ i ∈ Finset.range 111, stT230 (i+1)) + stT230 112 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 111
    simpa using h
  have hprev := st230_p111
  have hstep := st230_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p113 : ((3426365584777/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT230 (i+1))
      = (∑ i ∈ Finset.range 112, stT230 (i+1)) + stT230 113 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 112
    simpa using h
  have hprev := st230_p112
  have hstep := st230_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p114 : ((16625357805353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT230 (i+1))
      = (∑ i ∈ Finset.range 113, stT230 (i+1)) + stT230 114 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 113
    simpa using h
  have hprev := st230_p113
  have hstep := st230_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p115 : ((16128746672573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT230 (i+1))
      = (∑ i ∈ Finset.range 114, stT230 (i+1)) + stT230 115 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 114
    simpa using h
  have hprev := st230_p114
  have hstep := st230_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p116 : ((17047960195997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT230 (i+1))
      = (∑ i ∈ Finset.range 115, stT230 (i+1)) + stT230 116 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 115
    simpa using h
  have hprev := st230_p115
  have hstep := st230_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p117 : ((16808042941487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT230 (i+1))
      = (∑ i ∈ Finset.range 116, stT230 (i+1)) + stT230 117 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 116
    simpa using h
  have hprev := st230_p116
  have hstep := st230_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p118 : ((16074655820837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT230 (i+1))
      = (∑ i ∈ Finset.range 117, stT230 (i+1)) + stT230 118 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 117
    simpa using h
  have hprev := st230_p117
  have hstep := st230_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p119 : ((16855378173101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT230 (i+1))
      = (∑ i ∈ Finset.range 118, stT230 (i+1)) + stT230 119 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 118
    simpa using h
  have hprev := st230_p118
  have hstep := st230_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p120 : ((17034569989751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT230 (i+1))
      = (∑ i ∈ Finset.range 119, stT230 (i+1)) + stT230 120 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 119
    simpa using h
  have hprev := st230_p119
  have hstep := st230_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p121 : ((16134366263367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT230 (i+1))
      = (∑ i ∈ Finset.range 120, stT230 (i+1)) + stT230 121 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 120
    simpa using h
  have hprev := st230_p120
  have hstep := st230_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p122 : ((4134573501247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT230 (i+1))
      = (∑ i ∈ Finset.range 121, stT230 (i+1)) + stT230 122 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 121
    simpa using h
  have hprev := st230_p121
  have hstep := st230_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p123 : ((17186017849497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT230 (i+1))
      = (∑ i ∈ Finset.range 122, stT230 (i+1)) + stT230 123 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 122
    simpa using h
  have hprev := st230_p122
  have hstep := st230_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p124 : ((3280441103093/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT230 (i+1))
      = (∑ i ∈ Finset.range 123, stT230 (i+1)) + stT230 124 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 123
    simpa using h
  have hprev := st230_p123
  have hstep := st230_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p125 : ((3239067547097/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT230 (i+1))
      = (∑ i ∈ Finset.range 124, stT230 (i+1)) + stT230 125 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 124
    simpa using h
  have hprev := st230_p124
  have hstep := st230_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p126 : ((3417160121579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT230 (i+1))
      = (∑ i ∈ Finset.range 125, stT230 (i+1)) + stT230 126 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 125
    simpa using h
  have hprev := st230_p125
  have hstep := st230_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p127 : ((16844011797821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT230 (i+1))
      = (∑ i ∈ Finset.range 126, stT230 (i+1)) + stT230 127 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 126
    simpa using h
  have hprev := st230_p126
  have hstep := st230_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p128 : ((16072157443169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT230 (i+1))
      = (∑ i ∈ Finset.range 127, stT230 (i+1)) + stT230 128 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 127
    simpa using h
  have hprev := st230_p127
  have hstep := st230_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p129 : ((16658056417469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT230 (i+1))
      = (∑ i ∈ Finset.range 128, stT230 (i+1)) + stT230 129 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 128
    simpa using h
  have hprev := st230_p128
  have hstep := st230_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p130 : ((17179931362151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT230 (i+1))
      = (∑ i ∈ Finset.range 129, stT230 (i+1)) + stT230 130 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 129
    simpa using h
  have hprev := st230_p129
  have hstep := st230_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p131 : ((16391533170941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT230 (i+1))
      = (∑ i ∈ Finset.range 130, stT230 (i+1)) + stT230 131 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 130
    simpa using h
  have hprev := st230_p130
  have hstep := st230_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p132 : ((2020185625787/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT230 (i+1))
      = (∑ i ∈ Finset.range 131, stT230 (i+1)) + stT230 132 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 131
    simpa using h
  have hprev := st230_p131
  have hstep := st230_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p133 : ((17024011335231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT230 (i+1))
      = (∑ i ∈ Finset.range 132, stT230 (i+1)) + stT230 133 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 132
    simpa using h
  have hprev := st230_p132
  have hstep := st230_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p134 : ((4245266885843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT230 (i+1))
      = (∑ i ∈ Finset.range 133, stT230 (i+1)) + stT230 134 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 133
    simpa using h
  have hprev := st230_p133
  have hstep := st230_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p135 : ((16135675286981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT230 (i+1))
      = (∑ i ∈ Finset.range 134, stT230 (i+1)) + stT230 135 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 134
    simpa using h
  have hprev := st230_p134
  have hstep := st230_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p136 : ((16401746479661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT230 (i+1))
      = (∑ i ∈ Finset.range 135, stT230 (i+1)) + stT230 136 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 135
    simpa using h
  have hprev := st230_p135
  have hstep := st230_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p137 : ((1717837151673/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT230 (i+1))
      = (∑ i ∈ Finset.range 136, stT230 (i+1)) + stT230 137 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 136
    simpa using h
  have hprev := st230_p136
  have hstep := st230_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p138 : ((1046672204687/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT230 (i+1))
      = (∑ i ∈ Finset.range 137, stT230 (i+1)) + stT230 138 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 137
    simpa using h
  have hprev := st230_p137
  have hstep := st230_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p139 : ((1003572328841/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT230 (i+1))
      = (∑ i ∈ Finset.range 138, stT230 (i+1)) + stT230 139 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 138
    simpa using h
  have hprev := st230_p138
  have hstep := st230_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p140 : ((8300631590443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT230 (i+1))
      = (∑ i ∈ Finset.range 139, stT230 (i+1)) + stT230 140 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 139
    simpa using h
  have hprev := st230_p139
  have hstep := st230_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p141 : ((860415712741/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT230 (i+1))
      = (∑ i ∈ Finset.range 140, stT230 (i+1)) + stT230 141 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 140
    simpa using h
  have hprev := st230_p140
  have hstep := st230_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p142 : ((129644462689/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT230 (i+1))
      = (∑ i ∈ Finset.range 141, stT230 (i+1)) + stT230 142 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 141
    simpa using h
  have hprev := st230_p141
  have hstep := st230_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p143 : ((4012789346829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT230 (i+1))
      = (∑ i ∈ Finset.range 142, stT230 (i+1)) + stT230 143 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 142
    simpa using h
  have hprev := st230_p142
  have hstep := st230_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p144 : ((8350804396901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT230 (i+1))
      = (∑ i ∈ Finset.range 143, stT230 (i+1)) + stT230 144 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 143
    simpa using h
  have hprev := st230_p143
  have hstep := st230_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p145 : ((860348123753/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT230 (i+1))
      = (∑ i ∈ Finset.range 144, stT230 (i+1)) + stT230 145 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 144
    simpa using h
  have hprev := st230_p144
  have hstep := st230_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p146 : ((8272615531411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT230 (i+1))
      = (∑ i ∈ Finset.range 145, stT230 (i+1)) + stT230 146 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 145
    simpa using h
  have hprev := st230_p145
  have hstep := st230_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p147 : ((320984809033/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT230 (i+1))
      = (∑ i ∈ Finset.range 146, stT230 (i+1)) + stT230 147 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 146
    simpa using h
  have hprev := st230_p146
  have hstep := st230_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p148 : ((2087534825689/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT230 (i+1))
      = (∑ i ∈ Finset.range 147, stT230 (i+1)) + stT230 148 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 147
    simpa using h
  have hprev := st230_p147
  have hstep := st230_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p149 : ((17214441908039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT230 (i+1))
      = (∑ i ∈ Finset.range 148, stT230 (i+1)) + stT230 149 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 148
    simpa using h
  have hprev := st230_p148
  have hstep := st230_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p150 : ((2074460212751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT230 (i+1))
      = (∑ i ∈ Finset.range 149, stT230 (i+1)) + stT230 150 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 149
    simpa using h
  have hprev := st230_p149
  have hstep := st230_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p151 : ((1603888564063/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT230 (i+1))
      = (∑ i ∈ Finset.range 150, stT230 (i+1)) + stT230 151 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 150
    simpa using h
  have hprev := st230_p150
  have hstep := st230_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p152 : ((132803222801/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT230 (i+1))
      = (∑ i ∈ Finset.range 151, stT230 (i+1)) + stT230 152 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 151
    simpa using h
  have hprev := st230_p151
  have hstep := st230_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p153 : ((17217592084417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT230 (i+1))
      = (∑ i ∈ Finset.range 152, stT230 (i+1)) + stT230 153 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 152
    simpa using h
  have hprev := st230_p152
  have hstep := st230_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p154 : ((8371496882257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT230 (i+1))
      = (∑ i ∈ Finset.range 153, stT230 (i+1)) + stT230 154 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 153
    simpa using h
  have hprev := st230_p153
  have hstep := st230_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p155 : ((8028589412737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT230 (i+1))
      = (∑ i ∈ Finset.range 154, stT230 (i+1)) + stT230 155 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 154
    simpa using h
  have hprev := st230_p154
  have hstep := st230_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p156 : ((8204818683457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT230 (i+1))
      = (∑ i ∈ Finset.range 155, stT230 (i+1)) + stT230 156 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 155
    simpa using h
  have hprev := st230_p155
  have hstep := st230_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p157 : ((428949686137/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT230 (i+1))
      = (∑ i ∈ Finset.range 156, stT230 (i+1)) + stT230 157 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 156
    simpa using h
  have hprev := st230_p156
  have hstep := st230_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p158 : ((1696553798749/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT230 (i+1))
      = (∑ i ∈ Finset.range 157, stT230 (i+1)) + stT230 158 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 157
    simpa using h
  have hprev := st230_p157
  have hstep := st230_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p159 : ((8089297036997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT230 (i+1))
      = (∑ i ∈ Finset.range 158, stT230 (i+1)) + stT230 159 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 158
    simpa using h
  have hprev := st230_p158
  have hstep := st230_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p160 : ((252738144791/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT230 (i+1))
      = (∑ i ∈ Finset.range 159, stT230 (i+1)) + stT230 160 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 159
    simpa using h
  have hprev := st230_p159
  have hstep := st230_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p161 : ((8477691343207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT230 (i+1))
      = (∑ i ∈ Finset.range 160, stT230 (i+1)) + stT230 161 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 160
    simpa using h
  have hprev := st230_p160
  have hstep := st230_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p162 : ((429474028773/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT230 (i+1))
      = (∑ i ∈ Finset.range 161, stT230 (i+1)) + stT230 162 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 161
    simpa using h
  have hprev := st230_p161
  have hstep := st230_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p163 : ((16471608324213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT230 (i+1))
      = (∑ i ∈ Finset.range 162, stT230 (i+1)) + stT230 163 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 162
    simpa using h
  have hprev := st230_p162
  have hstep := st230_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p164 : ((4006366462221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT230 (i+1))
      = (∑ i ∈ Finset.range 163, stT230 (i+1)) + stT230 164 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 163
    simpa using h
  have hprev := st230_p163
  have hstep := st230_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p165 : ((4144621479037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT230 (i+1))
      = (∑ i ∈ Finset.range 164, stT230 (i+1)) + stT230 165 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 164
    simpa using h
  have hprev := st230_p164
  have hstep := st230_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p166 : ((8607525385849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT230 (i+1))
      = (∑ i ∈ Finset.range 165, stT230 (i+1)) + stT230 166 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 165
    simpa using h
  have hprev := st230_p165
  have hstep := st230_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p167 : ((8449869192473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT230 (i+1))
      = (∑ i ∈ Finset.range 166, stT230 (i+1)) + stT230 167 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 166
    simpa using h
  have hprev := st230_p166
  have hstep := st230_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p168 : ((807355483207/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT230 (i+1))
      = (∑ i ∈ Finset.range 167, stT230 (i+1)) + stT230 168 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 167
    simpa using h
  have hprev := st230_p167
  have hstep := st230_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p169 : ((403987625909/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT230 (i+1))
      = (∑ i ∈ Finset.range 168, stT230 (i+1)) + stT230 169 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 168
    simpa using h
  have hprev := st230_p168
  have hstep := st230_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p170 : ((4227872749101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT230 (i+1))
      = (∑ i ∈ Finset.range 169, stT230 (i+1)) + stT230 170 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 169
    simpa using h
  have hprev := st230_p169
  have hstep := st230_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p171 : ((17222941927129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT230 (i+1))
      = (∑ i ∈ Finset.range 170, stT230 (i+1)) + stT230 171 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 170
    simpa using h
  have hprev := st230_p170
  have hstep := st230_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p172 : ((16615532378399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT230 (i+1))
      = (∑ i ∈ Finset.range 171, stT230 (i+1)) + stT230 172 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 171
    simpa using h
  have hprev := st230_p171
  have hstep := st230_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p173 : ((16026291721249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT230 (i+1))
      = (∑ i ∈ Finset.range 172, stT230 (i+1)) + stT230 173 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 172
    simpa using h
  have hprev := st230_p172
  have hstep := st230_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p174 : ((653938182541/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT230 (i+1))
      = (∑ i ∈ Finset.range 173, stT230 (i+1)) + stT230 174 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 173
    simpa using h
  have hprev := st230_p173
  have hstep := st230_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p175 : ((17091272504221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT230 (i+1))
      = (∑ i ∈ Finset.range 174, stT230 (i+1)) + stT230 175 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 174
    simpa using h
  have hprev := st230_p174
  have hstep := st230_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p176 : ((17146975944643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT230 (i+1))
      = (∑ i ∈ Finset.range 175, stT230 (i+1)) + stT230 176 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 175
    simpa using h
  have hprev := st230_p175
  have hstep := st230_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p177 : ((8219370910211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT230 (i+1))
      = (∑ i ∈ Finset.range 176, stT230 (i+1)) + stT230 177 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 176
    simpa using h
  have hprev := st230_p176
  have hstep := st230_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p178 : ((8002607005343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT230 (i+1))
      = (∑ i ∈ Finset.range 177, stT230 (i+1)) + stT230 178 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 177
    simpa using h
  have hprev := st230_p177
  have hstep := st230_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p179 : ((16470392889331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT230 (i+1))
      = (∑ i ∈ Finset.range 178, stT230 (i+1)) + stT230 179 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 178
    simpa using h
  have hprev := st230_p178
  have hstep := st230_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p180 : ((17161885555611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT230 (i+1))
      = (∑ i ∈ Finset.range 179, stT230 (i+1)) + stT230 180 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 179
    simpa using h
  have hprev := st230_p179
  have hstep := st230_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p181 : ((17098143549591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT230 (i+1))
      = (∑ i ∈ Finset.range 180, stT230 (i+1)) + stT230 181 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 180
    simpa using h
  have hprev := st230_p180
  have hstep := st230_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p182 : ((16374364812091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT230 (i+1))
      = (∑ i ∈ Finset.range 181, stT230 (i+1)) + stT230 182 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 181
    simpa using h
  have hprev := st230_p181
  have hstep := st230_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p183 : ((16001718566559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT230 (i+1))
      = (∑ i ∈ Finset.range 182, stT230 (i+1)) + stT230 183 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 182
    simpa using h
  have hprev := st230_p182
  have hstep := st230_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p184 : ((8245308572567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT230 (i+1))
      = (∑ i ∈ Finset.range 183, stT230 (i+1)) + stT230 184 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 183
    simpa using h
  have hprev := st230_p183
  have hstep := st230_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p185 : ((8583743016261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT230 (i+1))
      = (∑ i ∈ Finset.range 184, stT230 (i+1)) + stT230 185 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 184
    simpa using h
  have hprev := st230_p184
  have hstep := st230_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p186 : ((8558070224193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT230 (i+1))
      = (∑ i ∈ Finset.range 185, stT230 (i+1)) + stT230 186 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 185
    simpa using h
  have hprev := st230_p185
  have hstep := st230_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p187 : ((8205419670127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT230 (i+1))
      = (∑ i ∈ Finset.range 186, stT230 (i+1)) + stT230 187 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 186
    simpa using h
  have hprev := st230_p186
  have hstep := st230_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p188 : ((15992016436429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT230 (i+1))
      = (∑ i ∈ Finset.range 187, stT230 (i+1)) + stT230 188 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 187
    simpa using h
  have hprev := st230_p187
  have hstep := st230_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p189 : ((16407803887117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT230 (i+1))
      = (∑ i ∈ Finset.range 188, stT230 (i+1)) + stT230 189 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 188
    simpa using h
  have hprev := st230_p188
  have hstep := st230_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p190 : ((17110430295021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT230 (i+1))
      = (∑ i ∈ Finset.range 189, stT230 (i+1)) + stT230 190 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 189
    simpa using h
  have hprev := st230_p189
  have hstep := st230_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p191 : ((17191256405117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT230 (i+1))
      = (∑ i ∈ Finset.range 190, stT230 (i+1)) + stT230 191 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 190
    simpa using h
  have hprev := st230_p190
  have hstep := st230_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p192 : ((16551669797061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT230 (i+1))
      = (∑ i ∈ Finset.range 191, stT230 (i+1)) + stT230 192 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 191
    simpa using h
  have hprev := st230_p191
  have hstep := st230_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p193 : ((3201437891521/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT230 (i+1))
      = (∑ i ∈ Finset.range 192, stT230 (i+1)) + stT230 193 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 192
    simpa using h
  have hprev := st230_p192
  have hstep := st230_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p194 : ((3248082904823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT230 (i+1))
      = (∑ i ∈ Finset.range 193, stT230 (i+1)) + stT230 194 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 193
    simpa using h
  have hprev := st230_p193
  have hstep := st230_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p195 : ((3391062942177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT230 (i+1))
      = (∑ i ∈ Finset.range 194, stT230 (i+1)) + stT230 195 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 194
    simpa using h
  have hprev := st230_p194
  have hstep := st230_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p196 : ((863352969957/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT230 (i+1))
      = (∑ i ∈ Finset.range 195, stT230 (i+1)) + stT230 196 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 195
    simpa using h
  have hprev := st230_p195
  have hstep := st230_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p197 : ((16797876583981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT230 (i+1))
      = (∑ i ∈ Finset.range 196, stT230 (i+1)) + stT230 197 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 196
    simpa using h
  have hprev := st230_p196
  have hstep := st230_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p198 : ((16121603011981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT230 (i+1))
      = (∑ i ∈ Finset.range 197, stT230 (i+1)) + stT230 198 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 197
    simpa using h
  have hprev := st230_p197
  have hstep := st230_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p199 : ((16051119583603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT230 (i+1))
      = (∑ i ∈ Finset.range 198, stT230 (i+1)) + stT230 199 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 198
    simpa using h
  have hprev := st230_p198
  have hstep := st230_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p200 : ((16665613082359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT230 (i+1))
      = (∑ i ∈ Finset.range 199, stT230 (i+1)) + stT230 200 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 199
    simpa using h
  have hprev := st230_p199
  have hstep := st230_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p201 : ((17235647518939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT230 (i+1))
      = (∑ i ∈ Finset.range 200, stT230 (i+1)) + stT230 201 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 200
    simpa using h
  have hprev := st230_p200
  have hstep := st230_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p202 : ((17095616741381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT230 (i+1))
      = (∑ i ∈ Finset.range 201, stT230 (i+1)) + stT230 202 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 201
    simpa using h
  have hprev := st230_p201
  have hstep := st230_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p203 : ((4103239353731/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT230 (i+1))
      = (∑ i ∈ Finset.range 202, stT230 (i+1)) + stT230 203 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 202
    simpa using h
  have hprev := st230_p202
  have hstep := st230_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p204 : ((15975266369197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT230 (i+1))
      = (∑ i ∈ Finset.range 203, stT230 (i+1)) + stT230 204 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 203
    simpa using h
  have hprev := st230_p203
  have hstep := st230_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p205 : ((16278674837647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT230 (i+1))
      = (∑ i ∈ Finset.range 204, stT230 (i+1)) + stT230 205 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 204
    simpa using h
  have hprev := st230_p204
  have hstep := st230_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p206 : ((16975371607531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT230 (i+1))
      = (∑ i ∈ Finset.range 205, stT230 (i+1)) + stT230 206 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 205
    simpa using h
  have hprev := st230_p205
  have hstep := st230_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p207 : ((17283357107003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT230 (i+1))
      = (∑ i ∈ Finset.range 206, stT230 (i+1)) + stT230 207 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 206
    simpa using h
  have hprev := st230_p206
  have hstep := st230_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p208 : ((16864079573563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT230 (i+1))
      = (∑ i ∈ Finset.range 207, stT230 (i+1)) + stT230 208 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 207
    simpa using h
  have hprev := st230_p207
  have hstep := st230_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p209 : ((16183710082993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT230 (i+1))
      = (∑ i ∈ Finset.range 208, stT230 (i+1)) + stT230 209 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 208
    simpa using h
  have hprev := st230_p208
  have hstep := st230_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p210 : ((15985494835087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT230 (i+1))
      = (∑ i ∈ Finset.range 209, stT230 (i+1)) + stT230 210 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 209
    simpa using h
  have hprev := st230_p209
  have hstep := st230_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p211 : ((16479952738663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT230 (i+1))
      = (∑ i ∈ Finset.range 210, stT230 (i+1)) + stT230 211 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 210
    simpa using h
  have hprev := st230_p210
  have hstep := st230_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p212 : ((17132283459481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT230 (i+1))
      = (∑ i ∈ Finset.range 211, stT230 (i+1)) + stT230 212 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 211
    simpa using h
  have hprev := st230_p211
  have hstep := st230_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p213 : ((17248459825633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT230 (i+1))
      = (∑ i ∈ Finset.range 212, stT230 (i+1)) + stT230 213 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 212
    simpa using h
  have hprev := st230_p212
  have hstep := st230_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p214 : ((133680386813/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT230 (i+1))
      = (∑ i ∈ Finset.range 213, stT230 (i+1)) + stT230 214 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 213
    simpa using h
  have hprev := st230_p213
  have hstep := st230_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p215 : ((3216818030559/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT230 (i+1))
      = (∑ i ∈ Finset.range 214, stT230 (i+1)) + stT230 215 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 214
    simpa using h
  have hprev := st230_p214
  have hstep := st230_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p216 : ((16019397750503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT230 (i+1))
      = (∑ i ∈ Finset.range 215, stT230 (i+1)) + stT230 216 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 215
    simpa using h
  have hprev := st230_p215
  have hstep := st230_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p217 : ((16578246569687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT230 (i+1))
      = (∑ i ∈ Finset.range 216, stT230 (i+1)) + stT230 217 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 216
    simpa using h
  have hprev := st230_p216
  have hstep := st230_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p218 : ((17186933435747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT230 (i+1))
      = (∑ i ∈ Finset.range 217, stT230 (i+1)) + stT230 218 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 217
    simpa using h
  have hprev := st230_p217
  have hstep := st230_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p219 : ((8615161592127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT230 (i+1))
      = (∑ i ∈ Finset.range 218, stT230 (i+1)) + stT230 219 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 218
    simpa using h
  have hprev := st230_p218
  have hstep := st230_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p220 : ((8334523145327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT230 (i+1))
      = (∑ i ∈ Finset.range 219, stT230 (i+1)) + stT230 220 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 219
    simpa using h
  have hprev := st230_p219
  have hstep := st230_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p221 : ((16065021588323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT230 (i+1))
      = (∑ i ∈ Finset.range 220, stT230 (i+1)) + stT230 221 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 220
    simpa using h
  have hprev := st230_p220
  have hstep := st230_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p222 : ((8006810514739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT230 (i+1))
      = (∑ i ∈ Finset.range 221, stT230 (i+1)) + stT230 222 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 221
    simpa using h
  have hprev := st230_p221
  have hstep := st230_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p223 : ((8280521507701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT230 (i+1))
      = (∑ i ∈ Finset.range 222, stT230 (i+1)) + stT230 223 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 222
    simpa using h
  have hprev := st230_p222
  have hstep := st230_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p224 : ((17172340872173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT230 (i+1))
      = (∑ i ∈ Finset.range 223, stT230 (i+1)) + stT230 224 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 223
    simpa using h
  have hprev := st230_p223
  have hstep := st230_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p225 : ((17259318118529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT230 (i+1))
      = (∑ i ∈ Finset.range 224, stT230 (i+1)) + stT230 225 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 224
    simpa using h
  have hprev := st230_p224
  have hstep := st230_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p226 : ((16742778681681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT230 (i+1))
      = (∑ i ∈ Finset.range 225, stT230 (i+1)) + stT230 226 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 225
    simpa using h
  have hprev := st230_p225
  have hstep := st230_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p227 : ((16115639148561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT230 (i+1))
      = (∑ i ∈ Finset.range 226, stT230 (i+1)) + stT230 227 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 226
    simpa using h
  have hprev := st230_p226
  have hstep := st230_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p228 : ((3991787238289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT230 (i+1))
      = (∑ i ∈ Finset.range 227, stT230 (i+1)) + stT230 228 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 227
    simpa using h
  have hprev := st230_p227
  have hstep := st230_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p229 : ((8216041988753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT230 (i+1))
      = (∑ i ∈ Finset.range 228, stT230 (i+1)) + stT230 229 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 228
    simpa using h
  have hprev := st230_p228
  have hstep := st230_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p230 : ((8538343635853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT230 (i+1))
      = (∑ i ∈ Finset.range 229, stT230 (i+1)) + stT230 230 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 229
    simpa using h
  have hprev := st230_p229
  have hstep := st230_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p231 : ((2163638557807/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT230 (i+1))
      = (∑ i ∈ Finset.range 230, stT230 (i+1)) + stT230 231 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 230
    simpa using h
  have hprev := st230_p230
  have hstep := st230_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p232 : ((1692100423177/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT230 (i+1))
      = (∑ i ∈ Finset.range 231, stT230 (i+1)) + stT230 232 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 231
    simpa using h
  have hprev := st230_p231
  have hstep := st230_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p233 : ((8133348601769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT230 (i+1))
      = (∑ i ∈ Finset.range 232, stT230 (i+1)) + stT230 233 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 232
    simpa using h
  have hprev := st230_p232
  have hstep := st230_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p234 : ((15933423046807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT230 (i+1))
      = (∑ i ∈ Finset.range 233, stT230 (i+1)) + stT230 234 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 233
    simpa using h
  have hprev := st230_p233
  have hstep := st230_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p235 : ((16214723188607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT230 (i+1))
      = (∑ i ∈ Finset.range 234, stT230 (i+1)) + stT230 235 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 234
    simpa using h
  have hprev := st230_p234
  have hstep := st230_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p236 : ((3371699017523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT230 (i+1))
      = (∑ i ∈ Finset.range 235, stT230 (i+1)) + stT230 236 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 235
    simpa using h
  have hprev := st230_p235
  have hstep := st230_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p237 : ((864979083461/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT230 (i+1))
      = (∑ i ∈ Finset.range 236, stT230 (i+1)) + stT230 237 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 236
    simpa using h
  have hprev := st230_p236
  have hstep := st230_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p238 : ((1072306228309/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT230 (i+1))
      = (∑ i ∈ Finset.range 237, stT230 (i+1)) + stT230 238 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 237
    simpa using h
  have hprev := st230_p237
  have hstep := st230_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p239 : ((4139314886751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT230 (i+1))
      = (∑ i ∈ Finset.range 238, stT230 (i+1)) + stT230 239 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 238
    simpa using h
  have hprev := st230_p238
  have hstep := st230_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p240 : ((800790533031/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT230 (i+1))
      = (∑ i ∈ Finset.range 239, stT230 (i+1)) + stT230 240 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 239
    simpa using h
  have hprev := st230_p239
  have hstep := st230_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p241 : ((7995441536517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT230 (i+1))
      = (∑ i ∈ Finset.range 240, stT230 (i+1)) + stT230 241 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 240
    simpa using h
  have hprev := st230_p240
  have hstep := st230_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p242 : ((8249914666337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT230 (i+1))
      = (∑ i ∈ Finset.range 241, stT230 (i+1)) + stT230 242 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 241
    simpa using h
  have hprev := st230_p241
  have hstep := st230_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p243 : ((8557128374837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT230 (i+1))
      = (∑ i ∈ Finset.range 242, stT230 (i+1)) + stT230 243 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 242
    simpa using h
  have hprev := st230_p242
  have hstep := st230_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p244 : ((1732460776821/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT230 (i+1))
      = (∑ i ∈ Finset.range 243, stT230 (i+1)) + stT230 244 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 243
    simpa using h
  have hprev := st230_p243
  have hstep := st230_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p245 : ((1696076731671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT230 (i+1))
      = (∑ i ∈ Finset.range 244, stT230 (i+1)) + stT230 245 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 244
    simpa using h
  have hprev := st230_p244
  have hstep := st230_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p246 : ((8161704821599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT230 (i+1))
      = (∑ i ∈ Finset.range 245, stT230 (i+1)) + stT230 246 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 245
    simpa using h
  have hprev := st230_p245
  have hstep := st230_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p247 : ((15930341403023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT230 (i+1))
      = (∑ i ∈ Finset.range 246, stT230 (i+1)) + stT230 247 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 246
    simpa using h
  have hprev := st230_p246
  have hstep := st230_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p248 : ((16095684608023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT230 (i+1))
      = (∑ i ∈ Finset.range 247, stT230 (i+1)) + stT230 248 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 247
    simpa using h
  have hprev := st230_p247
  have hstep := st230_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p249 : ((16683750061271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT230 (i+1))
      = (∑ i ∈ Finset.range 248, stT230 (i+1)) + stT230 249 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 248
    simpa using h
  have hprev := st230_p248
  have hstep := st230_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_p250 : ((8613077110503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT230 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT230 (i+1))
      = (∑ i ∈ Finset.range 249, stT230 (i+1)) + stT230 250 := by
    have h := Finset.sum_range_succ (fun i => stT230 (i+1)) 249
    simpa using h
  have hprev := st230_p249
  have hstep := st230_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st230_s250 :
    |Real.sin (((230 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((96253/500000 : ℚ) : ℝ))
      - ((102841/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1350201/10000000) (δ := 11551/1000000000) (ψ := 96253/500000) 230 202
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 230`** (evaluated boundary). -/
theorem station_230_sign : hardyG ((((230:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 230 250 (by norm_num) (by norm_num)
    ((96253/500000 : ℚ) : ℝ)
  have hchain := st230_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT230 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((230 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((96253/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st230_c250
  have hsinb := abs_le.mp st230_s250
  have hbdy_lo : ((-18769318998969/529002500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((230 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((96253/500000 : ℚ) : ℝ))) / 2
          - ((((230:ℕ)):ℝ))
            * Real.sin (((230 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((96253/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((230:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((230:ℝ) * Real.log (250:ℝ) - ((96253/500000 : ℚ) : ℝ))) / 2
        - ((230:ℝ)) * Real.sin ((230:ℝ) * Real.log (250:ℝ) - ((96253/500000 : ℚ) : ℝ))
        ≥ ((-237415017/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((230:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-237415017/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-237415017/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-237415017/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((230:ℕ)):ℝ))+1) * (((((230:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((91267274593/78125000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8613077110503/5000000000000 : ℚ) : ℝ) + ((-18769318998969/529002500000000 : ℚ) : ℝ)
      - ((91267274593/78125000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((96253/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((230:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((96253/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((230:ℕ)):ℝ)))).re
      - Real.sin ((96253/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((230:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((230:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((230:ℕ)):ℝ))
      = (((((230:ℕ)):ℝ)) * (Real.log ((((230:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((230:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_230
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
  have hθwin : |(((96253/500000 : ℚ) : ℝ) + ((48:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((230:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((230:ℕ)):ℝ)))
    (φ := ((96253/500000 : ℚ) : ℝ) + ((48:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((96253/500000 : ℚ) : ℝ) + ((48:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((96253/500000 : ℚ)) : ℝ) - Real.pi) + ((48:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((96253/500000 : ℚ)) : ℝ) - Real.pi) 48).1,
    (cos_sin_shift ((((96253/500000 : ℚ)) : ℝ) - Real.pi) 48).2]
  exact cos_sin_flip ((96253/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_230_sign
end AxiomAudit
