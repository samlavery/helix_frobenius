import RequestProject.DVPSqrtTable

/-!
# Station `t = 84` of the extended Hardy ladder (rung-91)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT84 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((84 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((134393/250000 : ℚ) : ℝ))

theorem st84_c1 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((429477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1343931/10000000) (δ := 41/100000000) (ψ := 134393/250000) 84 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t1 : ((107363/125000 : ℚ) : ℝ) ≤ stT84 1 := by
  have hc : ((107363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107363/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((107363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c2 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((419299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 711327/2500000) (δ := 329/50000000) (ψ := 134393/250000) 84 9
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t2 : ((2964537768683/10000000000000 : ℚ) : ℝ) ≤ stT84 2 := by
  have hc : ((419249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2964537768683/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((419249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c3 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-802291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6254799/10000000) (δ := 361/50000000) (ψ := 134393/250000) 84 15
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t3 : ((-4632318170523/10000000000000 : ℚ) : ℝ) ≤ stT84 3 := by
  have hc : ((-802341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4632318170523/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-802341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c4 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-946761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7034547/10000000) (δ := 257/50000000) (ψ := 134393/250000) 84 18
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t4 : ((-4734055946811/10000000000000 : ℚ) : ℝ) ≤ stT84 4 := by
  have hc : ((-946811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4734055946811/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-946811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c5 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-907597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3385401/5000000) (δ := 97/12500000) (ψ := 134393/250000) 84 21
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t5 : ((-507390102999/1250000000000 : ℚ) : ℝ) ≤ stT84 5 := by
  have hc : ((-907647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-507390102999/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-907647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c6 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((677657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51639/250000) (δ := 579/100000000) (ψ := 134393/250000) 84 24
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t6 : ((1383159190287/5000000000000 : ℚ) : ℝ) ≤ stT84 6 := by
  have hc : ((677607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1383159190287/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((677607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c7 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((903067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277461/2500000) (δ := 443/100000000) (ψ := 134393/250000) 84 26
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t7 : ((853270696487/2500000000000 : ℚ) : ℝ) ≤ stT84 7 := by
  have hc : ((903017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((853270696487/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((903017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c8 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-110517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2242089/5000000) (δ := 501/100000000) (ψ := 134393/250000) 84 28
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t8 : ((-97706249857/1250000000000 : ℚ) : ℝ) ≤ stT84 8 := by
  have hc : ((-55271/250000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97706249857/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-55271/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c9 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-48729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 567787/1250000) (δ := 79/12500000) (ψ := 134393/250000) 84 29
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t9 : ((-81231682913/1000000000000 : ℚ) : ℝ) ≤ stT84 9 := by
  have hc : ((-48739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81231682913/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-48739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c10 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-322503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2373961/5000000) (δ := 387/50000000) (ψ := 134393/250000) 84 31
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t10 : ((-510001127867/5000000000000 : ℚ) : ℝ) ≤ stT84 10 := by
  have hc : ((-322553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-510001127867/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-322553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c11 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((1969/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110187/2500000) (δ := 73/12500000) (ψ := 134393/250000) 84 32
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t11 : ((59364559857/200000000000 : ℚ) : ℝ) ≤ stT84 11 := by
  have hc : ((19689/20000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59364559857/200000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((19689/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c12 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((33019/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1061839/5000000) (δ := 7/1562500) (ψ := 134393/250000) 84 33
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t12 : ((190620828783/1000000000000 : ℚ) : ℝ) ≤ stT84 12 := by
  have hc : ((66033/100000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190620828783/1000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((66033/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c13 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((277243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3224683/10000000) (δ := 223/50000000) (ψ := 134393/250000) 84 34
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t13 : ((1537589571/20000000000 : ℚ) : ℝ) ≤ stT84 13 := by
  have hc : ((277193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1537589571/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((277193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c14 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((332581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1539697/5000000) (δ := 313/50000000) (ψ := 134393/250000) 84 35
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t14 : ((222181585243/2500000000000 : ℚ) : ℝ) ≤ stT84 14 := by
  have hc : ((332531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222181585243/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((332531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c15 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((735783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 929967/5000000) (δ := 107/12500000) (ψ := 134393/250000) 84 36
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t15 : ((474913444301/2500000000000 : ℚ) : ℝ) ≤ stT84 15 := by
  have hc : ((735733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474913444301/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((735733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c16 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((993049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14747/500000) (δ := 137/20000000) (ψ := 134393/250000) 84 37
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t16 : ((992999/4000000 : ℚ) : ℝ) ≤ stT84 16 := by
  have hc : ((992999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((992999/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((992999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c17 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((259113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -817933/2500000) (δ := 237/50000000) (ψ := 134393/250000) 84 38
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t17 : ((157080000357/2500000000000 : ℚ) : ℝ) ≤ stT84 17 := by
  have hc : ((259063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157080000357/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((259063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c18 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-469511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6976429/10000000) (δ := 23/5000000) (ψ := 134393/250000) 84 39
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t18 : ((-34584598479/156250000000 : ℚ) : ℝ) ≤ stT84 18 := by
  have hc : ((-14673/15625 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34584598479/156250000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-14673/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c19 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-22413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 547211/1250000) (δ := 33/5000000) (ψ := 134393/250000) 84 39
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t19 : ((-102866603483/2500000000000 : ℚ) : ℝ) ≤ stT84 19 := by
  have hc : ((-89677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102866603483/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-89677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c20 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((487567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139671/2500000) (δ := 59/10000000) (ψ := 134393/250000) 84 40
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t20 : ((545088288657/2500000000000 : ℚ) : ℝ) ≤ stT84 20 := by
  have hc : ((243771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((545088288657/2500000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((243771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c21 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-148593/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6020713/10000000) (δ := 281/50000000) (ψ := 134393/250000) 84 41
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t21 : ((-324278345937/2000000000000 : ℚ) : ℝ) ≤ stT84 21 := by
  have hc : ((-148603/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324278345937/2000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-148603/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c22 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((71339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3748491/10000000) (δ := 441/100000000) (ψ := 134393/250000) 84 41
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t22 : ((151988647023/10000000000000 : ℚ) : ℝ) ≤ stT84 22 := by
  have hc : ((71289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151988647023/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((71289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c23 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((497709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312301/5000000) (δ := 711/100000000) (ψ := 134393/250000) 84 42
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t23 : ((129711334737/1250000000000 : ℚ) : ℝ) ≤ stT84 23 := by
  have hc : ((497659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129711334737/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((497659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c24 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-16319/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6312917/10000000) (δ := 591/100000000) (ψ := 134393/250000) 84 42
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t24 : ((-52051671/312500000 : ℚ) : ℝ) ≤ stT84 24 := by
  have hc : ((-102/125 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52051671/312500000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-102/125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c25 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((7571/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -205607/2500000) (δ := 661/100000000) (ψ := 134393/250000) 84 43
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t25 : ((37853/200000 : ℚ) : ℝ) ≤ stT84 25 := by
  have hc : ((37853/40000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37853/200000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((37853/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c26 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-246137/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3706961/5000000) (δ := 541/100000000) (ψ := 134393/250000) 84 43
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t26 : ((-482739045719/2500000000000 : ℚ) : ℝ) ≤ stT84 26 := by
  have hc : ((-492299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482739045719/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-492299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c27 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((30911/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92143/2500000) (δ := 553/100000000) (ψ := 134393/250000) 84 44
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t27 : ((1903526799/10000000000 : ℚ) : ℝ) ≤ stT84 27 := by
  have hc : ((494551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1903526799/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((494551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c28 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-486357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7268633/10000000) (δ := 77/10000000) (ψ := 134393/250000) 84 44
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t28 : ((-459587945193/2500000000000 : ℚ) : ℝ) ≤ stT84 28 := by
  have hc : ((-243191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459587945193/2500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-243191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c29 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((227443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1070153/10000000) (δ := 599/100000000) (ψ := 134393/250000) 84 45
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t29 : ((844655498533/5000000000000 : ℚ) : ℝ) ≤ stT84 29 := by
  have hc : ((454861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((844655498533/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((454861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c30 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-93817/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6049173/10000000) (δ := 171/25000000) (ψ := 134393/250000) 84 45
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t30 : ((-342594096203/2500000000000 : ℚ) : ℝ) ≤ stT84 30 := by
  have hc : ((-375293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342594096203/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-375293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c31 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((111351/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43327/156250) (δ := 207/25000000) (ψ := 134393/250000) 84 46
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t31 : ((399939693881/5000000000000 : ℚ) : ℝ) ≤ stT84 31 := by
  have hc : ((222677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399939693881/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((222677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c32 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((3269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3894299/10000000) (δ := 207/25000000) (ψ := 134393/250000) 84 46
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t32 : ((5756729979/2500000000000 : ℚ) : ℝ) ≤ stT84 32 := by
  have hc : ((6513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5756729979/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((6513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c33 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-269753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83619/156250) (δ := 101/20000000) (ψ := 134393/250000) 84 47
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t33 : ((-234811668753/2500000000000 : ℚ) : ℝ) ≤ stT84 33 := by
  have hc : ((-134889/250000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234811668753/2500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-134889/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c34 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((933407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 458753/5000000) (δ := 329/50000000) (ψ := 134393/250000) 84 47
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t34 : ((320138650929/2000000000000 : ℚ) : ℝ) ≤ stT84 34 := by
  have hc : ((933357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320138650929/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((933357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c35 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-235719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7004889/10000000) (δ := 101/20000000) (ψ := 134393/250000) 84 47
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t35 : ((-796918152067/5000000000000 : ℚ) : ℝ) ≤ stT84 35 := by
  have hc : ((-471463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-796918152067/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-471463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c36 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((440289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278719/1000000) (δ := 527/100000000) (ψ := 134393/250000) 84 48
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t36 : ((366865686587/5000000000000 : ℚ) : ℝ) ≤ stT84 36 := by
  have hc : ((440239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366865686587/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((440239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c37 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((374779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1483297/5000000) (δ := 767/100000000) (ψ := 134393/250000) 84 48
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t37 : ((616050353981/10000000000000 : ℚ) : ℝ) ≤ stT84 37 := by
  have hc : ((374729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((616050353981/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((374729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c38 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-239903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7141037/10000000) (δ := 487/100000000) (ψ := 134393/250000) 84 49
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t38 : ((-155677809133/1000000000000 : ℚ) : ℝ) ≤ stT84 38 := by
  have hc : ((-479831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155677809133/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-479831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c39 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((195259/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337237/2000000) (δ := 119/25000000) (ψ := 134393/250000) 84 49
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t39 : ((625289021533/5000000000000 : ℚ) : ℝ) ≤ stT84 39 := by
  have hc : ((390493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((625289021533/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((390493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c40 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((118297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 726111/2000000) (δ := 447/100000000) (ψ := 134393/250000) 84 49
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t40 : ((93482412543/5000000000000 : ℚ) : ℝ) ≤ stT84 40 := by
  have hc : ((118247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93482412543/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((118247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c41 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-92687/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172299/250000) (δ := 537/100000000) (ψ := 134393/250000) 84 50
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t41 : ((-18095077337/125000000000 : ℚ) : ℝ) ≤ stT84 41 := by
  have hc : ((-23173/25000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18095077337/125000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-23173/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c42 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((148689/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -915737/5000000) (δ := 353/50000000) (ψ := 134393/250000) 84 50
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t42 : ((229416603407/2000000000000 : ℚ) : ℝ) ≤ stT84 42 := by
  have hc : ((148679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229416603407/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((148679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c43 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((321037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310993/1000000) (δ := 373/50000000) (ψ := 134393/250000) 84 50
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t43 : ((97900072039/2000000000000 : ℚ) : ℝ) ≤ stT84 43 := by
  have hc : ((320987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97900072039/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((320987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c44 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-999439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3885117/5000000) (δ := 23/4000000) (ψ := 134393/250000) 84 51
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t44 : ((-1506786638373/10000000000000 : ℚ) : ℝ) ≤ stT84 44 := by
  have hc : ((-999489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1506786638373/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-999489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c45 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((68659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1525467/5000000) (δ := 187/25000000) (ψ := 134393/250000) 84 51
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t45 : ((102335819439/2000000000000 : ℚ) : ℝ) ≤ stT84 45 := by
  have hc : ((68649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102335819439/2000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((68649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c46 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((810463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391159/2500000) (δ := 197/25000000) (ψ := 134393/250000) 84 51
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t46 : ((1194888325047/10000000000000 : ℚ) : ℝ) ≤ stT84 46 := by
  have hc : ((810413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1194888325047/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((810413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c47 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-94859/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6080939/10000000) (δ := 171/20000000) (ψ := 134393/250000) 84 51
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t47 : ((-11070015753/100000000000 : ℚ) : ℝ) ≤ stT84 47 := by
  have hc : ((-379461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11070015753/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-379461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c48 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-489509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325363/625000) (δ := 191/25000000) (ψ := 134393/250000) 84 52
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t48 : ((-44163606949/625000000000 : ℚ) : ℝ) ≤ stT84 48 := by
  have hc : ((-489559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44163606949/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-489559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c49 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((939269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -437879/5000000) (δ := 799/100000000) (ψ := 134393/250000) 84 52
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t49 : ((1341741026049/10000000000000 : ℚ) : ℝ) ≤ stT84 49 := by
  have hc : ((939219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1341741026049/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((939219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c50 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((111101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3366811/10000000) (δ := 201/25000000) (ψ := 134393/250000) 84 52
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t50 : ((39271280797/1250000000000 : ℚ) : ℝ) ≤ stT84 50 := by
  have hc : ((27769/125000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39271280797/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((27769/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c51 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-991373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3762681/5000000) (δ := 151/25000000) (ψ := 134393/250000) 84 52
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t51 : ((-1388270789863/10000000000000 : ℚ) : ℝ) ≤ stT84 51 := by
  have hc : ((-991423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1388270789863/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-991423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c52 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-14213/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4104803/10000000) (δ := 713/100000000) (ψ := 134393/250000) 84 53
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t52 : ((-19723759473/2000000000000 : ℚ) : ℝ) ≤ stT84 52 := by
  have hc : ((-14223/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19723759473/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-14223/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c53 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((999123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52341/5000000) (δ := 753/100000000) (ψ := 134393/250000) 84 53
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t53 : ((274466333633/2000000000000 : ℚ) : ℝ) ≤ stT84 53 := by
  have hc : ((999073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274466333633/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((999073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c54 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((42517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1910333/5000000) (δ := 473/100000000) (ψ := 134393/250000) 84 53
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t54 : ((57790240209/10000000000000 : ℚ) : ℝ) ≤ stT84 54 := by
  have hc : ((42467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57790240209/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((42467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c55 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-997409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1534797/2000000) (δ := 69/10000000) (ψ := 134393/250000) 84 53
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t55 : ((-3362434289/25000000000 : ℚ) : ℝ) ≤ stT84 55 := by
  have hc : ((-997459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3362434289/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-997459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c56 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-128881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1062523/2500000) (δ := 37/5000000) (ψ := 134393/250000) 84 54
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t56 : ((-172291397817/10000000000000 : ℚ) : ℝ) ≤ stT84 56 := by
  have hc : ((-128931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172291397817/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-128931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c57 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((15271/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -533181/10000000) (δ := 27/5000000) (ψ := 134393/250000) 84 54
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t57 : ((161807147051/1250000000000 : ℚ) : ℝ) ≤ stT84 57 := by
  have hc : ((488647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161807147051/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((488647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c58 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((317567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 623817/2000000) (δ := 783/100000000) (ψ := 134393/250000) 84 54
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t58 : ((52115017761/1250000000000 : ℚ) : ℝ) ≤ stT84 58 := by
  have hc : ((317517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52115017761/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((317517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c59 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-896927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1677229/2500000) (δ := 503/100000000) (ψ := 134393/250000) 84 54
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t59 : ((-116776538653/1000000000000 : ℚ) : ℝ) ≤ stT84 59 := by
  have hc : ((-896977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116776538653/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-896977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c60 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-578611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341847/625000) (δ := 511/100000000) (ψ := 134393/250000) 84 55
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t60 : ((-149409691539/2000000000000 : ℚ) : ℝ) ≤ stT84 60 := by
  have hc : ((-578661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149409691539/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-578661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c61 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((348583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1998399/10000000) (δ := 511/100000000) (ψ := 134393/250000) 84 55
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t61 : ((13946328417/156250000000 : ℚ) : ℝ) ≤ stT84 61 := by
  have hc : ((174279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13946328417/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((174279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c62 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((843771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1416311/10000000) (δ := 711/100000000) (ψ := 134393/250000) 84 55
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t62 : ((1071526513721/10000000000000 : ℚ) : ℝ) ≤ stT84 62 := by
  have hc : ((843721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1071526513721/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((843721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c63 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-333257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2388191/5000000) (δ := 163/25000000) (ψ := 134393/250000) 84 55
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t63 : ((-209963744887/5000000000000 : ℚ) : ℝ) ≤ stT84 63 := by
  have hc : ((-333307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209963744887/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-333307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c64 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-995787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3812213/5000000) (δ := 341/50000000) (ψ := 134393/250000) 84 56
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t64 : ((-1244797245837/10000000000000 : ℚ) : ℝ) ≤ stT84 64 := by
  have hc : ((-995837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1244797245837/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-995837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c65 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-87853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4368547/10000000) (δ := 281/50000000) (ψ := 134393/250000) 84 56
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t65 : ((-13624912693/625000000000 : ℚ) : ℝ) ≤ stT84 65 := by
  have hc : ((-43939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13624912693/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-43939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c66 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((893843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581189/5000000) (δ := 521/100000000) (ψ := 134393/250000) 84 56
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t66 : ((550091158401/5000000000000 : ℚ) : ℝ) ≤ stT84 66 := by
  have hc : ((893793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((550091158401/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((893793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c67 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((27919/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1995577/10000000) (δ := 681/100000000) (ψ := 134393/250000) 84 56
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t67 : ((17053015699/200000000000 : ℚ) : ℝ) ≤ stT84 67 := by
  have hc : ((27917/40000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17053015699/200000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((27917/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c68 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-454581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021349/2000000) (δ := 801/100000000) (ψ := 134393/250000) 84 56
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t68 : ((-551321466449/10000000000000 : ℚ) : ℝ) ≤ stT84 68 := by
  have hc : ((-454631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551321466449/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-454631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c69 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-198379/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7535471/10000000) (δ := 831/100000000) (ψ := 134393/250000) 84 57
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t69 : ((-238832383151/2000000000000 : ℚ) : ℝ) ≤ stT84 69 := by
  have hc : ((-198389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238832383151/2000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-198389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c70 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-58147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1128459/2500000) (δ := 511/100000000) (ψ := 134393/250000) 84 57
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t70 : ((-139027842051/5000000000000 : ℚ) : ℝ) ≤ stT84 70 := by
  have hc : ((-116319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139027842051/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-116319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c71 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((163467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1535063/10000000) (δ := 153/25000000) (ψ := 134393/250000) 84 57
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t71 : ((193987661917/2000000000000 : ℚ) : ℝ) ≤ stT84 71 := by
  have hc : ((163457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193987661917/2000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((163457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c72 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((42341/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21907/156250) (δ := 711/100000000) (ψ := 134393/250000) 84 57
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t72 : ((99792775947/1000000000000 : ℚ) : ℝ) ≤ stT84 72 := by
  have hc : ((84677/100000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99792775947/1000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((84677/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c73 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-29623/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2149323/5000000) (δ := 511/100000000) (ψ := 134393/250000) 84 57
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t73 : ((-8670704699/500000000000 : ℚ) : ℝ) ≤ stT84 73 := by
  have hc : ((-29633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8670704699/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-29633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c74 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-48063/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7155833/10000000) (δ := 193/25000000) (ψ := 134393/250000) 84 57
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t74 : ((-111750076487/1000000000000 : ℚ) : ℝ) ≤ stT84 74 := by
  have hc : ((-96131/100000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111750076487/1000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-96131/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c75 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-661279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -358331/625000) (δ := 37/5000000) (ψ := 134393/250000) 84 58
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t75 : ((-763637257629/10000000000000 : ℚ) : ℝ) ≤ stT84 75 := by
  have hc : ((-661329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-763637257629/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-661329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c76 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((380259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2951799/10000000) (δ := 27/5000000) (ψ := 134393/250000) 84 58
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t76 : ((218064689651/5000000000000 : ℚ) : ℝ) ≤ stT84 76 := by
  have hc : ((380209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218064689651/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((380209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c77 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((199317/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206661/10000000) (δ := 33/5000000) (ψ := 134393/250000) 84 58
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t77 : ((45426250747/400000000000 : ℚ) : ℝ) ≤ stT84 77 := by
  have hc : ((199307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45426250747/400000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((199307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c78 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((269637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1251527/5000000) (δ := 31/5000000) (ψ := 134393/250000) 84 58
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t78 : ((76318866631/1250000000000 : ℚ) : ℝ) ≤ stT84 78 := by
  have hc : ((67403/125000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76318866631/1250000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((67403/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c79 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-479867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5178249/10000000) (δ := 423/100000000) (ψ := 134393/250000) 84 58
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t79 : ((-16873401803/312500000000 : ℚ) : ℝ) ≤ stT84 79 := by
  have hc : ((-479917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16873401803/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-479917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c80 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-499953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7819793/10000000) (δ := 29/5000000) (ψ := 134393/250000) 84 58
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t80 : ((-139748100813/1250000000000 : ℚ) : ℝ) ≤ stT84 80 := by
  have hc : ((-249989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139748100813/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-249989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c81 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-16093/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5279441/10000000) (δ := 217/50000000) (ψ := 134393/250000) 84 59
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t81 : ((-35765723057/625000000000 : ℚ) : ℝ) ≤ stT84 81 := by
  have hc : ((-257513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35765723057/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-257513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c82 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((14699/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2702721/10000000) (δ := 449/100000000) (ψ := 134393/250000) 84 59
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t82 : ((51937922217/1000000000000 : ℚ) : ℝ) ≤ stT84 82 := by
  have hc : ((235159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51937922217/1000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((235159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c83 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((998023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39309/2500000) (δ := 809/100000000) (ψ := 134393/250000) 84 59
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t83 : ((547708539833/5000000000000 : ℚ) : ℝ) ≤ stT84 83 := by
  have hc : ((997973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((547708539833/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((997973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c84 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((587277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589441/2500000) (δ := 889/100000000) (ψ := 134393/250000) 84 59
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t84 : ((640716920203/10000000000000 : ℚ) : ℝ) ≤ stT84 84 := by
  have hc : ((587227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((640716920203/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((587227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c85 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-358261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4843001/10000000) (δ := 237/50000000) (ψ := 134393/250000) 84 59
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t85 : ((-388643101083/10000000000000 : ℚ) : ℝ) ≤ stT84 85 := by
  have hc : ((-358311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388643101083/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-358311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c86 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-243869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7299169/10000000) (δ := 397/50000000) (ψ := 134393/250000) 84 59
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t86 : ((-65746062533/625000000000 : ℚ) : ℝ) ≤ stT84 86 := by
  have hc : ((-487763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65746062533/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-487763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c87 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-146449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2990511/5000000) (δ := 359/50000000) (ψ := 134393/250000) 84 60
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t87 : ((-157020597867/2000000000000 : ℚ) : ℝ) ≤ stT84 87 := by
  have hc : ((-146459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157020597867/2000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-146459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c88 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((137957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -895249/2500000) (δ := 379/50000000) (ψ := 134393/250000) 84 60
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t88 : ((147009275721/10000000000000 : ℚ) : ℝ) ≤ stT84 88 := by
  have hc : ((137907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147009275721/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((137907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c89 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((110687/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1208089/10000000) (δ := 113/20000000) (ψ := 134393/250000) 84 60
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t89 : ((469285051831/5000000000000 : ℚ) : ℝ) ≤ stT84 89 := by
  have hc : ((442723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469285051831/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((442723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c90 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((22453/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8893/78125) (δ := 113/20000000) (ψ := 134393/250000) 84 60
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t90 : ((23666210061/250000000000 : ℚ) : ℝ) ≤ stT84 90 := by
  have hc : ((89807/100000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23666210061/250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((89807/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c91 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((37239/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 345877/1000000) (δ := 177/20000000) (ψ := 134393/250000) 84 60
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t91 : ((9756641259/500000000000 : ℚ) : ℝ) ≤ stT84 91 := by
  have hc : ((37229/200000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9756641259/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((37229/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c92 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-667431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46031/80000) (δ := 129/20000000) (ψ := 134393/250000) 84 60
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t92 : ((-695897668613/10000000000000 : ℚ) : ℝ) ≤ stT84 92 := by
  have hc : ((-667481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-695897668613/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-667481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c93 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-249421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1920949/2500000) (δ := 31/4000000) (ψ := 134393/250000) 84 61
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t93 : ((-64662641673/625000000000 : ℚ) : ℝ) ≤ stT84 93 := by
  have hc : ((-498867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64662641673/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-498867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c94 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-568201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2718893/5000000) (δ := 131/20000000) (ψ := 134393/250000) 84 61
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t94 : ((-293053291461/5000000000000 : ℚ) : ℝ) ≤ stT84 94 := by
  have hc : ((-568251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293053291461/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-568251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c95 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((140377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3215543/10000000) (δ := 147/20000000) (ψ := 134393/250000) 84 61
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t95 : ((1124984877/39062500000 : ℚ) : ℝ) ≤ stT84 95 := by
  have hc : ((4386/15625 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1124984877/39062500000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((4386/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c96 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((45923/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101657/1000000) (δ := 147/20000000) (ψ := 134393/250000) 84 61
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t96 : ((4686738071/50000000000 : ℚ) : ℝ) ≤ stT84 96 := by
  have hc : ((91841/100000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4686738071/50000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((91841/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c97 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((447169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18119/156250) (δ := 131/20000000) (ψ := 134393/250000) 84 61
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t97 : ((28375366989/312500000000 : ℚ) : ℝ) ≤ stT84 97 := by
  have hc : ((55893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28375366989/312500000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((55893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c98 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((60737/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3313481/10000000) (δ := 131/20000000) (ψ := 134393/250000) 84 61
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t98 : ((15335243781/625000000000 : ℚ) : ℝ) ≤ stT84 98 := by
  have hc : ((121449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15335243781/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((121449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c99 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-570731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5445479/10000000) (δ := 107/25000000) (ψ := 134393/250000) 84 61
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t99 : ((-286828297339/5000000000000 : ℚ) : ℝ) ≤ stT84 99 := by
  have hc : ((-570781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286828297339/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-570781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_c100 :
    |Real.cos (((84 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((134393/250000 : ℚ) : ℝ))
      - ((-992907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7556049/10000000) (δ := 139/20000000) (ψ := 134393/250000) 84 61
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st84_t100 : ((-992957/10000000 : ℚ) : ℝ) ≤ stT84 100 := by
  have hc : ((-992957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((84 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((134393/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st84_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-992957/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-992957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st84_p1 : ((107363/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT84 (i+1) := by
  rw [Finset.sum_range_one]
  exact st84_t1

theorem st84_p2 : ((11553577768683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT84 (i+1))
      = (∑ i ∈ Finset.range 1, stT84 (i+1)) + stT84 2 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 1
    simpa using h
  have hprev := st84_p1
  have hstep := st84_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p3 : ((86515744977/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT84 (i+1))
      = (∑ i ∈ Finset.range 2, stT84 (i+1)) + stT84 3 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 2
    simpa using h
  have hprev := st84_p2
  have hstep := st84_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p4 : ((2187203651349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT84 (i+1))
      = (∑ i ∈ Finset.range 3, stT84 (i+1)) + stT84 4 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 3
    simpa using h
  have hprev := st84_p3
  have hstep := st84_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p5 : ((-1871917172643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT84 (i+1))
      = (∑ i ∈ Finset.range 4, stT84 (i+1)) + stT84 5 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 4
    simpa using h
  have hprev := st84_p4
  have hstep := st84_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p6 : ((894401207931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT84 (i+1))
      = (∑ i ∈ Finset.range 5, stT84 (i+1)) + stT84 6 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 5
    simpa using h
  have hprev := st84_p5
  have hstep := st84_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p7 : ((4307483993879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT84 (i+1))
      = (∑ i ∈ Finset.range 6, stT84 (i+1)) + stT84 7 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 6
    simpa using h
  have hprev := st84_p6
  have hstep := st84_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p8 : ((3525833995023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT84 (i+1))
      = (∑ i ∈ Finset.range 7, stT84 (i+1)) + stT84 8 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 7
    simpa using h
  have hprev := st84_p7
  have hstep := st84_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p9 : ((2713517165893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT84 (i+1))
      = (∑ i ∈ Finset.range 8, stT84 (i+1)) + stT84 9 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 8
    simpa using h
  have hprev := st84_p8
  have hstep := st84_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p10 : ((1693514910159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT84 (i+1))
      = (∑ i ∈ Finset.range 9, stT84 (i+1)) + stT84 10 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 9
    simpa using h
  have hprev := st84_p9
  have hstep := st84_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p11 : ((4661742903009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT84 (i+1))
      = (∑ i ∈ Finset.range 10, stT84 (i+1)) + stT84 11 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 10
    simpa using h
  have hprev := st84_p10
  have hstep := st84_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p12 : ((6567951190839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT84 (i+1))
      = (∑ i ∈ Finset.range 11, stT84 (i+1)) + stT84 12 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 11
    simpa using h
  have hprev := st84_p11
  have hstep := st84_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p13 : ((7336745976339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT84 (i+1))
      = (∑ i ∈ Finset.range 12, stT84 (i+1)) + stT84 13 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 12
    simpa using h
  have hprev := st84_p12
  have hstep := st84_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p14 : ((8225472317311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT84 (i+1))
      = (∑ i ∈ Finset.range 13, stT84 (i+1)) + stT84 14 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 13
    simpa using h
  have hprev := st84_p13
  have hstep := st84_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p15 : ((2025025218903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT84 (i+1))
      = (∑ i ∈ Finset.range 14, stT84 (i+1)) + stT84 15 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 14
    simpa using h
  have hprev := st84_p14
  have hstep := st84_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p16 : ((2521524718903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT84 (i+1))
      = (∑ i ∈ Finset.range 15, stT84 (i+1)) + stT84 16 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 15
    simpa using h
  have hprev := st84_p15
  have hstep := st84_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p17 : ((13235943595943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT84 (i+1))
      = (∑ i ∈ Finset.range 16, stT84 (i+1)) + stT84 17 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 16
    simpa using h
  have hprev := st84_p16
  have hstep := st84_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p18 : ((11022529293287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT84 (i+1))
      = (∑ i ∈ Finset.range 17, stT84 (i+1)) + stT84 18 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 17
    simpa using h
  have hprev := st84_p17
  have hstep := st84_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p19 : ((2122212575871/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT84 (i+1))
      = (∑ i ∈ Finset.range 18, stT84 (i+1)) + stT84 19 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 18
    simpa using h
  have hprev := st84_p18
  have hstep := st84_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p20 : ((12791416033983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT84 (i+1))
      = (∑ i ∈ Finset.range 19, stT84 (i+1)) + stT84 20 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 19
    simpa using h
  have hprev := st84_p19
  have hstep := st84_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p21 : ((5585012152149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT84 (i+1))
      = (∑ i ∈ Finset.range 20, stT84 (i+1)) + stT84 21 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 20
    simpa using h
  have hprev := st84_p20
  have hstep := st84_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p22 : ((11322012951321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT84 (i+1))
      = (∑ i ∈ Finset.range 21, stT84 (i+1)) + stT84 22 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 21
    simpa using h
  have hprev := st84_p21
  have hstep := st84_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p23 : ((12359703629217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT84 (i+1))
      = (∑ i ∈ Finset.range 22, stT84 (i+1)) + stT84 23 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 22
    simpa using h
  have hprev := st84_p22
  have hstep := st84_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p24 : ((10694050157217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT84 (i+1))
      = (∑ i ∈ Finset.range 23, stT84 (i+1)) + stT84 24 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 23
    simpa using h
  have hprev := st84_p23
  have hstep := st84_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p25 : ((12586700157217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT84 (i+1))
      = (∑ i ∈ Finset.range 24, stT84 (i+1)) + stT84 25 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 24
    simpa using h
  have hprev := st84_p24
  have hstep := st84_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p26 : ((10655743974341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT84 (i+1))
      = (∑ i ∈ Finset.range 25, stT84 (i+1)) + stT84 26 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 25
    simpa using h
  have hprev := st84_p25
  have hstep := st84_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p27 : ((12559270773341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT84 (i+1))
      = (∑ i ∈ Finset.range 26, stT84 (i+1)) + stT84 27 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 26
    simpa using h
  have hprev := st84_p26
  have hstep := st84_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p28 : ((10720918992569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT84 (i+1))
      = (∑ i ∈ Finset.range 27, stT84 (i+1)) + stT84 28 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 27
    simpa using h
  have hprev := st84_p27
  have hstep := st84_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p29 : ((2482045997927/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT84 (i+1))
      = (∑ i ∈ Finset.range 28, stT84 (i+1)) + stT84 29 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 28
    simpa using h
  have hprev := st84_p28
  have hstep := st84_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p30 : ((11039853604823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT84 (i+1))
      = (∑ i ∈ Finset.range 29, stT84 (i+1)) + stT84 30 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 29
    simpa using h
  have hprev := st84_p29
  have hstep := st84_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p31 : ((2367946598517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT84 (i+1))
      = (∑ i ∈ Finset.range 30, stT84 (i+1)) + stT84 31 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 30
    simpa using h
  have hprev := st84_p30
  have hstep := st84_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p32 : ((11862759912501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT84 (i+1))
      = (∑ i ∈ Finset.range 31, stT84 (i+1)) + stT84 32 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 31
    simpa using h
  have hprev := st84_p31
  have hstep := st84_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p33 : ((10923513237489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT84 (i+1))
      = (∑ i ∈ Finset.range 32, stT84 (i+1)) + stT84 33 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 32
    simpa using h
  have hprev := st84_p32
  have hstep := st84_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p34 : ((6262103246067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT84 (i+1))
      = (∑ i ∈ Finset.range 33, stT84 (i+1)) + stT84 34 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 33
    simpa using h
  have hprev := st84_p33
  have hstep := st84_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p35 : ((2732592547/2500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT84 (i+1))
      = (∑ i ∈ Finset.range 34, stT84 (i+1)) + stT84 35 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 34
    simpa using h
  have hprev := st84_p34
  have hstep := st84_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p36 : ((5832050780587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT84 (i+1))
      = (∑ i ∈ Finset.range 35, stT84 (i+1)) + stT84 36 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 35
    simpa using h
  have hprev := st84_p35
  have hstep := st84_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p37 : ((2456030383031/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT84 (i+1))
      = (∑ i ∈ Finset.range 36, stT84 (i+1)) + stT84 37 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 36
    simpa using h
  have hprev := st84_p36
  have hstep := st84_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p38 : ((428934952953/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT84 (i+1))
      = (∑ i ∈ Finset.range 37, stT84 (i+1)) + stT84 38 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 37
    simpa using h
  have hprev := st84_p37
  have hstep := st84_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p39 : ((11973951866891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT84 (i+1))
      = (∑ i ∈ Finset.range 38, stT84 (i+1)) + stT84 39 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 38
    simpa using h
  have hprev := st84_p38
  have hstep := st84_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p40 : ((12160916691977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT84 (i+1))
      = (∑ i ∈ Finset.range 39, stT84 (i+1)) + stT84 40 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 39
    simpa using h
  have hprev := st84_p39
  have hstep := st84_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p41 : ((10713310505017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT84 (i+1))
      = (∑ i ∈ Finset.range 40, stT84 (i+1)) + stT84 41 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 40
    simpa using h
  have hprev := st84_p40
  have hstep := st84_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p42 : ((2965098380513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT84 (i+1))
      = (∑ i ∈ Finset.range 41, stT84 (i+1)) + stT84 42 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 41
    simpa using h
  have hprev := st84_p41
  have hstep := st84_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p43 : ((12349893882247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT84 (i+1))
      = (∑ i ∈ Finset.range 42, stT84 (i+1)) + stT84 43 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 42
    simpa using h
  have hprev := st84_p42
  have hstep := st84_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p44 : ((5421553621937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT84 (i+1))
      = (∑ i ∈ Finset.range 43, stT84 (i+1)) + stT84 44 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 43
    simpa using h
  have hprev := st84_p43
  have hstep := st84_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p45 : ((11354786341069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT84 (i+1))
      = (∑ i ∈ Finset.range 44, stT84 (i+1)) + stT84 45 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 44
    simpa using h
  have hprev := st84_p44
  have hstep := st84_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p46 : ((3137418666529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT84 (i+1))
      = (∑ i ∈ Finset.range 45, stT84 (i+1)) + stT84 46 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 45
    simpa using h
  have hprev := st84_p45
  have hstep := st84_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p47 : ((44697941761/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT84 (i+1))
      = (∑ i ∈ Finset.range 46, stT84 (i+1)) + stT84 47 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 46
    simpa using h
  have hprev := st84_p46
  have hstep := st84_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p48 : ((671003461227/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT84 (i+1))
      = (∑ i ∈ Finset.range 47, stT84 (i+1)) + stT84 48 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 47
    simpa using h
  have hprev := st84_p47
  have hstep := st84_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p49 : ((12077796405681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT84 (i+1))
      = (∑ i ∈ Finset.range 48, stT84 (i+1)) + stT84 49 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 48
    simpa using h
  have hprev := st84_p48
  have hstep := st84_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p50 : ((12391966652057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT84 (i+1))
      = (∑ i ∈ Finset.range 49, stT84 (i+1)) + stT84 50 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 49
    simpa using h
  have hprev := st84_p49
  have hstep := st84_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p51 : ((5501847931097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT84 (i+1))
      = (∑ i ∈ Finset.range 50, stT84 (i+1)) + stT84 51 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 50
    simpa using h
  have hprev := st84_p50
  have hstep := st84_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p52 : ((10905077064829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT84 (i+1))
      = (∑ i ∈ Finset.range 51, stT84 (i+1)) + stT84 52 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 51
    simpa using h
  have hprev := st84_p51
  have hstep := st84_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p53 : ((6138704366497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT84 (i+1))
      = (∑ i ∈ Finset.range 52, stT84 (i+1)) + stT84 53 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 52
    simpa using h
  have hprev := st84_p52
  have hstep := st84_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p54 : ((12335198973203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT84 (i+1))
      = (∑ i ∈ Finset.range 53, stT84 (i+1)) + stT84 54 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 53
    simpa using h
  have hprev := st84_p53
  have hstep := st84_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p55 : ((10990225257603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT84 (i+1))
      = (∑ i ∈ Finset.range 54, stT84 (i+1)) + stT84 55 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 54
    simpa using h
  have hprev := st84_p54
  have hstep := st84_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p56 : ((5408966929893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT84 (i+1))
      = (∑ i ∈ Finset.range 55, stT84 (i+1)) + stT84 56 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 55
    simpa using h
  have hprev := st84_p55
  have hstep := st84_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p57 : ((6056195518097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT84 (i+1))
      = (∑ i ∈ Finset.range 56, stT84 (i+1)) + stT84 57 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 56
    simpa using h
  have hprev := st84_p56
  have hstep := st84_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p58 : ((6264655589141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT84 (i+1))
      = (∑ i ∈ Finset.range 57, stT84 (i+1)) + stT84 58 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 57
    simpa using h
  have hprev := st84_p57
  have hstep := st84_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p59 : ((1420193223969/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT84 (i+1))
      = (∑ i ∈ Finset.range 58, stT84 (i+1)) + stT84 59 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 58
    simpa using h
  have hprev := st84_p58
  have hstep := st84_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p60 : ((10614497334057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT84 (i+1))
      = (∑ i ∈ Finset.range 59, stT84 (i+1)) + stT84 60 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 59
    simpa using h
  have hprev := st84_p59
  have hstep := st84_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p61 : ((2301412470549/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT84 (i+1))
      = (∑ i ∈ Finset.range 60, stT84 (i+1)) + stT84 61 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 60
    simpa using h
  have hprev := st84_p60
  have hstep := st84_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p62 : ((6289294433233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT84 (i+1))
      = (∑ i ∈ Finset.range 61, stT84 (i+1)) + stT84 62 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 61
    simpa using h
  have hprev := st84_p61
  have hstep := st84_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p63 : ((3039665344173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT84 (i+1))
      = (∑ i ∈ Finset.range 62, stT84 (i+1)) + stT84 63 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 62
    simpa using h
  have hprev := st84_p62
  have hstep := st84_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p64 : ((2182772826171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT84 (i+1))
      = (∑ i ∈ Finset.range 63, stT84 (i+1)) + stT84 64 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 63
    simpa using h
  have hprev := st84_p63
  have hstep := st84_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p65 : ((10695865527767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT84 (i+1))
      = (∑ i ∈ Finset.range 64, stT84 (i+1)) + stT84 65 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 64
    simpa using h
  have hprev := st84_p64
  have hstep := st84_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p66 : ((11796047844569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT84 (i+1))
      = (∑ i ∈ Finset.range 65, stT84 (i+1)) + stT84 66 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 65
    simpa using h
  have hprev := st84_p65
  have hstep := st84_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p67 : ((12648698629519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT84 (i+1))
      = (∑ i ∈ Finset.range 66, stT84 (i+1)) + stT84 67 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 66
    simpa using h
  have hprev := st84_p66
  have hstep := st84_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p68 : ((1209737716307/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT84 (i+1))
      = (∑ i ∈ Finset.range 67, stT84 (i+1)) + stT84 68 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 67
    simpa using h
  have hprev := st84_p67
  have hstep := st84_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p69 : ((2180643049463/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT84 (i+1))
      = (∑ i ∈ Finset.range 68, stT84 (i+1)) + stT84 69 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 68
    simpa using h
  have hprev := st84_p68
  have hstep := st84_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p70 : ((10625159563213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT84 (i+1))
      = (∑ i ∈ Finset.range 69, stT84 (i+1)) + stT84 70 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 69
    simpa using h
  have hprev := st84_p69
  have hstep := st84_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p71 : ((5797548936399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT84 (i+1))
      = (∑ i ∈ Finset.range 70, stT84 (i+1)) + stT84 71 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 70
    simpa using h
  have hprev := st84_p70
  have hstep := st84_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p72 : ((3148256408067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT84 (i+1))
      = (∑ i ∈ Finset.range 71, stT84 (i+1)) + stT84 72 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 71
    simpa using h
  have hprev := st84_p71
  have hstep := st84_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p73 : ((776225721143/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT84 (i+1))
      = (∑ i ∈ Finset.range 72, stT84 (i+1)) + stT84 73 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 72
    simpa using h
  have hprev := st84_p72
  have hstep := st84_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p74 : ((5651055386709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT84 (i+1))
      = (∑ i ∈ Finset.range 73, stT84 (i+1)) + stT84 74 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 73
    simpa using h
  have hprev := st84_p73
  have hstep := st84_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p75 : ((10538473515789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT84 (i+1))
      = (∑ i ∈ Finset.range 74, stT84 (i+1)) + stT84 75 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 74
    simpa using h
  have hprev := st84_p74
  have hstep := st84_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p76 : ((10974602895091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT84 (i+1))
      = (∑ i ∈ Finset.range 75, stT84 (i+1)) + stT84 76 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 75
    simpa using h
  have hprev := st84_p75
  have hstep := st84_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p77 : ((6055129581883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT84 (i+1))
      = (∑ i ∈ Finset.range 76, stT84 (i+1)) + stT84 77 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 76
    simpa using h
  have hprev := st84_p76
  have hstep := st84_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p78 : ((6360405048407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT84 (i+1))
      = (∑ i ∈ Finset.range 77, stT84 (i+1)) + stT84 78 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 77
    simpa using h
  have hprev := st84_p77
  have hstep := st84_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p79 : ((6090430619559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT84 (i+1))
      = (∑ i ∈ Finset.range 78, stT84 (i+1)) + stT84 79 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 78
    simpa using h
  have hprev := st84_p78
  have hstep := st84_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p80 : ((5531438216307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT84 (i+1))
      = (∑ i ∈ Finset.range 79, stT84 (i+1)) + stT84 80 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 79
    simpa using h
  have hprev := st84_p79
  have hstep := st84_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p81 : ((5245312431851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT84 (i+1))
      = (∑ i ∈ Finset.range 80, stT84 (i+1)) + stT84 81 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 80
    simpa using h
  have hprev := st84_p80
  have hstep := st84_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p82 : ((688125255367/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT84 (i+1))
      = (∑ i ∈ Finset.range 81, stT84 (i+1)) + stT84 82 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 81
    simpa using h
  have hprev := st84_p81
  have hstep := st84_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p83 : ((6052710582769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT84 (i+1))
      = (∑ i ∈ Finset.range 82, stT84 (i+1)) + stT84 83 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 82
    simpa using h
  have hprev := st84_p82
  have hstep := st84_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p84 : ((12746138085741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT84 (i+1))
      = (∑ i ∈ Finset.range 83, stT84 (i+1)) + stT84 84 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 83
    simpa using h
  have hprev := st84_p83
  have hstep := st84_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p85 : ((6178747492329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT84 (i+1))
      = (∑ i ∈ Finset.range 84, stT84 (i+1)) + stT84 85 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 84
    simpa using h
  have hprev := st84_p84
  have hstep := st84_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p86 : ((1130555798413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT84 (i+1))
      = (∑ i ∈ Finset.range 85, stT84 (i+1)) + stT84 86 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 85
    simpa using h
  have hprev := st84_p85
  have hstep := st84_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p87 : ((2104090998959/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT84 (i+1))
      = (∑ i ∈ Finset.range 86, stT84 (i+1)) + stT84 87 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 86
    simpa using h
  have hprev := st84_p86
  have hstep := st84_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p88 : ((2666866067629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT84 (i+1))
      = (∑ i ∈ Finset.range 87, stT84 (i+1)) + stT84 88 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 87
    simpa using h
  have hprev := st84_p87
  have hstep := st84_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p89 : ((5803017187089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT84 (i+1))
      = (∑ i ∈ Finset.range 88, stT84 (i+1)) + stT84 89 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 88
    simpa using h
  have hprev := st84_p88
  have hstep := st84_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p90 : ((6276341388309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT84 (i+1))
      = (∑ i ∈ Finset.range 89, stT84 (i+1)) + stT84 90 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 89
    simpa using h
  have hprev := st84_p89
  have hstep := st84_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p91 : ((6373907800899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT84 (i+1))
      = (∑ i ∈ Finset.range 90, stT84 (i+1)) + stT84 91 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 90
    simpa using h
  have hprev := st84_p90
  have hstep := st84_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p92 : ((2410383586637/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT84 (i+1))
      = (∑ i ∈ Finset.range 91, stT84 (i+1)) + stT84 92 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 91
    simpa using h
  have hprev := st84_p91
  have hstep := st84_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p93 : ((11017315666417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT84 (i+1))
      = (∑ i ∈ Finset.range 92, stT84 (i+1)) + stT84 93 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 92
    simpa using h
  have hprev := st84_p92
  have hstep := st84_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p94 : ((2086241816699/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT84 (i+1))
      = (∑ i ∈ Finset.range 93, stT84 (i+1)) + stT84 94 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 93
    simpa using h
  have hprev := st84_p93
  have hstep := st84_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p95 : ((10719205212007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT84 (i+1))
      = (∑ i ∈ Finset.range 94, stT84 (i+1)) + stT84 95 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 94
    simpa using h
  have hprev := st84_p94
  have hstep := st84_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p96 : ((11656552826207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT84 (i+1))
      = (∑ i ∈ Finset.range 95, stT84 (i+1)) + stT84 96 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 95
    simpa using h
  have hprev := st84_p95
  have hstep := st84_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p97 : ((2512912913971/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT84 (i+1))
      = (∑ i ∈ Finset.range 96, stT84 (i+1)) + stT84 97 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 96
    simpa using h
  have hprev := st84_p96
  have hstep := st84_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p98 : ((12809928470351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT84 (i+1))
      = (∑ i ∈ Finset.range 97, stT84 (i+1)) + stT84 98 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 97
    simpa using h
  have hprev := st84_p97
  have hstep := st84_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p99 : ((12236271875673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT84 (i+1))
      = (∑ i ∈ Finset.range 98, stT84 (i+1)) + stT84 99 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 98
    simpa using h
  have hprev := st84_p98
  have hstep := st84_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st84_p100 : ((11243314875673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT84 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT84 (i+1))
      = (∑ i ∈ Finset.range 99, stT84 (i+1)) + stT84 100 := by
    have h := Finset.sum_range_succ (fun i => stT84 (i+1)) 99
    simpa using h
  have hprev := st84_p99
  have hstep := st84_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 84`.** -/
theorem station_84_sign : hardyG (((84:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 84 100 (by norm_num) (by norm_num)
    ((134393/250000 : ℚ) : ℝ)
  have hchain := st84_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT84 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((84:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((134393/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((84:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((84:ℕ)):ℝ)+1) * ((((84:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((440917/560000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((11243314875673/10000000000000 : ℚ) : ℝ) - ((440917/560000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((134393/250000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((84:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((134393/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((84:ℕ)):ℝ))).re
      - Real.sin ((134393/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((84:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((84:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((84:ℕ)):ℝ)
      = ((((84:ℕ)):ℝ) * (Real.log (((84:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((84:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_84
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
  have hθwin : |(((134393/250000 : ℚ) : ℝ) + ((11:ℤ)) * (2*Real.pi) - Real.pi) - theta (((84:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((84:ℕ)):ℝ))
    (φ := ((134393/250000 : ℚ) : ℝ) + ((11:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((134393/250000 : ℚ) : ℝ) + ((11:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((134393/250000 : ℚ)) : ℝ) - Real.pi) + ((11:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((134393/250000 : ℚ)) : ℝ) - Real.pi) 11).1,
    (cos_sin_shift ((((134393/250000 : ℚ)) : ℝ) - Real.pi) 11).2]
  exact cos_sin_flip ((134393/250000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_84_sign
end AxiomAudit
