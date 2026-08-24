import RequestProject.DVPSqrtTable

/-!
# Station `t = 100` of the extended Hardy ladder (rung-109)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT100 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((100 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((7571/1000000 : ℚ) : ℝ))

theorem st100_c1 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((999971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1183/625000) (δ := 21/100000000) (ψ := 7571/1000000) 100 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t1 : ((999921/1000000 : ℚ) : ℝ) ≤ stT100 1 := by
  have hc : ((999921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999921/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((999921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c2 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((245401/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 480271/10000000) (δ := 779/100000000) (ψ := 7571/1000000) 100 11
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t2 : ((3470317049059/5000000000000 : ℚ) : ℝ) ≤ stT100 2 := by
  have hc : ((490777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3470317049059/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((490777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c3 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-497397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7598769/10000000) (δ := 221/25000000) (ψ := 7571/1000000) 100 17
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t3 : ((-1435933704633/2500000000000 : ℚ) : ℝ) ≤ stT100 3 := by
  have hc : ((-248711/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1435933704633/2500000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-248711/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c4 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((231057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97947/1000000) (δ := 577/100000000) (ψ := 7571/1000000) 100 22
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t4 : ((462089/1000000 : ℚ) : ℝ) ≤ stT100 4 := by
  have hc : ((462089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462089/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((462089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c5 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-755097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1213299/2000000) (δ := 903/100000000) (ψ := 7571/1000000) 100 26
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t5 : ((-422140010499/1250000000000 : ℚ) : ℝ) ≤ stT100 5 := by
  have hc : ((-755147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422140010499/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-755147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c6 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-995241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1521999/2000000) (δ := 173/25000000) (ψ := 7571/1000000) 100 29
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t6 : ((-4063258587553/10000000000000 : ℚ) : ℝ) ≤ stT100 6 := by
  have hc : ((-995291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4063258587553/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-995291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c7 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((980989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122063/2500000) (δ := 529/100000000) (ψ := 7571/1000000) 100 31
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t7 : ((926900051429/2500000000000 : ℚ) : ℝ) ≤ stT100 7 := by
  have hc : ((980939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((926900051429/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((980939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c8 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((830123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147867/1000000) (δ := 147/25000000) (ψ := 7571/1000000) 100 33
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t8 : ((2934750483909/10000000000000 : ℚ) : ℝ) ≤ stT100 8 := by
  have hc : ((830073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2934750483909/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((830073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c9 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((980737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245749/5000000) (δ := 757/100000000) (ψ := 7571/1000000) 100 35
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t9 : ((3268956339771/10000000000000 : ℚ) : ℝ) ≤ stT100 9 := by
  have hc : ((980687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3268956339771/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((980687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c10 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-610049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86989/156250) (δ := 449/50000000) (ψ := 7571/1000000) 100 37
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t10 : ((-964651322761/5000000000000 : ℚ) : ℝ) ≤ stT100 10 := by
  have hc : ((-610099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-964651322761/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-610099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c11 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((522587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1276143/5000000) (δ := 709/100000000) (ψ := 7571/1000000) 100 38
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t11 : ((1575508101681/10000000000000 : ℚ) : ℝ) ≤ stT100 11 := by
  have hc : ((522537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1575508101681/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((522537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c12 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-478069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1777699/2500000) (δ := 513/100000000) (ψ := 7571/1000000) 100 40
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t12 : ((-21564668917/78125000000 : ℚ) : ℝ) ≤ stT100 12 := by
  have hc : ((-239047/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21564668917/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-239047/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c13 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((43277/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2808083/10000000) (δ := 541/100000000) (ψ := 7571/1000000) 100 41
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t13 : ((30003723/250000000 : ℚ) : ℝ) ≤ stT100 13 := by
  have hc : ((5409/12500 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30003723/250000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((5409/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c14 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((99999/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10947/10000000) (δ := 731/100000000) (ψ := 7571/1000000) 100 42
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t14 : ((33405645541/125000000000 : ℚ) : ℝ) ≤ stT100 14 := by
  have hc : ((49997/50000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33405645541/125000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((49997/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c15 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((813599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 775601/5000000) (δ := 1001/100000000) (ψ := 7571/1000000) 100 43
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t15 : ((525143438853/2500000000000 : ℚ) : ℝ) ≤ stT100 15 := by
  have hc : ((813549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525143438853/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((813549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c16 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((70303/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1977869/10000000) (δ := 79/10000000) (ψ := 7571/1000000) 100 44
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t16 : ((35149/200000 : ℚ) : ℝ) ≤ stT100 16 := by
  have hc : ((35149/50000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35149/200000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((35149/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c17 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((105209/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1426061/10000000) (δ := 579/100000000) (ψ := 7571/1000000) 100 45
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t17 : ((255154120929/1250000000000 : ℚ) : ℝ) ≤ stT100 17 := by
  have hc : ((420811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255154120929/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((420811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c18 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((199999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7701/10000000) (δ := 111/20000000) (ψ := 7571/1000000) 100 46
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t18 : ((235689236379/1000000000000 : ℚ) : ℝ) ≤ stT100 18 := by
  have hc : ((199989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235689236379/1000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((199989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c19 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((642237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2183457/10000000) (δ := 153/20000000) (ψ := 7571/1000000) 100 47
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t19 : ((1473277801359/10000000000000 : ℚ) : ℝ) ≤ stT100 19 := by
  have hc : ((642187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1473277801359/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((642187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c20 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-440757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79189/156250) (δ := 23/3125000) (ψ := 7571/1000000) 100 48
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t20 : ((-246418606719/2500000000000 : ℚ) : ℝ) ≤ stT100 20 := by
  have hc : ((-440807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246418606719/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-440807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c21 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-958297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1425889/2000000) (δ := 627/100000000) (ψ := 7571/1000000) 100 48
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t21 : ((-2091284698113/10000000000000 : ℚ) : ℝ) ≤ stT100 21 := by
  have hc : ((-958347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2091284698113/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-958347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c22 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((21443/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 610297/2000000) (δ := 507/100000000) (ψ := 7571/1000000) 100 49
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t22 : ((365679708633/5000000000000 : ℚ) : ℝ) ≤ stT100 22 := by
  have hc : ((171519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365679708633/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((171519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c23 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((407689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1543537/10000000) (δ := 423/50000000) (ψ := 7571/1000000) 100 50
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t23 : ((6640922997/39062500000 : ℚ) : ℝ) ≤ stT100 23 := by
  have hc : ((25479/31250 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6640922997/39062500000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((25479/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c24 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-879039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6611597/10000000) (δ := 143/20000000) (ψ := 7571/1000000) 100 51
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t24 : ((-897216694269/5000000000000 : ℚ) : ℝ) ≤ stT100 24 := by
  have hc : ((-879089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-897216694269/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-879089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c25 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((66421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1796951/5000000) (δ := 151/20000000) (ψ := 7571/1000000) 100 51
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t25 : ((16599/625000 : ℚ) : ℝ) ≤ stT100 25 := by
  have hc : ((16599/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16599/625000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((16599/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c26 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((602989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2308883/10000000) (δ := 39/6250000) (ψ := 7571/1000000) 100 52
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t26 : ((1182460452179/10000000000000 : ℚ) : ℝ) ≤ stT100 26 := by
  have hc : ((602939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1182460452179/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((602939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c27 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-38317/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7126199/10000000) (δ := 659/100000000) (ψ := 7571/1000000) 100 52
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t27 : ((-73744953819/400000000000 : ℚ) : ℝ) ≤ stT100 27 := by
  have hc : ((-38319/40000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73744953819/400000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-38319/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c28 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((244813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255073/5000000) (δ := 933/100000000) (ψ := 7571/1000000) 100 53
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t28 : ((462629370511/2500000000000 : ℚ) : ℝ) ≤ stT100 28 := by
  have hc : ((489601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462629370511/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((489601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c29 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-420519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6424987/10000000) (δ := 723/100000000) (ψ := 7571/1000000) 100 54
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t29 : ((-6101022367/39062500000 : ℚ) : ℝ) ≤ stT100 29 := by
  have hc : ((-13142/15625 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6101022367/39062500000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-13142/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c30 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((85263/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2050401/10000000) (δ := 1/125000) (ψ := 7571/1000000) 100 54
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t30 : ((622626976007/5000000000000 : ℚ) : ℝ) ≤ stT100 30 := by
  have hc : ((341027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((622626976007/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((341027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c31 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-23021/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5460107/10000000) (δ := 31/3125000) (ψ := 7571/1000000) 100 55
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t31 : ((-20675275621/200000000000 : ℚ) : ℝ) ≤ stT100 31 := by
  have hc : ((-23023/40000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20675275621/200000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-23023/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c32 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((273999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 619267/2500000) (δ := 31/3125000) (ψ := 7571/1000000) 100 55
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t32 : ((121080480521/1250000000000 : ℚ) : ℝ) ≤ stT100 32 := by
  have hc : ((136987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121080480521/1250000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((136987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c33 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-150179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5537981/10000000) (δ := 291/50000000) (ψ := 7571/1000000) 100 56
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t33 : ((-522899817591/5000000000000 : ℚ) : ℝ) ≤ stT100 33 := by
  have hc : ((-300383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522899817591/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-300383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c34 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((358919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96263/500000) (δ := 781/100000000) (ψ := 7571/1000000) 100 56
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t34 : ((61549782659/500000000000 : ℚ) : ℝ) ≤ stT100 34 := by
  have hc : ((179447/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61549782659/500000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((179447/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c35 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-432093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6535819/10000000) (δ := 37/6250000) (ψ := 7571/1000000) 100 57
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t35 : ((-365206472231/2500000000000 : ℚ) : ℝ) ≤ stT100 35 := by
  have hc : ((-216059/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365206472231/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-216059/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c36 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((195903/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5069/100000) (δ := 651/100000000) (ψ := 7571/1000000) 100 57
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t36 : ((163244101369/1000000000000 : ℚ) : ℝ) ≤ stT100 36 := by
  have hc : ((195893/200000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163244101369/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((195893/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c37 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-490139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1839161/2500000) (δ := 891/100000000) (ψ := 7571/1000000) 100 57
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t37 : ((-20145617859/125000000000 : ℚ) : ℝ) ≤ stT100 37 := by
  have hc : ((-122541/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20145617859/125000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-122541/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c38 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((781517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -842129/5000000) (δ := 563/100000000) (ψ := 7571/1000000) 100 58
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t38 : ((633853353969/5000000000000 : ℚ) : ℝ) ≤ stT100 38 := by
  have hc : ((781467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633853353969/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((781467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c39 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-345761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2404807/5000000) (δ := 7/1250000) (ψ := 7571/1000000) 100 58
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t39 : ((-276870464851/5000000000000 : ℚ) : ℝ) ≤ stT100 39 := by
  have hc : ((-345811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276870464851/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-345811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c40 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-5079/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4568897/10000000) (δ := 267/50000000) (ψ := 7571/1000000) 100 59
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t40 : ((-200804653/5000000000 : ℚ) : ℝ) ≤ stT100 40 := by
  have hc : ((-127/500 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200804653/5000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-127/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c41 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((400539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50133/312500) (δ := 327/50000000) (ψ := 7571/1000000) 100 59
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t41 : ((312748766409/2500000000000 : ℚ) : ℝ) ≤ stT100 41 := by
  have hc : ((200257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312748766409/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((200257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c42 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-995941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1907161/2500000) (δ := 829/100000000) (ψ := 7571/1000000) 100 59
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t42 : ((-768423988347/5000000000000 : ℚ) : ℝ) ≤ stT100 42 := by
  have hc : ((-995991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-768423988347/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-995991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c43 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((63817/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -439339/2000000) (δ := 429/50000000) (ψ := 7571/1000000) 100 60
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t43 : ((4865617141/50000000000 : ℚ) : ℝ) ≤ stT100 43 := by
  have hc : ((15953/25000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4865617141/50000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((15953/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c44 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((29991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 887671/2500000) (δ := 349/50000000) (ψ := 7571/1000000) 100 60
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t44 : ((11299509109/500000000000 : ℚ) : ℝ) ≤ stT100 44 := by
  have hc : ((29981/200000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11299509109/500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((29981/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c45 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-864839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1307813/2000000) (δ := 7/800000) (ψ := 7571/1000000) 100 61
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t45 : ((-161162551371/1250000000000 : ℚ) : ℝ) ≤ stT100 45 := by
  have hc : ((-864889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161162551371/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-864889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c46 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((91401/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -522169/5000000) (δ := 191/20000000) (ψ := 7571/1000000) 100 61
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t46 : ((33688999731/250000000000 : ℚ) : ℝ) ≤ stT100 46 := by
  have hc : ((22849/25000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33688999731/250000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((22849/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c47 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-8069/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4332213/10000000) (δ := 63/6250000) (ψ := 7571/1000000) 100 61
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t47 : ((-470939739/20000000000 : ℚ) : ℝ) ≤ stT100 47 := by
  have hc : ((-16143/100000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470939739/20000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-16143/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c48 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-767007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3056199/5000000) (δ := 917/100000000) (ψ := 7571/1000000) 100 62
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t48 : ((-69196979027/625000000000 : ℚ) : ℝ) ≤ stT100 48 := by
  have hc : ((-767057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69196979027/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-767057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c49 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((57971/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119697/1250000) (δ := 483/50000000) (ψ := 7571/1000000) 100 62
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t49 : ((662489801253/5000000000000 : ℚ) : ℝ) ≤ stT100 49 := by
  have hc : ((463743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((662489801253/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((463743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c50 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-13279/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4093101/10000000) (δ := 957/100000000) (ψ := 7571/1000000) 100 62
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t50 : ((-9396744923/1000000000000 : ℚ) : ℝ) ≤ stT100 50 := by
  have hc : ((-13289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9396744923/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-13289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c51 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-222219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3332103/5000000) (δ := 353/50000000) (ψ := 7571/1000000) 100 63
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t51 : ((-622373094103/5000000000000 : ℚ) : ℝ) ≤ stT100 51 := by
  have hc : ((-444463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-622373094103/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-444463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c52 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((374623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452421/2500000) (δ := 413/50000000) (ψ := 7571/1000000) 100 63
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t52 : ((1038947553/10000000000 : ℚ) : ℝ) ≤ stT100 52 := by
  have hc : ((187299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1038947553/10000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((187299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c53 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((7601/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 590473/2000000) (δ := 433/50000000) (ψ := 7571/1000000) 100 63
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t53 : ((5219699/100000000 : ℚ) : ℝ) ≤ stT100 53 := by
  have hc : ((19/50 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5219699/100000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((19/50 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c54 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-995823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3812699/5000000) (δ := 273/50000000) (ψ := 7571/1000000) 100 63
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t54 : ((-338802965711/2500000000000 : ℚ) : ℝ) ≤ stT100 54 := by
  have hc : ((-995873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338802965711/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-995873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c55 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((171827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3495281/10000000) (δ := 827/100000000) (ψ := 7571/1000000) 100 64
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t55 : ((231623935023/10000000000000 : ℚ) : ℝ) ≤ stT100 55 := by
  have hc : ((171777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231623935023/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((171777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c56 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((919599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504673/5000000) (δ := 907/100000000) (ψ := 7571/1000000) 100 64
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t56 : ((614399422997/5000000000000 : ℚ) : ℝ) ≤ stT100 56 := by
  have hc : ((919549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614399422997/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((919549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c57 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-567033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8491/15625) (δ := 667/100000000) (ψ := 7571/1000000) 100 64
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t57 : ((-751120147239/10000000000000 : ℚ) : ℝ) ≤ stT100 57 := by
  have hc : ((-567083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751120147239/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-567083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c58 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-717021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481447/2500000) (δ := 37/4000000) (ψ := 7571/1000000) 100 65
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t58 : ((-188312166523/2000000000000 : ℚ) : ℝ) ≤ stT100 58 := by
  have hc : ((-717071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188312166523/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-717071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c59 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((394729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1652179/10000000) (δ := 113/20000000) (ψ := 7571/1000000) 100 65
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t59 : ((32116299741/312500000000 : ℚ) : ℝ) ≤ stT100 59 := by
  have hc : ((24669/31250 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32116299741/312500000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((24669/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c60 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((261751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3187/12500) (δ := 299/50000000) (ψ := 7571/1000000) 100 65
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t60 : ((84471673911/1250000000000 : ℚ) : ℝ) ≤ stT100 60 := by
  have hc : ((130863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84471673911/1250000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((130863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c61 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-892101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3340963/5000000) (δ := 319/50000000) (ψ := 7571/1000000) 100 65
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t61 : ((-1142282483719/10000000000000 : ℚ) : ℝ) ≤ stT100 61 := by
  have hc : ((-892151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1142282483719/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-892151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c62 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-200939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4960907/10000000) (δ := 849/100000000) (ψ := 7571/1000000) 100 66
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t62 : ((-31903085241/625000000000 : ℚ) : ℝ) ≤ stT100 62 := by
  have hc : ((-50241/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31903085241/625000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-50241/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c63 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((18541/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -480411/5000000) (δ := 377/50000000) (ψ := 7571/1000000) 100 66
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t63 : ((1167909687/10000000000 : ℚ) : ℝ) ≤ stT100 63 := by
  have hc : ((927/1000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1167909687/10000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((927/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c64 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((371189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2976267/10000000) (δ := 809/100000000) (ψ := 7571/1000000) 100 66
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t64 : ((371139/8000000 : ℚ) : ℝ) ≤ stT100 64 := by
  have hc : ((371139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371139/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((371139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c65 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-920801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3426157/5000000) (δ := 689/100000000) (ψ := 7571/1000000) 100 66
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t65 : ((-285543924037/2500000000000 : ℚ) : ℝ) ≤ stT100 65 := by
  have hc : ((-920851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285543924037/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-920851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c66 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-215101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5038781/10000000) (δ := 583/100000000) (ψ := 7571/1000000) 100 67
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t66 : ((-26480182029/500000000000 : ℚ) : ℝ) ≤ stT100 66 := by
  have hc : ((-107563/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26480182029/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-107563/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c67 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((871901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79957/625000) (δ := 823/100000000) (ψ := 7571/1000000) 100 67
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t67 : ((532567567797/5000000000000 : ℚ) : ℝ) ≤ stT100 67 := by
  have hc : ((871851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((532567567797/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((871851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c68 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((282739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2424459/10000000) (δ := 983/100000000) (ψ := 7571/1000000) 100 67
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t68 : ((85710262023/1250000000000 : ℚ) : ℝ) ≤ stT100 68 := by
  have hc : ((141357/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85710262023/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((141357/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c69 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-757103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6074159/10000000) (δ := 983/100000000) (ψ := 7571/1000000) 100 67
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t69 : ((-911505453427/10000000000000 : ℚ) : ℝ) ≤ stT100 69 := by
  have hc : ((-757153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-911505453427/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-757153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c70 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-93401/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301831/500000) (δ := 613/100000000) (ψ := 7571/1000000) 100 68
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t70 : ((-446572216041/5000000000000 : ℚ) : ℝ) ≤ stT100 70 := by
  have hc : ((-373629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-446572216041/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-373629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c71 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((543509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2490461/10000000) (δ := 3/400000) (ψ := 7571/1000000) 100 68
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t71 : ((644966815479/10000000000000 : ℚ) : ℝ) ≤ stT100 71 := by
  have hc : ((543459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((644966815479/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((543459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c72 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((230027/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10061/100000) (δ := 813/100000000) (ψ := 7571/1000000) 100 68
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t72 : ((542149236819/5000000000000 : ℚ) : ℝ) ≤ stT100 72 := by
  have hc : ((460029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((542149236819/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((460029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c73 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-104707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445443/1000000) (δ := 613/100000000) (ψ := 7571/1000000) 100 68
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t73 : ((-7661224349/312500000000 : ℚ) : ℝ) ≤ stT100 73 := by
  have hc : ((-26183/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7661224349/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-26183/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c74 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196303/250000) (δ := 921/100000000) (ψ := 7571/1000000) 100 69
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t74 : ((-23250702477/200000000000 : ℚ) : ℝ) ≤ stT100 74 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23250702477/200000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c75 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-112893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -899273/2000000) (δ := 441/50000000) (ψ := 7571/1000000) 100 69
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t75 : ((-65193263759/2500000000000 : ℚ) : ℝ) ≤ stT100 75 := by
  have hc : ((-56459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65193263759/2500000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-56459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c76 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((889739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -592529/5000000) (δ := 301/50000000) (ψ := 7571/1000000) 100 69
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t76 : ((510271339371/5000000000000 : ℚ) : ℝ) ≤ stT100 76 := by
  have hc : ((889689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((510271339371/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((889689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c77 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((336261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1041481/5000000) (δ := 401/50000000) (ψ := 7571/1000000) 100 69
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t77 : ((19158811339/250000000000 : ℚ) : ℝ) ≤ stT100 77 := by
  have hc : ((84059/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19158811339/250000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((84059/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c78 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-131253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5308813/10000000) (δ := 381/50000000) (ψ := 7571/1000000) 100 69
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t78 : ((-148629037809/2500000000000 : ℚ) : ℝ) ≤ stT100 78 := by
  have hc : ((-262531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148629037809/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-262531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c79 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-241863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3607197/5000000) (δ := 511/100000000) (ψ := 7571/1000000) 100 70
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t79 : ((-17008201409/156250000000 : ℚ) : ℝ) ≤ stT100 79 := by
  have hc : ((-483751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17008201409/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-483751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c80 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-14263/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2034849/5000000) (δ := 671/100000000) (ψ := 7571/1000000) 100 70
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t80 : ((-15960494367/2500000000000 : ℚ) : ℝ) ≤ stT100 80 := by
  have hc : ((-28551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15960494367/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-28551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c81 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((926563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241017/2500000) (δ := 133/25000000) (ψ := 7571/1000000) 100 70
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t81 : ((1029458785943/10000000000000 : ℚ) : ℝ) ≤ stT100 81 := by
  have hc : ((926513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1029458785943/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((926513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c82 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((666433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420691/2000000) (δ := 551/100000000) (ψ := 7571/1000000) 100 70
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t82 : ((147179348529/2000000000000 : ℚ) : ℝ) ≤ stT100 82 := by
  have hc : ((666383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147179348529/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((666383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c83 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-7253/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1026759/2000000) (δ := 951/100000000) (ψ := 7571/1000000) 100 70
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t83 : ((-254785990803/5000000000000 : ℚ) : ℝ) ≤ stT100 83 := by
  have hc : ((-232121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254785990803/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-232121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c84 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-497003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189503/250000) (δ := 1021/100000000) (ψ := 7571/1000000) 100 71
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t84 : ((-13557557013/125000000000 : ℚ) : ℝ) ≤ stT100 84 := by
  have hc : ((-124257/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13557557013/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-124257/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c85 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-137123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2310753/5000000) (δ := 271/50000000) (ψ := 7571/1000000) 100 71
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t85 : ((-37189497411/1250000000000 : ℚ) : ℝ) ≤ stT100 85 := by
  have hc : ((-34287/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37189497411/1250000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-34287/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c86 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((389101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212187/1250000) (δ := 471/50000000) (ψ := 7571/1000000) 100 71
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t86 : ((104887788963/1250000000000 : ℚ) : ℝ) ≤ stT100 86 := by
  have hc : ((97269/125000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104887788963/1250000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((97269/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c87 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((444169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119271/1000000) (δ := 821/100000000) (ψ := 7571/1000000) 100 71
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t87 : ((1860047313/19531250000 : ℚ) : ℝ) ≤ stT100 87 := by
  have hc : ((27759/31250 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1860047313/19531250000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((27759/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c88 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-49137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1012471/2500000) (δ := 861/100000000) (ψ := 7571/1000000) 100 71
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t88 : ((-13108384687/2500000000000 : ℚ) : ℝ) ≤ stT100 88 := by
  have hc : ((-49187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13108384687/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-49187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c89 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-231067/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1718693/2500000) (δ := 331/50000000) (ψ := 7571/1000000) 100 71
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t89 : ((-244943807841/2500000000000 : ℚ) : ℝ) ≤ stT100 89 := by
  have hc : ((-462159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244943807841/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-462159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c90 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-748071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3019933/5000000) (δ := 673/100000000) (ψ := 7571/1000000) 100 72
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t90 : ((-788589109253/10000000000000 : ℚ) : ℝ) ≤ stT100 90 := by
  have hc : ((-748121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-788589109253/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-748121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c91 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((6423/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3277407/10000000) (δ := 1033/100000000) (ψ := 7571/1000000) 100 72
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t91 : ((6731817777/250000000000 : ℚ) : ℝ) ≤ stT100 91 := by
  have hc : ((25687/100000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6731817777/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((25687/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c92 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((3051/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -545139/10000000) (δ := 753/100000000) (ψ := 7571/1000000) 100 72
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t92 : ((25445794161/250000000000 : ℚ) : ℝ) ≤ stT100 92 := by
  have hc : ((97627/100000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25445794161/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((97627/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c93 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((325067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 215759/1000000) (δ := 913/100000000) (ψ := 7571/1000000) 100 72
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t93 : ((168526313471/2500000000000 : ℚ) : ℝ) ≤ stT100 93 := by
  have hc : ((162521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168526313471/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((162521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c94 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-353929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1207853/2500000) (δ := 793/100000000) (ψ := 7571/1000000) 100 72
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t94 : ((-182550864069/5000000000000 : ℚ) : ℝ) ≤ stT100 94 := by
  have hc : ((-353979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182550864069/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-353979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c95 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-988649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373847/500000) (δ := 913/100000000) (ψ := 7571/1000000) 100 72
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t95 : ((-1014384411321/10000000000000 : ℚ) : ℝ) ≤ stT100 95 := by
  have hc : ((-988699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1014384411321/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-988699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c96 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-312247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5613199/10000000) (δ := 221/25000000) (ψ := 7571/1000000) 100 73
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t96 : ((-19919460057/312500000000 : ℚ) : ℝ) ≤ stT100 96 := by
  have hc : ((-19517/31250 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19919460057/312500000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-19517/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c97 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((176977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1511251/5000000) (δ := 191/25000000) (ψ := 7571/1000000) 100 73
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t97 : ((11229219087/312500000000 : ℚ) : ℝ) ≤ stT100 97 := by
  have hc : ((22119/62500 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11229219087/312500000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((22119/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c98 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((491619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -458377/10000000) (δ := 191/25000000) (ψ := 7571/1000000) 100 73
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t98 : ((31036541393/312500000000 : ℚ) : ℝ) ≤ stT100 98 := by
  have hc : ((245797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31036541393/312500000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((245797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c99 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((673483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519929/2500000) (δ := 519/100000000) (ψ := 7571/1000000) 100 73
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t99 : ((676825082021/10000000000000 : ℚ) : ℝ) ≤ stT100 99 := by
  have hc : ((673433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((676825082021/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((673433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_c100 :
    |Real.cos (((100 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((7571/1000000 : ℚ) : ℝ))
      - ((-131497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45923/100000) (δ := 211/25000000) (ψ := 7571/1000000) 100 73
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st100_t100 : ((-65761/2500000 : ℚ) : ℝ) ≤ stT100 100 := by
  have hc : ((-65761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((100 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((7571/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st100_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65761/2500000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-65761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st100_p1 : ((999921/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT100 (i+1) := by
  rw [Finset.sum_range_one]
  exact st100_t1

theorem st100_p2 : ((8469922049059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT100 (i+1))
      = (∑ i ∈ Finset.range 1, stT100 (i+1)) + stT100 2 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 1
    simpa using h
  have hprev := st100_p1
  have hstep := st100_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p3 : ((5598054639793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT100 (i+1))
      = (∑ i ∈ Finset.range 2, stT100 (i+1)) + stT100 3 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 2
    simpa using h
  have hprev := st100_p2
  have hstep := st100_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p4 : ((7908499639793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT100 (i+1))
      = (∑ i ∈ Finset.range 3, stT100 (i+1)) + stT100 4 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 3
    simpa using h
  have hprev := st100_p3
  have hstep := st100_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p5 : ((6219939597797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT100 (i+1))
      = (∑ i ∈ Finset.range 4, stT100 (i+1)) + stT100 5 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 4
    simpa using h
  have hprev := st100_p4
  have hstep := st100_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p6 : ((8376620608041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT100 (i+1))
      = (∑ i ∈ Finset.range 5, stT100 (i+1)) + stT100 6 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 5
    simpa using h
  have hprev := st100_p5
  have hstep := st100_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p7 : ((12084220813757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT100 (i+1))
      = (∑ i ∈ Finset.range 6, stT100 (i+1)) + stT100 7 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 6
    simpa using h
  have hprev := st100_p6
  have hstep := st100_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p8 : ((7509485648833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT100 (i+1))
      = (∑ i ∈ Finset.range 7, stT100 (i+1)) + stT100 8 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 7
    simpa using h
  have hprev := st100_p7
  have hstep := st100_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p9 : ((18287927637437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT100 (i+1))
      = (∑ i ∈ Finset.range 8, stT100 (i+1)) + stT100 9 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 8
    simpa using h
  have hprev := st100_p8
  have hstep := st100_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p10 : ((3271724998383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT100 (i+1))
      = (∑ i ∈ Finset.range 9, stT100 (i+1)) + stT100 10 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 9
    simpa using h
  have hprev := st100_p9
  have hstep := st100_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p11 : ((4483533273399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT100 (i+1))
      = (∑ i ∈ Finset.range 10, stT100 (i+1)) + stT100 11 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 10
    simpa using h
  have hprev := st100_p10
  have hstep := st100_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p12 : ((758692773611/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT100 (i+1))
      = (∑ i ∈ Finset.range 11, stT100 (i+1)) + stT100 12 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 11
    simpa using h
  have hprev := st100_p11
  have hstep := st100_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p13 : ((818700219611/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT100 (i+1))
      = (∑ i ∈ Finset.range 12, stT100 (i+1)) + stT100 13 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 12
    simpa using h
  have hprev := st100_p12
  have hstep := st100_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p14 : ((38092912071/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT100 (i+1))
      = (∑ i ∈ Finset.range 13, stT100 (i+1)) + stT100 14 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 13
    simpa using h
  have hprev := st100_p13
  have hstep := st100_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p15 : ((330422340483/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT100 (i+1))
      = (∑ i ∈ Finset.range 14, stT100 (i+1)) + stT100 15 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 14
    simpa using h
  have hprev := st100_p14
  have hstep := st100_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p16 : ((357882496733/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT100 (i+1))
      = (∑ i ∈ Finset.range 15, stT100 (i+1)) + stT100 16 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 15
    simpa using h
  have hprev := st100_p15
  have hstep := st100_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p17 : ((3118214094793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT100 (i+1))
      = (∑ i ∈ Finset.range 16, stT100 (i+1)) + stT100 17 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 16
    simpa using h
  have hprev := st100_p16
  have hstep := st100_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p18 : ((13651302561067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT100 (i+1))
      = (∑ i ∈ Finset.range 17, stT100 (i+1)) + stT100 18 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 17
    simpa using h
  have hprev := st100_p17
  have hstep := st100_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p19 : ((28775882923493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT100 (i+1))
      = (∑ i ∈ Finset.range 18, stT100 (i+1)) + stT100 19 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 18
    simpa using h
  have hprev := st100_p18
  have hstep := st100_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p20 : ((27790208496617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT100 (i+1))
      = (∑ i ∈ Finset.range 19, stT100 (i+1)) + stT100 20 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 19
    simpa using h
  have hprev := st100_p19
  have hstep := st100_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p21 : ((3212365474813/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT100 (i+1))
      = (∑ i ∈ Finset.range 20, stT100 (i+1)) + stT100 21 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 20
    simpa using h
  have hprev := st100_p20
  have hstep := st100_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p22 : ((2643028321577/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT100 (i+1))
      = (∑ i ∈ Finset.range 21, stT100 (i+1)) + stT100 22 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 21
    simpa using h
  have hprev := st100_p21
  have hstep := st100_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p23 : ((14065179751501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT100 (i+1))
      = (∑ i ∈ Finset.range 22, stT100 (i+1)) + stT100 23 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 22
    simpa using h
  have hprev := st100_p22
  have hstep := st100_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p24 : ((822997691077/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT100 (i+1))
      = (∑ i ∈ Finset.range 23, stT100 (i+1)) + stT100 24 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 23
    simpa using h
  have hprev := st100_p23
  have hstep := st100_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p25 : ((831297191077/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT100 (i+1))
      = (∑ i ∈ Finset.range 24, stT100 (i+1)) + stT100 25 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 24
    simpa using h
  have hprev := st100_p24
  have hstep := st100_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p26 : ((27783970566643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT100 (i+1))
      = (∑ i ∈ Finset.range 25, stT100 (i+1)) + stT100 26 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 25
    simpa using h
  have hprev := st100_p25
  have hstep := st100_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p27 : ((1621271670073/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT100 (i+1))
      = (∑ i ∈ Finset.range 26, stT100 (i+1)) + stT100 27 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 26
    simpa using h
  have hprev := st100_p26
  have hstep := st100_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p28 : ((6947716050803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT100 (i+1))
      = (∑ i ∈ Finset.range 27, stT100 (i+1)) + stT100 28 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 27
    simpa using h
  have hprev := st100_p27
  have hstep := st100_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p29 : ((1311450123863/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT100 (i+1))
      = (∑ i ∈ Finset.range 28, stT100 (i+1)) + stT100 29 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 28
    simpa using h
  have hprev := st100_p28
  have hstep := st100_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p30 : ((13737128214637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT100 (i+1))
      = (∑ i ∈ Finset.range 29, stT100 (i+1)) + stT100 30 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 29
    simpa using h
  have hprev := st100_p29
  have hstep := st100_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p31 : ((826265395257/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT100 (i+1))
      = (∑ i ∈ Finset.range 30, stT100 (i+1)) + stT100 31 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 30
    simpa using h
  have hprev := st100_p30
  have hstep := st100_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p32 : ((3426142061549/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT100 (i+1))
      = (∑ i ∈ Finset.range 31, stT100 (i+1)) + stT100 32 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 31
    simpa using h
  have hprev := st100_p31
  have hstep := st100_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p33 : ((2636333685721/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT100 (i+1))
      = (∑ i ∈ Finset.range 32, stT100 (i+1)) + stT100 33 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 32
    simpa using h
  have hprev := st100_p32
  have hstep := st100_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p34 : ((2759433251039/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT100 (i+1))
      = (∑ i ∈ Finset.range 33, stT100 (i+1)) + stT100 34 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 33
    simpa using h
  have hprev := st100_p33
  have hstep := st100_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p35 : ((13066753310733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT100 (i+1))
      = (∑ i ∈ Finset.range 34, stT100 (i+1)) + stT100 35 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 34
    simpa using h
  have hprev := st100_p34
  have hstep := st100_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p36 : ((6941486908789/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT100 (i+1))
      = (∑ i ∈ Finset.range 35, stT100 (i+1)) + stT100 36 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 35
    simpa using h
  have hprev := st100_p35
  have hstep := st100_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p37 : ((6538574551609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT100 (i+1))
      = (∑ i ∈ Finset.range 36, stT100 (i+1)) + stT100 37 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 36
    simpa using h
  have hprev := st100_p36
  have hstep := st100_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p38 : ((13711002457187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT100 (i+1))
      = (∑ i ∈ Finset.range 37, stT100 (i+1)) + stT100 38 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 37
    simpa using h
  have hprev := st100_p37
  have hstep := st100_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p39 : ((839633249521/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT100 (i+1))
      = (∑ i ∈ Finset.range 38, stT100 (i+1)) + stT100 39 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 38
    simpa using h
  have hprev := st100_p38
  have hstep := st100_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p40 : ((1654165917417/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT100 (i+1))
      = (∑ i ∈ Finset.range 39, stT100 (i+1)) + stT100 40 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 39
    simpa using h
  have hprev := st100_p39
  have hstep := st100_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p41 : ((6929412436077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT100 (i+1))
      = (∑ i ∈ Finset.range 40, stT100 (i+1)) + stT100 41 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 40
    simpa using h
  have hprev := st100_p40
  have hstep := st100_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p42 : ((13090400883807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT100 (i+1))
      = (∑ i ∈ Finset.range 41, stT100 (i+1)) + stT100 42 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 41
    simpa using h
  have hprev := st100_p41
  have hstep := st100_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p43 : ((13576962597907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT100 (i+1))
      = (∑ i ∈ Finset.range 42, stT100 (i+1)) + stT100 43 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 42
    simpa using h
  have hprev := st100_p42
  have hstep := st100_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p44 : ((13689957688997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT100 (i+1))
      = (∑ i ∈ Finset.range 43, stT100 (i+1)) + stT100 44 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 43
    simpa using h
  have hprev := st100_p43
  have hstep := st100_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p45 : ((13045307483513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT100 (i+1))
      = (∑ i ∈ Finset.range 44, stT100 (i+1)) + stT100 45 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 44
    simpa using h
  have hprev := st100_p44
  have hstep := st100_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p46 : ((13719087478133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT100 (i+1))
      = (∑ i ∈ Finset.range 45, stT100 (i+1)) + stT100 46 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 45
    simpa using h
  have hprev := st100_p45
  have hstep := st100_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p47 : ((13601352543383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT100 (i+1))
      = (∑ i ∈ Finset.range 46, stT100 (i+1)) + stT100 47 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 46
    simpa using h
  have hprev := st100_p46
  have hstep := st100_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p48 : ((13047776711167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT100 (i+1))
      = (∑ i ∈ Finset.range 47, stT100 (i+1)) + stT100 48 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 47
    simpa using h
  have hprev := st100_p47
  have hstep := st100_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p49 : ((685513325621/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT100 (i+1))
      = (∑ i ∈ Finset.range 48, stT100 (i+1)) + stT100 49 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 48
    simpa using h
  have hprev := st100_p48
  have hstep := st100_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p50 : ((2732656557561/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT100 (i+1))
      = (∑ i ∈ Finset.range 49, stT100 (i+1)) + stT100 50 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 49
    simpa using h
  have hprev := st100_p49
  have hstep := st100_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p51 : ((6520454846851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT100 (i+1))
      = (∑ i ∈ Finset.range 50, stT100 (i+1)) + stT100 51 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 50
    simpa using h
  have hprev := st100_p50
  have hstep := st100_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p52 : ((6780191735101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT100 (i+1))
      = (∑ i ∈ Finset.range 51, stT100 (i+1)) + stT100 52 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 51
    simpa using h
  have hprev := st100_p51
  have hstep := st100_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p53 : ((6910684210101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT100 (i+1))
      = (∑ i ∈ Finset.range 52, stT100 (i+1)) + stT100 53 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 52
    simpa using h
  have hprev := st100_p52
  have hstep := st100_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p54 : ((657188124439/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT100 (i+1))
      = (∑ i ∈ Finset.range 53, stT100 (i+1)) + stT100 54 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 53
    simpa using h
  have hprev := st100_p53
  have hstep := st100_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p55 : ((26519148912583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT100 (i+1))
      = (∑ i ∈ Finset.range 54, stT100 (i+1)) + stT100 55 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 54
    simpa using h
  have hprev := st100_p54
  have hstep := st100_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p56 : ((27747947758577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT100 (i+1))
      = (∑ i ∈ Finset.range 55, stT100 (i+1)) + stT100 56 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 55
    simpa using h
  have hprev := st100_p55
  have hstep := st100_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p57 : ((13498413805669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT100 (i+1))
      = (∑ i ∈ Finset.range 56, stT100 (i+1)) + stT100 57 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 56
    simpa using h
  have hprev := st100_p56
  have hstep := st100_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p58 : ((26055266778723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT100 (i+1))
      = (∑ i ∈ Finset.range 57, stT100 (i+1)) + stT100 58 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 57
    simpa using h
  have hprev := st100_p57
  have hstep := st100_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p59 : ((5416597674087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT100 (i+1))
      = (∑ i ∈ Finset.range 58, stT100 (i+1)) + stT100 59 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 58
    simpa using h
  have hprev := st100_p58
  have hstep := st100_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p60 : ((27758761761723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT100 (i+1))
      = (∑ i ∈ Finset.range 59, stT100 (i+1)) + stT100 60 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 59
    simpa using h
  have hprev := st100_p59
  have hstep := st100_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p61 : ((6654119819501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT100 (i+1))
      = (∑ i ∈ Finset.range 60, stT100 (i+1)) + stT100 61 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 60
    simpa using h
  have hprev := st100_p60
  have hstep := st100_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p62 : ((6526507478537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT100 (i+1))
      = (∑ i ∈ Finset.range 61, stT100 (i+1)) + stT100 62 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 61
    simpa using h
  have hprev := st100_p61
  have hstep := st100_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p63 : ((6818484900287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT100 (i+1))
      = (∑ i ∈ Finset.range 62, stT100 (i+1)) + stT100 63 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 62
    simpa using h
  have hprev := st100_p62
  have hstep := st100_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p64 : ((6934465837787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT100 (i+1))
      = (∑ i ∈ Finset.range 63, stT100 (i+1)) + stT100 64 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 63
    simpa using h
  have hprev := st100_p63
  have hstep := st100_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p65 : ((5319137531/2000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT100 (i+1))
      = (∑ i ∈ Finset.range 64, stT100 (i+1)) + stT100 65 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 64
    simpa using h
  have hprev := st100_p64
  have hstep := st100_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p66 : ((1303304200721/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT100 (i+1))
      = (∑ i ∈ Finset.range 65, stT100 (i+1)) + stT100 66 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 65
    simpa using h
  have hprev := st100_p65
  have hstep := st100_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p67 : ((13565609575007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT100 (i+1))
      = (∑ i ∈ Finset.range 66, stT100 (i+1)) + stT100 67 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 66
    simpa using h
  have hprev := st100_p66
  have hstep := st100_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p68 : ((13908450623099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT100 (i+1))
      = (∑ i ∈ Finset.range 67, stT100 (i+1)) + stT100 68 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 67
    simpa using h
  have hprev := st100_p67
  have hstep := st100_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p69 : ((26905395792771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT100 (i+1))
      = (∑ i ∈ Finset.range 68, stT100 (i+1)) + stT100 69 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 68
    simpa using h
  have hprev := st100_p68
  have hstep := st100_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p70 : ((26012251360689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT100 (i+1))
      = (∑ i ∈ Finset.range 69, stT100 (i+1)) + stT100 70 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 69
    simpa using h
  have hprev := st100_p69
  have hstep := st100_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p71 : ((3332152272021/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT100 (i+1))
      = (∑ i ∈ Finset.range 70, stT100 (i+1)) + stT100 71 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 70
    simpa using h
  have hprev := st100_p70
  have hstep := st100_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p72 : ((13870758324903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT100 (i+1))
      = (∑ i ∈ Finset.range 71, stT100 (i+1)) + stT100 72 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 71
    simpa using h
  have hprev := st100_p71
  have hstep := st100_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p73 : ((13748178735319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT100 (i+1))
      = (∑ i ∈ Finset.range 72, stT100 (i+1)) + stT100 73 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 72
    simpa using h
  have hprev := st100_p72
  have hstep := st100_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p74 : ((6583455586697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT100 (i+1))
      = (∑ i ∈ Finset.range 73, stT100 (i+1)) + stT100 74 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 73
    simpa using h
  have hprev := st100_p73
  have hstep := st100_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p75 : ((3259131161469/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT100 (i+1))
      = (∑ i ∈ Finset.range 74, stT100 (i+1)) + stT100 75 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 74
    simpa using h
  have hprev := st100_p74
  have hstep := st100_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p76 : ((13546795985247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT100 (i+1))
      = (∑ i ∈ Finset.range 75, stT100 (i+1)) + stT100 76 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 75
    simpa using h
  have hprev := st100_p75
  have hstep := st100_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p77 : ((13929972212027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT100 (i+1))
      = (∑ i ∈ Finset.range 76, stT100 (i+1)) + stT100 77 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 76
    simpa using h
  have hprev := st100_p76
  have hstep := st100_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p78 : ((13632714136409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT100 (i+1))
      = (∑ i ∈ Finset.range 77, stT100 (i+1)) + stT100 78 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 77
    simpa using h
  have hprev := st100_p77
  have hstep := st100_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p79 : ((13088451691321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT100 (i+1))
      = (∑ i ∈ Finset.range 78, stT100 (i+1)) + stT100 79 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 78
    simpa using h
  have hprev := st100_p78
  have hstep := st100_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p80 : ((13056530702587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT100 (i+1))
      = (∑ i ∈ Finset.range 79, stT100 (i+1)) + stT100 80 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 79
    simpa using h
  have hprev := st100_p79
  have hstep := st100_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p81 : ((27142520191117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT100 (i+1))
      = (∑ i ∈ Finset.range 80, stT100 (i+1)) + stT100 81 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 80
    simpa using h
  have hprev := st100_p80
  have hstep := st100_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p82 : ((13939208466881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT100 (i+1))
      = (∑ i ∈ Finset.range 81, stT100 (i+1)) + stT100 82 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 81
    simpa using h
  have hprev := st100_p81
  have hstep := st100_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p83 : ((6842211238039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT100 (i+1))
      = (∑ i ∈ Finset.range 82, stT100 (i+1)) + stT100 83 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 82
    simpa using h
  have hprev := st100_p82
  have hstep := st100_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p84 : ((6571060097779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT100 (i+1))
      = (∑ i ∈ Finset.range 83, stT100 (i+1)) + stT100 84 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 83
    simpa using h
  have hprev := st100_p83
  have hstep := st100_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p85 : ((6496681102957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT100 (i+1))
      = (∑ i ∈ Finset.range 84, stT100 (i+1)) + stT100 85 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 84
    simpa using h
  have hprev := st100_p84
  have hstep := st100_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p86 : ((6706456680883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT100 (i+1))
      = (∑ i ∈ Finset.range 85, stT100 (i+1)) + stT100 86 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 85
    simpa using h
  have hprev := st100_p85
  have hstep := st100_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p87 : ((6944542736947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT100 (i+1))
      = (∑ i ∈ Finset.range 86, stT100 (i+1)) + stT100 87 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 86
    simpa using h
  have hprev := st100_p86
  have hstep := st100_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p88 : ((346571717613/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT100 (i+1))
      = (∑ i ∈ Finset.range 87, stT100 (i+1)) + stT100 88 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 87
    simpa using h
  have hprev := st100_p87
  have hstep := st100_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p89 : ((6686490544419/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT100 (i+1))
      = (∑ i ∈ Finset.range 88, stT100 (i+1)) + stT100 89 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 88
    simpa using h
  have hprev := st100_p88
  have hstep := st100_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p90 : ((25957373068423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT100 (i+1))
      = (∑ i ∈ Finset.range 89, stT100 (i+1)) + stT100 90 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 89
    simpa using h
  have hprev := st100_p89
  have hstep := st100_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p91 : ((26226645779503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT100 (i+1))
      = (∑ i ∈ Finset.range 90, stT100 (i+1)) + stT100 91 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 90
    simpa using h
  have hprev := st100_p90
  have hstep := st100_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p92 : ((27244477545943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT100 (i+1))
      = (∑ i ∈ Finset.range 91, stT100 (i+1)) + stT100 92 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 91
    simpa using h
  have hprev := st100_p91
  have hstep := st100_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p93 : ((27918582799827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT100 (i+1))
      = (∑ i ∈ Finset.range 92, stT100 (i+1)) + stT100 93 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 92
    simpa using h
  have hprev := st100_p92
  have hstep := st100_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p94 : ((27553481071689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT100 (i+1))
      = (∑ i ∈ Finset.range 93, stT100 (i+1)) + stT100 94 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 93
    simpa using h
  have hprev := st100_p93
  have hstep := st100_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p95 : ((1658693541273/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT100 (i+1))
      = (∑ i ∈ Finset.range 94, stT100 (i+1)) + stT100 95 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 94
    simpa using h
  have hprev := st100_p94
  have hstep := st100_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p96 : ((1618854621159/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT100 (i+1))
      = (∑ i ∈ Finset.range 95, stT100 (i+1)) + stT100 96 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 95
    simpa using h
  have hprev := st100_p95
  have hstep := st100_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p97 : ((1641313059333/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT100 (i+1))
      = (∑ i ∈ Finset.range 96, stT100 (i+1)) + stT100 97 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 96
    simpa using h
  have hprev := st100_p96
  have hstep := st100_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p98 : ((1703386142119/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT100 (i+1))
      = (∑ i ∈ Finset.range 97, stT100 (i+1)) + stT100 98 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 97
    simpa using h
  have hprev := st100_p97
  have hstep := st100_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p99 : ((1117240134237/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT100 (i+1))
      = (∑ i ∈ Finset.range 98, stT100 (i+1)) + stT100 99 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 98
    simpa using h
  have hprev := st100_p98
  have hstep := st100_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st100_p100 : ((1106718374237/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT100 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT100 (i+1))
      = (∑ i ∈ Finset.range 99, stT100 (i+1)) + stT100 100 := by
    have h := Finset.sum_range_succ (fun i => stT100 (i+1)) 99
    simpa using h
  have hprev := st100_p99
  have hstep := st100_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 100`.** -/
theorem station_100_sign : 0 < hardyG (((100:ℕ)):ℝ) := by
  have hcore := phase_station_lower 100 100 (by norm_num) (by norm_num)
    ((7571/1000000 : ℚ) : ℝ)
  have hchain := st100_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT100 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((100:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((7571/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((100:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((100:ℕ)):ℝ)+1) * ((((100:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((408551/400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1106718374237/400000000000 : ℚ) : ℝ) - ((408551/400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((7571/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((100:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((7571/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((100:ℕ)):ℝ))).re
      - Real.sin ((7571/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((100:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((100:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((100:ℕ)):ℝ)
      = ((((100:ℕ)):ℝ) * (Real.log (((100:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((100:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_100
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
  have hθwin : |(((7571/1000000 : ℚ) : ℝ) + ((14:ℤ)) * (2*Real.pi)) - theta (((100:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((100:ℕ)):ℝ))
    (φ := ((7571/1000000 : ℚ) : ℝ) + ((14:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((7571/1000000 : ℚ)) : ℝ) 14).1,
    (cos_sin_shift (((7571/1000000 : ℚ)) : ℝ) 14).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_100_sign
end AxiomAudit
