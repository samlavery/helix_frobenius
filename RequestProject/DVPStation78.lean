import RequestProject.DVPSqrtTable

/-!
# Station `t = 78` of the extended Hardy ladder (rung-81)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT78 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((78 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-424127/500000 : ℚ) : ℝ))

theorem st78_c1 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((330647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1060317/5000000) (δ := 41/100000000) (ψ := -424127/500000) 78 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t1 : ((165311/250000 : ℚ) : ℝ) ≤ stT78 1 := by
  have hc : ((165311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165311/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((165311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c2 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-32047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -817467/2000000) (δ := 299/50000000) (ψ := -424127/500000) 78 9
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t2 : ((-7086977903/156250000000 : ℚ) : ℝ) ≤ stT78 2 := by
  have hc : ((-4009/62500 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7086977903/156250000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-4009/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c3 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((72847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -712291/2000000) (δ := 21/3125000) (ψ := -424127/500000) 78 14
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t3 : ((105109490661/1250000000000 : ℚ) : ℝ) ≤ stT78 3 := by
  have hc : ((36411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105109490661/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((36411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c4 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-279951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5412659/10000000) (δ := 111/25000000) (ψ := -424127/500000) 78 17
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t4 : ((-174985034997/625000000000 : ℚ) : ℝ) ≤ stT78 4 := by
  have hc : ((-34997/62500 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174985034997/625000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-34997/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c5 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((751341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 900881/5000000) (δ := 707/100000000) (ψ := -424127/500000) 78 20
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t5 : ((671974955257/2000000000000 : ℚ) : ℝ) ≤ stT78 5 := by
  have hc : ((751291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671974955257/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((751291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c6 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-720567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5938539/10000000) (δ := 517/100000000) (ψ := -424127/500000) 78 22
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t6 : ((-2941906652011/10000000000000 : ℚ) : ℝ) ≤ stT78 6 := by
  have hc : ((-720617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2941906652011/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-720617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c7 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-129507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 916399/2000000) (δ := 53/12500000) (ψ := -424127/500000) 78 24
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t7 : ((-24479248807/250000000000 : ℚ) : ℝ) ≤ stT78 7 := by
  have hc : ((-32383/125000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24479248807/250000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-32383/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c8 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((14841/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79531/1000000) (δ := 483/100000000) (ψ := -424127/500000) 78 26
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t8 : ((1678978659771/5000000000000 : ℚ) : ℝ) ≤ stT78 8 := by
  have hc : ((474887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1678978659771/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((474887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c9 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-169893/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6464419/10000000) (δ := 591/100000000) (ψ := -424127/500000) 78 27
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t9 : ((-283171723301/1000000000000 : ℚ) : ℝ) ≤ stT78 9 := by
  have hc : ((-169903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283171723301/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-169903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c10 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-38103/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4406207/10000000) (δ := 89/12500000) (ψ := -424127/500000) 78 29
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t10 : ((-60261950707/1000000000000 : ℚ) : ℝ) ≤ stT78 10 := by
  have hc : ((-38113/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60261950707/1000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-38113/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c11 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((818803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305737/2000000) (δ := 563/100000000) (ψ := -424127/500000) 78 30
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t11 : ((2468632814089/10000000000000 : ℚ) : ℝ) ≤ stT78 11 := by
  have hc : ((818753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2468632814089/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((818753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c12 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((497099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26943/1000000) (δ := 409/100000000) (ψ := -424127/500000) 78 31
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t12 : ((717464433287/2500000000000 : ℚ) : ℝ) ≤ stT78 12 := by
  have hc : ((248537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((717464433287/2500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((248537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c13 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((989123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73813/2000000) (δ := 111/25000000) (ψ := -424127/500000) 78 32
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t13 : ((5486387931/20000000000 : ℚ) : ℝ) ≤ stT78 13 := by
  have hc : ((989073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5486387931/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((989073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c14 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((99481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -812987/5000000) (δ := 71/12500000) (ψ := -424127/500000) 78 33
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t14 : ((265857410547/1250000000000 : ℚ) : ℝ) ≤ stT78 14 := by
  have hc : ((397899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265857410547/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((397899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c15 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((2333/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3880327/10000000) (δ := 777/100000000) (ψ := -424127/500000) 78 34
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t15 : ((6007640579/1250000000000 : ℚ) : ℝ) ≤ stT78 15 := by
  have hc : ((9307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6007640579/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((9307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c16 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-942661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7003279/10000000) (δ := 313/50000000) (ψ := -424127/500000) 78 35
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t16 : ((-2356778442711/10000000000000 : ℚ) : ℝ) ≤ stT78 16 := by
  have hc : ((-942711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2356778442711/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-942711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c17 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-174551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2409261/5000000) (δ := 233/50000000) (ψ := -424127/500000) 78 35
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t17 : ((-26463070227/312500000000 : ℚ) : ℝ) ≤ stT78 17 := by
  have hc : ((-10911/31250 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26463070227/312500000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-10911/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c18 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((994743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5129/200000) (δ := 447/100000000) (ψ := -424127/500000) 78 36
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t18 : ((1172256642123/5000000000000 : ℚ) : ℝ) ≤ stT78 18 := by
  have hc : ((994693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1172256642123/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((994693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c19 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-2391/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -981681/2000000) (δ := 309/50000000) (ψ := -424127/500000) 78 37
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t19 : ((-43888389619/500000000000 : ℚ) : ℝ) ≤ stT78 19 := by
  have hc : ((-38261/100000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43888389619/500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-38261/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c20 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-224979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5093787/10000000) (δ := 279/50000000) (ψ := -424127/500000) 78 37
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t20 : ((-31445265267/312500000000 : ℚ) : ℝ) ≤ stT78 20 := by
  have hc : ((-56251/125000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31445265267/312500000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-56251/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c21 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((28273/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -550047/5000000) (δ := 247/50000000) (ψ := -424127/500000) 78 38
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t21 : ((493546471527/2500000000000 : ℚ) : ℝ) ≤ stT78 21 := by
  have hc : ((452343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493546471527/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((452343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c22 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-998899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1547331/2000000) (δ := 403/100000000) (ψ := -424127/500000) 78 39
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t22 : ((-266220907449/1250000000000 : ℚ) : ℝ) ≤ stT78 22 := by
  have hc : ((-998949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266220907449/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-998949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c23 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((931393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 931439/10000000) (δ := 683/100000000) (ψ := -424127/500000) 78 39
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t23 : ((242748033549/1250000000000 : ℚ) : ℝ) ≤ stT78 23 := by
  have hc : ((931343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242748033549/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((931343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c24 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-852193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6477399/10000000) (δ := 553/100000000) (ψ := -424127/500000) 78 40
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t24 : ((-869817102903/5000000000000 : ℚ) : ℝ) ≤ stT78 24 := by
  have hc : ((-852243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-869817102903/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-852243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c25 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((829181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148289/1000000) (δ := 593/100000000) (ψ := -424127/500000) 78 40
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t25 : ((829131/5000000 : ℚ) : ℝ) ≤ stT78 25 := by
  have hc : ((829131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((829131/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((829131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c26 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-218091/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1315407/2000000) (δ := 261/50000000) (ψ := -424127/500000) 78 41
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t26 : ((-427736296267/2500000000000 : ℚ) : ℝ) ≤ stT78 26 := by
  have hc : ((-436207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427736296267/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-436207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c27 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((190287/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 782329/10000000) (δ := 481/100000000) (ψ := -424127/500000) 78 41
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t27 : ((732376173/4000000000 : ℚ) : ℝ) ≤ stT78 27 := by
  have hc : ((190277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((732376173/4000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((190277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c28 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-31249/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7833943/10000000) (δ := 711/100000000) (ψ := -424127/500000) 78 42
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t28 : ((-944928508407/5000000000000 : ℚ) : ℝ) ≤ stT78 28 := by
  have hc : ((-500009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-944928508407/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-500009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c29 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((230609/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30973/312500) (δ := 571/100000000) (ψ := -424127/500000) 78 42
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t29 : ((856413724929/5000000000000 : ℚ) : ℝ) ≤ stT78 29 := by
  have hc : ((461193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((856413724929/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((461193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c30 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-39157/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5619667/10000000) (δ := 79/12500000) (ψ := -424127/500000) 78 42
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t30 : ((-285985139751/2500000000000 : ℚ) : ℝ) ≤ stT78 30 := by
  have hc : ((-313281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285985139751/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-313281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c31 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((1859/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3694281/10000000) (δ := 761/100000000) (ψ := -424127/500000) 78 43
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t31 : ((1668533237/100000000000 : ℚ) : ℝ) ≤ stT78 31 := by
  have hc : ((929/10000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1668533237/100000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((929/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c32 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((16919/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 499343/2000000) (δ := 781/100000000) (ψ := -424127/500000) 78 43
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t32 : ((239248566557/2500000000000 : ℚ) : ℝ) ≤ stT78 32 := by
  have hc : ((270679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239248566557/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((270679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c33 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-193417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288431/400000) (δ := 453/100000000) (ψ := -424127/500000) 78 44
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t33 : ((-336713272779/2000000000000 : ℚ) : ℝ) ≤ stT78 33 := by
  have hc : ((-193427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336713272779/2000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-193427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c34 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((84949/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1389447/10000000) (δ := 61/10000000) (ψ := -424127/500000) 78 44
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t34 : ((1820971073/12500000000 : ℚ) : ℝ) ≤ stT78 34 := by
  have hc : ((5309/6250 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1820971073/12500000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((5309/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c35 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-4189/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4263123/10000000) (δ := 473/100000000) (ψ := -424127/500000) 78 44
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t35 : ((-113333528141/5000000000000 : ℚ) : ℝ) ≤ stT78 35 := by
  have hc : ((-67049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113333528141/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-67049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c36 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-724157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37197/62500) (δ := 519/100000000) (ψ := -424127/500000) 78 45
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t36 : ((-1207011908069/10000000000000 : ℚ) : ℝ) ≤ stT78 36 := by
  have hc : ((-724207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1207011908069/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-724207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c37 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((970503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7609/125000) (δ := 719/100000000) (ψ := -424127/500000) 78 45
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t37 : ((1595414057017/10000000000000 : ℚ) : ℝ) ≤ stT78 37 := by
  have hc : ((970453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1595414057017/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((970453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c38 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-262719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4591589/10000000) (δ := 29/6250000) (ψ := -424127/500000) 78 45
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t38 : ((-85253562667/2000000000000 : ℚ) : ℝ) ≤ stT78 38 := by
  have hc : ((-262769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85253562667/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-262769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c39 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-37553/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1210231/2000000) (δ := 7/1562500) (ψ := -424127/500000) 78 46
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t39 : ((-60136946151/500000000000 : ℚ) : ℝ) ≤ stT78 39 := by
  have hc : ((-75111/100000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60136946151/500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-75111/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c40 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((902321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -557091/5000000) (δ := 83/20000000) (ψ := -424127/500000) 78 46
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t40 : ((713307482199/5000000000000 : ℚ) : ℝ) ≤ stT78 40 := by
  have hc : ((902271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((713307482199/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((902271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c41 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((45161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3700877/10000000) (δ := 99/20000000) (ψ := -424127/500000) 78 46
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t41 : ((4405660077/312500000000 : ℚ) : ℝ) ≤ stT78 41 := by
  have hc : ((2821/31250 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4405660077/312500000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((2821/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c42 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-976253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228377/312500) (δ := 339/50000000) (ψ := -424127/500000) 78 47
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t42 : ((-753234361651/5000000000000 : ℚ) : ℝ) ≤ stT78 42 := by
  have hc : ((-976303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-753234361651/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-976303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c43 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((464393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2719617/10000000) (δ := 349/50000000) (ψ := -424127/500000) 78 47
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t43 : ((141623221971/2000000000000 : ℚ) : ℝ) ≤ stT78 43 := by
  have hc : ((464343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141623221971/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((464343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c44 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((380697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88167/500000) (δ := 259/50000000) (ψ := -424127/500000) 78 47
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t44 : ((560433943/4882812500 : ℚ) : ℝ) ≤ stT78 44 := by
  have hc : ((11896/15625 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((560433943/4882812500 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((11896/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c45 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-775447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3072773/5000000) (δ := 133/20000000) (ψ := -424127/500000) 78 47
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t45 : ((-144505335483/1250000000000 : ℚ) : ℝ) ≤ stT78 45 := by
  have hc : ((-775497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144505335483/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-775497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c46 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-256989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -527653/1000000) (δ := 23/3125000) (ψ := -424127/500000) 78 48
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t46 : ((-9473664547/125000000000 : ℚ) : ℝ) ≤ stT78 46 := by
  have hc : ((-128507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9473664547/125000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-128507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c47 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((907657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54141/500000) (δ := 787/100000000) (ψ := -424127/500000) 78 48
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t47 : ((1323880042943/10000000000000 : ℚ) : ℝ) ≤ stT78 47 := by
  have hc : ((907607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1323880042943/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((907607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c48 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((353919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604519/2000000) (δ := 707/100000000) (ψ := -424127/500000) 78 48
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t48 : ((4086125343/80000000000 : ℚ) : ℝ) ≤ stT78 48 := by
  have hc : ((353869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4086125343/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((353869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c49 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-94789/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1760839/2500000) (δ := 189/25000000) (ψ := -424127/500000) 78 48
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t49 : ((-16927506771/125000000000 : ℚ) : ℝ) ≤ stT78 49 := by
  have hc : ((-47397/50000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16927506771/125000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-47397/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c50 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-313841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118127/250000) (δ := 97/12500000) (ψ := -424127/500000) 78 49
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t50 : ((-221954523337/5000000000000 : ℚ) : ℝ) ≤ stT78 50 := by
  have hc : ((-313891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221954523337/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-313891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c51 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((940931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -863567/10000000) (δ := 67/12500000) (ψ := -424127/500000) 78 49
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t51 : ((32937421167/250000000000 : ℚ) : ℝ) ≤ stT78 51 := by
  have hc : ((940881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32937421167/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((940881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c52 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((390903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2922959/10000000) (δ := 169/25000000) (ψ := -424127/500000) 78 49
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t52 : ((2168061591/40000000000 : ℚ) : ℝ) ≤ stT78 52 := by
  have hc : ((390853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2168061591/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((390853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c53 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-176781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3318679/5000000) (δ := 169/25000000) (ψ := -424127/500000) 78 49
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t53 : ((-121420589173/1000000000000 : ℚ) : ℝ) ≤ stT78 53 := by
  have hc : ((-176791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121420589173/1000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-176791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c54 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-141049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135641/250000) (δ := 223/50000000) (ψ := -424127/500000) 78 50
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t54 : ((-95980219461/1250000000000 : ℚ) : ℝ) ≤ stT78 54 := by
  have hc : ((-282123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95980219461/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-282123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c55 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((739127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -923779/5000000) (δ := 637/100000000) (ψ := -424127/500000) 78 50
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t55 : ((996570687723/10000000000000 : ℚ) : ℝ) ≤ stT78 55 := by
  have hc : ((739077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((996570687723/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((739077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c56 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((19651/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1666051/10000000) (δ := 697/100000000) (ψ := -424127/500000) 78 50
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t56 : ((52516157647/500000000000 : ℚ) : ℝ) ≤ stT78 56 := by
  have hc : ((78599/100000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52516157647/500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((78599/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c57 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-458397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1279367/2500000) (δ := 497/100000000) (ψ := -424127/500000) 78 50
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t57 : ((-607228180251/10000000000000 : ℚ) : ℝ) ≤ stT78 57 := by
  have hc : ((-458447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-607228180251/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-458447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c58 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-965887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1439821/2000000) (δ := 143/20000000) (ψ := -424127/500000) 78 51
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t58 : ((-253667613381/2000000000000 : ℚ) : ℝ) ≤ stT78 58 := by
  have hc : ((-965937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253667613381/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-965937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c59 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((24517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3865691/10000000) (δ := 19/4000000) (ψ := -424127/500000) 78 51
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t59 : ((31853318163/10000000000000 : ℚ) : ℝ) ≤ stT78 59 := by
  have hc : ((24467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31853318163/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((24467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c60 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((24311/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -588303/10000000) (δ := 7/1562500) (ψ := -424127/500000) 78 51
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t60 : ((62767482783/500000000000 : ℚ) : ℝ) ≤ stT78 60 := by
  have hc : ((97239/100000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62767482783/500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((97239/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c61 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((30883/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2634911/10000000) (δ := 117/25000000) (ψ := -424127/500000) 78 51
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t61 : ((19768801897/312500000000 : ℚ) : ℝ) ≤ stT78 61 := by
  have hc : ((247039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19768801897/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((247039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c62 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-682727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5805713/10000000) (δ := 81/12500000) (ψ := -424127/500000) 78 51
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t62 : ((-433564077777/5000000000000 : ℚ) : ℝ) ≤ stT78 62 := by
  have hc : ((-682777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433564077777/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-682777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c63 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-909499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -847773/1250000) (δ := 151/25000000) (ψ := -424127/500000) 78 52
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t63 : ((-572962206609/5000000000000 : ℚ) : ℝ) ≤ stT78 63 := by
  have hc : ((-909549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-572962206609/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-909549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c64 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((21547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1855627/5000000) (δ := 639/100000000) (ψ := -424127/500000) 78 52
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t64 : ((43069/4000000 : ℚ) : ℝ) ≤ stT78 64 := by
  have hc : ((43069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43069/4000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((43069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c65 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((481189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343969/5000000) (δ := 519/100000000) (ψ := -424127/500000) 78 52
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t65 : ((149202580977/1250000000000 : ℚ) : ℝ) ≤ stT78 65 := by
  have hc : ((120291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149202580977/1250000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((120291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c66 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((121849/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2289219/10000000) (δ := 121/25000000) (ψ := -424127/500000) 78 52
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t66 : ((74986665423/1000000000000 : ℚ) : ℝ) ≤ stT78 66 := by
  have hc : ((121839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74986665423/1000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((121839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c67 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-495009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1044321/2000000) (δ := 83/12500000) (ψ := -424127/500000) 78 52
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t67 : ((-120962221001/2000000000000 : ℚ) : ℝ) ≤ stT78 67 := by
  have hc : ((-495059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120962221001/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-495059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c68 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-994739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -949677/1250000) (δ := 753/100000000) (ψ := -424127/500000) 78 53
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t68 : ((-1206359729731/10000000000000 : ℚ) : ℝ) ≤ stT78 68 := by
  have hc : ((-994789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1206359729731/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-994789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c69 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-20221/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95013/200000) (δ := 753/100000000) (ψ := -424127/500000) 78 53
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t69 : ((-194775959187/5000000000000 : ℚ) : ℝ) ≤ stT78 69 := by
  have hc : ((-161793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194775959187/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-161793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c70 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((356181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1944847/10000000) (δ := 493/100000000) (ψ := -424127/500000) 78 53
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t70 : ((26605476473/312500000000 : ℚ) : ℝ) ≤ stT78 70 := by
  have hc : ((89039/125000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26605476473/312500000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((89039/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c71 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((946539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 821157/10000000) (δ := 57/10000000) (ψ := -424127/500000) 78 53
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t71 : ((1123275161909/10000000000000 : ℚ) : ℝ) ≤ stT78 71 := by
  have hc : ((946489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1123275161909/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((946489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c72 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((150829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141939/400000) (δ := 633/100000000) (ψ := -424127/500000) 78 53
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t72 : ((177694710069/10000000000000 : ℚ) : ℝ) ≤ stT78 72 := by
  have hc : ((150779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177694710069/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((150779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c73 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-798303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1559543/2500000) (δ := 493/100000000) (ψ := -424127/500000) 78 53
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t73 : ((-233600482859/2500000000000 : ℚ) : ℝ) ≤ stT78 73 := by
  have hc : ((-798353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233600482859/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-798353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c74 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-18303/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6816689/10000000) (δ := 7/1000000) (ψ := -424127/500000) 78 54
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t74 : ((-166234211/1562500000 : ℚ) : ℝ) ≤ stT78 74 := by
  have hc : ((-572/625 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166234211/1562500000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-572/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c75 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-108669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5249/12500) (δ := 703/100000000) (ψ := -424127/500000) 78 54
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t75 : ((-125537938019/10000000000000 : ℚ) : ℝ) ≤ stT78 75 := by
  have hc : ((-108719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125537938019/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-108719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c76 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((399083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1616381/10000000) (δ := 503/100000000) (ψ := -424127/500000) 78 54
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t76 : ((114437663131/1250000000000 : ℚ) : ℝ) ≤ stT78 76 := by
  have hc : ((199529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114437663131/1250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((199529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c77 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((931213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37307/400000) (δ := 643/100000000) (ψ := -424127/500000) 78 54
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t77 : ((212231602123/2000000000000 : ℚ) : ℝ) ≤ stT78 77 := by
  have hc : ((931163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212231602123/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((931163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c78 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((190097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3448839/10000000) (δ := 603/100000000) (ψ := -424127/500000) 78 54
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t78 : ((215185847019/10000000000000 : ℚ) : ℝ) ≤ stT78 78 := by
  have hc : ((190047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215185847019/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((190047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c79 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-359507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5932949/10000000) (δ := 403/100000000) (ψ := -424127/500000) 78 54
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t79 : ((-3160196397/39062500000 : ℚ) : ℝ) ≤ stT78 79 := by
  have hc : ((-89883/125000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3160196397/39062500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-89883/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c80 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-488729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7322151/10000000) (δ := 2/390625) (ψ := -424127/500000) 78 55
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t80 : ((-136610897409/1250000000000 : ℚ) : ℝ) ≤ stT78 80 := by
  have hc : ((-244377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136610897409/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-244377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c81 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-379363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61247/125000) (δ := 411/100000000) (ψ := -424127/500000) 78 55
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t81 : ((-52696292157/1250000000000 : ℚ) : ℝ) ≤ stT78 81 := by
  have hc : ((-379413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52696292157/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-379413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c82 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((537913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626773/2500000) (δ := 27/6250000) (ψ := -424127/500000) 78 55
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t82 : ((118794035769/2000000000000 : ℚ) : ℝ) ≤ stT78 82 := by
  have hc : ((537863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118794035769/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((537863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c83 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((199671/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143427/10000000) (δ := 47/6250000) (ψ := -424127/500000) 78 55
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t83 : ((109578149681/1000000000000 : ℚ) : ℝ) ≤ stT78 83 := by
  have hc : ((199661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109578149681/1000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((199661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c84 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((127927/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2191931/10000000) (δ := 99/12500000) (ψ := -424127/500000) 78 55
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t84 : ((139568831613/2000000000000 : ℚ) : ℝ) ≤ stT78 84 := by
  have hc : ((127917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139568831613/2000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((127917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c85 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-113533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89993/200000) (δ := 431/100000000) (ψ := -424127/500000) 78 55
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t85 : ((-61585512687/2500000000000 : ℚ) : ℝ) ≤ stT78 85 := by
  have hc : ((-56779/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61585512687/2500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-56779/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c86 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-454599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3390189/5000000) (δ := 751/100000000) (ψ := -424127/500000) 78 55
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t86 : ((-1914975737/19531250000 : ℚ) : ℝ) ≤ stT78 86 := by
  have hc : ((-14207/15625 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1914975737/19531250000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-14207/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c87 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-890523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266929/400000) (δ := 641/100000000) (ψ := -424127/500000) 78 56
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t87 : ((-954794890749/10000000000000 : ℚ) : ℝ) ≤ stT78 87 := by
  have hc : ((-890573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-954794890749/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-890573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c88 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-205579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -444463/1000000) (δ := 701/100000000) (ψ := -424127/500000) 78 56
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t88 : ((-54800334129/2500000000000 : ℚ) : ℝ) ≤ stT78 88 := by
  have hc : ((-205629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54800334129/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-205629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c89 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((312179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35019/156250) (δ := 271/50000000) (ψ := -424127/500000) 78 56
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t89 : ((165441151769/2500000000000 : ℚ) : ℝ) ≤ stT78 89 := by
  have hc : ((156077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165441151769/2500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((156077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c90 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((124961/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62423/10000000) (δ := 261/50000000) (ψ := -424127/500000) 78 56
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t90 : ((131713802337/1250000000000 : ℚ) : ℝ) ≤ stT78 90 := by
  have hc : ((499819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131713802337/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((499819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c91 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((133951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418459/2000000) (δ := 401/50000000) (ψ := -424127/500000) 78 56
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t91 : ((35102051811/500000000000 : ℚ) : ℝ) ≤ stT78 91 := by
  have hc : ((133941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35102051811/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((133941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c92 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-14789/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527933/1250000) (δ := 291/50000000) (ψ := -424127/500000) 78 56
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t92 : ((-61700512713/5000000000000 : ℚ) : ℝ) ≤ stT78 92 := by
  have hc : ((-59181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61700512713/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-59181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c93 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-410123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6331593/10000000) (δ := 361/50000000) (ψ := -424127/500000) 78 56
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t93 : ((-13290743403/156250000000 : ℚ) : ℝ) ≤ stT78 93 := by
  have hc : ((-102537/125000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13290743403/156250000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-102537/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c94 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-243683/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7290789/10000000) (δ := 79/12500000) (ψ := -424127/500000) 78 57
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t94 : ((-251352900001/2500000000000 : ℚ) : ℝ) ≤ stT78 94 := by
  have hc : ((-487391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251352900001/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-487391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c95 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-24849/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2613639/5000000) (δ := 173/25000000) (ψ := -424127/500000) 78 57
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t95 : ((-50994234237/1000000000000 : ℚ) : ℝ) ≤ stT78 95 := by
  have hc : ((-49703/100000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50994234237/1000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-49703/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c96 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((58463/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592687/5000000) (δ := 89/12500000) (ψ := -424127/500000) 78 57
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t96 : ((2982915043/100000000000 : ℚ) : ℝ) ≤ stT78 96 := by
  have hc : ((58453/200000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2982915043/100000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((58453/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c97 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((893439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1164631/10000000) (δ := 37/6250000) (ψ := -424127/500000) 78 57
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t97 : ((453549473797/5000000000000 : ℚ) : ℝ) ≤ stT78 97 := by
  have hc : ((893389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453549473797/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((893389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c98 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((59043/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835387/10000000) (δ := 153/25000000) (ψ := -424127/500000) 78 57
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t98 : ((59639247811/625000000000 : ℚ) : ℝ) ≤ stT78 98 := by
  have hc : ((472319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59639247811/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((472319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c99 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((215119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2815099/10000000) (δ := 411/100000000) (ψ := -424127/500000) 78 57
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t99 : ((108088714239/2500000000000 : ℚ) : ℝ) ≤ stT78 99 := by
  have hc : ((107547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108088714239/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((107547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_c100 :
    |Real.cos (((78 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-424127/500000 : ℚ) : ℝ))
      - ((-10397/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2387457/5000000) (δ := 79/12500000) (ψ := -424127/500000) 78 57
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st78_t100 : ((-166377/5000000 : ℚ) : ℝ) ≤ stT78 100 := by
  have hc : ((-166377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((78 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-424127/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st78_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166377/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-166377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st78_p1 : ((165311/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT78 (i+1) := by
  rw [Finset.sum_range_one]
  exact st78_t1

theorem st78_p2 : ((96232397097/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT78 (i+1))
      = (∑ i ∈ Finset.range 1, stT78 (i+1)) + stT78 2 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 1
    simpa using h
  have hprev := st78_p1
  have hstep := st78_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p3 : ((874968667437/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT78 (i+1))
      = (∑ i ∈ Finset.range 2, stT78 (i+1)) + stT78 3 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 2
    simpa using h
  have hprev := st78_p2
  have hstep := st78_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p4 : ((524998597443/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT78 (i+1))
      = (∑ i ∈ Finset.range 3, stT78 (i+1)) + stT78 4 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 3
    simpa using h
  have hprev := st78_p3
  have hstep := st78_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p5 : ((7559863555829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT78 (i+1))
      = (∑ i ∈ Finset.range 4, stT78 (i+1)) + stT78 5 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 4
    simpa using h
  have hprev := st78_p4
  have hstep := st78_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p6 : ((2308978451909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT78 (i+1))
      = (∑ i ∈ Finset.range 5, stT78 (i+1)) + stT78 6 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 5
    simpa using h
  have hprev := st78_p5
  have hstep := st78_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p7 : ((1819393475769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT78 (i+1))
      = (∑ i ∈ Finset.range 6, stT78 (i+1)) + stT78 7 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 6
    simpa using h
  have hprev := st78_p6
  have hstep := st78_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p8 : ((174918606777/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT78 (i+1))
      = (∑ i ∈ Finset.range 7, stT78 (i+1)) + stT78 8 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 7
    simpa using h
  have hprev := st78_p7
  have hstep := st78_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p9 : ((416502703807/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT78 (i+1))
      = (∑ i ∈ Finset.range 8, stT78 (i+1)) + stT78 9 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 8
    simpa using h
  have hprev := st78_p8
  have hstep := st78_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p10 : ((3562407531/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT78 (i+1))
      = (∑ i ∈ Finset.range 9, stT78 (i+1)) + stT78 10 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 9
    simpa using h
  have hprev := st78_p9
  have hstep := st78_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p11 : ((6031040345089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT78 (i+1))
      = (∑ i ∈ Finset.range 10, stT78 (i+1)) + stT78 11 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 10
    simpa using h
  have hprev := st78_p10
  have hstep := st78_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p12 : ((8900898078237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT78 (i+1))
      = (∑ i ∈ Finset.range 11, stT78 (i+1)) + stT78 12 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 11
    simpa using h
  have hprev := st78_p11
  have hstep := st78_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p13 : ((11644092043737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT78 (i+1))
      = (∑ i ∈ Finset.range 12, stT78 (i+1)) + stT78 13 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 12
    simpa using h
  have hprev := st78_p12
  have hstep := st78_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p14 : ((13770951328113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT78 (i+1))
      = (∑ i ∈ Finset.range 13, stT78 (i+1)) + stT78 14 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 13
    simpa using h
  have hprev := st78_p13
  have hstep := st78_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p15 : ((2763802490549/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT78 (i+1))
      = (∑ i ∈ Finset.range 14, stT78 (i+1)) + stT78 15 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 14
    simpa using h
  have hprev := st78_p14
  have hstep := st78_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p16 : ((5731117005017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT78 (i+1))
      = (∑ i ∈ Finset.range 15, stT78 (i+1)) + stT78 16 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 15
    simpa using h
  have hprev := st78_p15
  have hstep := st78_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p17 : ((1061541576277/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT78 (i+1))
      = (∑ i ∈ Finset.range 16, stT78 (i+1)) + stT78 17 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 16
    simpa using h
  have hprev := st78_p16
  have hstep := st78_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p18 : ((1619991130877/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT78 (i+1))
      = (∑ i ∈ Finset.range 17, stT78 (i+1)) + stT78 18 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 17
    simpa using h
  have hprev := st78_p17
  have hstep := st78_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p19 : ((3020540313659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT78 (i+1))
      = (∑ i ∈ Finset.range 18, stT78 (i+1)) + stT78 19 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 18
    simpa using h
  have hprev := st78_p18
  have hstep := st78_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p20 : ((2768978191523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT78 (i+1))
      = (∑ i ∈ Finset.range 19, stT78 (i+1)) + stT78 20 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 19
    simpa using h
  have hprev := st78_p19
  have hstep := st78_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p21 : ((65250493261/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT78 (i+1))
      = (∑ i ∈ Finset.range 20, stT78 (i+1)) + stT78 21 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 20
    simpa using h
  have hprev := st78_p20
  have hstep := st78_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p22 : ((341260356019/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT78 (i+1))
      = (∑ i ∈ Finset.range 21, stT78 (i+1)) + stT78 22 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 21
    simpa using h
  have hprev := st78_p21
  have hstep := st78_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p23 : ((12862315661/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT78 (i+1))
      = (∑ i ∈ Finset.range 22, stT78 (i+1)) + stT78 23 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 22
    simpa using h
  have hprev := st78_p22
  have hstep := st78_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p24 : ((5561340727597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT78 (i+1))
      = (∑ i ∈ Finset.range 23, stT78 (i+1)) + stT78 24 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 23
    simpa using h
  have hprev := st78_p23
  have hstep := st78_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p25 : ((6390471727597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT78 (i+1))
      = (∑ i ∈ Finset.range 24, stT78 (i+1)) + stT78 25 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 24
    simpa using h
  have hprev := st78_p24
  have hstep := st78_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p26 : ((5534999135063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT78 (i+1))
      = (∑ i ∈ Finset.range 25, stT78 (i+1)) + stT78 26 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 25
    simpa using h
  have hprev := st78_p25
  have hstep := st78_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p27 : ((6450469351313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT78 (i+1))
      = (∑ i ∈ Finset.range 26, stT78 (i+1)) + stT78 27 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 26
    simpa using h
  have hprev := st78_p26
  have hstep := st78_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p28 : ((2752770421453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT78 (i+1))
      = (∑ i ∈ Finset.range 27, stT78 (i+1)) + stT78 28 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 27
    simpa using h
  have hprev := st78_p27
  have hstep := st78_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p29 : ((1272390913567/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT78 (i+1))
      = (∑ i ∈ Finset.range 28, stT78 (i+1)) + stT78 29 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 28
    simpa using h
  have hprev := st78_p28
  have hstep := st78_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p30 : ((5789984288333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT78 (i+1))
      = (∑ i ∈ Finset.range 29, stT78 (i+1)) + stT78 30 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 29
    simpa using h
  have hprev := st78_p29
  have hstep := st78_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p31 : ((5873410950183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT78 (i+1))
      = (∑ i ∈ Finset.range 30, stT78 (i+1)) + stT78 31 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 30
    simpa using h
  have hprev := st78_p30
  have hstep := st78_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p32 : ((6351908083297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT78 (i+1))
      = (∑ i ∈ Finset.range 31, stT78 (i+1)) + stT78 32 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 31
    simpa using h
  have hprev := st78_p31
  have hstep := st78_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p33 : ((11020249802699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT78 (i+1))
      = (∑ i ∈ Finset.range 32, stT78 (i+1)) + stT78 33 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 32
    simpa using h
  have hprev := st78_p32
  have hstep := st78_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p34 : ((12477026661099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT78 (i+1))
      = (∑ i ∈ Finset.range 33, stT78 (i+1)) + stT78 34 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 33
    simpa using h
  have hprev := st78_p33
  have hstep := st78_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p35 : ((12250359604817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT78 (i+1))
      = (∑ i ∈ Finset.range 34, stT78 (i+1)) + stT78 35 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 34
    simpa using h
  have hprev := st78_p34
  have hstep := st78_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p36 : ((2760836924187/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT78 (i+1))
      = (∑ i ∈ Finset.range 35, stT78 (i+1)) + stT78 36 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 35
    simpa using h
  have hprev := st78_p35
  have hstep := st78_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p37 : ((2527752350753/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT78 (i+1))
      = (∑ i ∈ Finset.range 36, stT78 (i+1)) + stT78 37 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 36
    simpa using h
  have hprev := st78_p36
  have hstep := st78_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p38 : ((1221249394043/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT78 (i+1))
      = (∑ i ∈ Finset.range 37, stT78 (i+1)) + stT78 38 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 37
    simpa using h
  have hprev := st78_p37
  have hstep := st78_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p39 : ((1100975501741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT78 (i+1))
      = (∑ i ∈ Finset.range 38, stT78 (i+1)) + stT78 39 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 38
    simpa using h
  have hprev := st78_p38
  have hstep := st78_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p40 : ((777273123863/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT78 (i+1))
      = (∑ i ∈ Finset.range 39, stT78 (i+1)) + stT78 40 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 39
    simpa using h
  have hprev := st78_p39
  have hstep := st78_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p41 : ((786084444017/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT78 (i+1))
      = (∑ i ∈ Finset.range 40, stT78 (i+1)) + stT78 41 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 40
    simpa using h
  have hprev := st78_p40
  have hstep := st78_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p42 : ((1107088238097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT78 (i+1))
      = (∑ i ∈ Finset.range 41, stT78 (i+1)) + stT78 42 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 41
    simpa using h
  have hprev := st78_p41
  have hstep := st78_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p43 : ((471159939633/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT78 (i+1))
      = (∑ i ∈ Finset.range 42, stT78 (i+1)) + stT78 43 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 42
    simpa using h
  have hprev := st78_p42
  have hstep := st78_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p44 : ((12926767206089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT78 (i+1))
      = (∑ i ∈ Finset.range 43, stT78 (i+1)) + stT78 44 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 43
    simpa using h
  have hprev := st78_p43
  have hstep := st78_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p45 : ((470828980889/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT78 (i+1))
      = (∑ i ∈ Finset.range 44, stT78 (i+1)) + stT78 45 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 44
    simpa using h
  have hprev := st78_p44
  have hstep := st78_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p46 : ((2202566271693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT78 (i+1))
      = (∑ i ∈ Finset.range 45, stT78 (i+1)) + stT78 46 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 45
    simpa using h
  have hprev := st78_p45
  have hstep := st78_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p47 : ((192761115647/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT78 (i+1))
      = (∑ i ∈ Finset.range 46, stT78 (i+1)) + stT78 47 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 46
    simpa using h
  have hprev := st78_p46
  have hstep := st78_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p48 : ((12847477069283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT78 (i+1))
      = (∑ i ∈ Finset.range 47, stT78 (i+1)) + stT78 48 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 47
    simpa using h
  have hprev := st78_p47
  have hstep := st78_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p49 : ((11493276527603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT78 (i+1))
      = (∑ i ∈ Finset.range 48, stT78 (i+1)) + stT78 49 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 48
    simpa using h
  have hprev := st78_p48
  have hstep := st78_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p50 : ((11049367480929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT78 (i+1))
      = (∑ i ∈ Finset.range 49, stT78 (i+1)) + stT78 50 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 49
    simpa using h
  have hprev := st78_p49
  have hstep := st78_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p51 : ((12366864327609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT78 (i+1))
      = (∑ i ∈ Finset.range 50, stT78 (i+1)) + stT78 51 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 50
    simpa using h
  have hprev := st78_p50
  have hstep := st78_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p52 : ((12908879725359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT78 (i+1))
      = (∑ i ∈ Finset.range 51, stT78 (i+1)) + stT78 52 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 51
    simpa using h
  have hprev := st78_p51
  have hstep := st78_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p53 : ((11694673833629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT78 (i+1))
      = (∑ i ∈ Finset.range 52, stT78 (i+1)) + stT78 53 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 52
    simpa using h
  have hprev := st78_p52
  have hstep := st78_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p54 : ((10926832077941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT78 (i+1))
      = (∑ i ∈ Finset.range 53, stT78 (i+1)) + stT78 54 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 53
    simpa using h
  have hprev := st78_p53
  have hstep := st78_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p55 : ((372606336427/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT78 (i+1))
      = (∑ i ∈ Finset.range 54, stT78 (i+1)) + stT78 55 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 54
    simpa using h
  have hprev := st78_p54
  have hstep := st78_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p56 : ((3243431479651/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT78 (i+1))
      = (∑ i ∈ Finset.range 55, stT78 (i+1)) + stT78 56 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 55
    simpa using h
  have hprev := st78_p55
  have hstep := st78_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p57 : ((12366497738353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT78 (i+1))
      = (∑ i ∈ Finset.range 56, stT78 (i+1)) + stT78 57 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 56
    simpa using h
  have hprev := st78_p56
  have hstep := st78_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p58 : ((1387269958931/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT78 (i+1))
      = (∑ i ∈ Finset.range 57, stT78 (i+1)) + stT78 58 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 57
    simpa using h
  have hprev := st78_p57
  have hstep := st78_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p59 : ((11130012989611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT78 (i+1))
      = (∑ i ∈ Finset.range 58, stT78 (i+1)) + stT78 59 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 58
    simpa using h
  have hprev := st78_p58
  have hstep := st78_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p60 : ((12385362645271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT78 (i+1))
      = (∑ i ∈ Finset.range 59, stT78 (i+1)) + stT78 60 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 59
    simpa using h
  have hprev := st78_p59
  have hstep := st78_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p61 : ((520718572239/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT78 (i+1))
      = (∑ i ∈ Finset.range 60, stT78 (i+1)) + stT78 61 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 60
    simpa using h
  have hprev := st78_p60
  have hstep := st78_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p62 : ((12150836150421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT78 (i+1))
      = (∑ i ∈ Finset.range 61, stT78 (i+1)) + stT78 62 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 61
    simpa using h
  have hprev := st78_p61
  have hstep := st78_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p63 : ((11004911737203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT78 (i+1))
      = (∑ i ∈ Finset.range 62, stT78 (i+1)) + stT78 63 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 62
    simpa using h
  have hprev := st78_p62
  have hstep := st78_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p64 : ((11112584237203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT78 (i+1))
      = (∑ i ∈ Finset.range 63, stT78 (i+1)) + stT78 64 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 63
    simpa using h
  have hprev := st78_p63
  have hstep := st78_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p65 : ((12306204885019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT78 (i+1))
      = (∑ i ∈ Finset.range 64, stT78 (i+1)) + stT78 65 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 64
    simpa using h
  have hprev := st78_p64
  have hstep := st78_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p66 : ((13056071539249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT78 (i+1))
      = (∑ i ∈ Finset.range 65, stT78 (i+1)) + stT78 66 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 65
    simpa using h
  have hprev := st78_p65
  have hstep := st78_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p67 : ((3112815108561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT78 (i+1))
      = (∑ i ∈ Finset.range 66, stT78 (i+1)) + stT78 67 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 66
    simpa using h
  have hprev := st78_p66
  have hstep := st78_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p68 : ((11244900704513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT78 (i+1))
      = (∑ i ∈ Finset.range 67, stT78 (i+1)) + stT78 68 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 67
    simpa using h
  have hprev := st78_p67
  have hstep := st78_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p69 : ((10855348786139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT78 (i+1))
      = (∑ i ∈ Finset.range 68, stT78 (i+1)) + stT78 69 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 68
    simpa using h
  have hprev := st78_p68
  have hstep := st78_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p70 : ((468268961331/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT78 (i+1))
      = (∑ i ∈ Finset.range 69, stT78 (i+1)) + stT78 70 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 69
    simpa using h
  have hprev := st78_p69
  have hstep := st78_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p71 : ((801874949699/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT78 (i+1))
      = (∑ i ∈ Finset.range 70, stT78 (i+1)) + stT78 71 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 70
    simpa using h
  have hprev := st78_p70
  have hstep := st78_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p72 : ((13007693905253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT78 (i+1))
      = (∑ i ∈ Finset.range 71, stT78 (i+1)) + stT78 72 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 71
    simpa using h
  have hprev := st78_p71
  have hstep := st78_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p73 : ((12073291973817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT78 (i+1))
      = (∑ i ∈ Finset.range 72, stT78 (i+1)) + stT78 73 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 72
    simpa using h
  have hprev := st78_p72
  have hstep := st78_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p74 : ((11009393023417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT78 (i+1))
      = (∑ i ∈ Finset.range 73, stT78 (i+1)) + stT78 74 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 73
    simpa using h
  have hprev := st78_p73
  have hstep := st78_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p75 : ((5441927542699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT78 (i+1))
      = (∑ i ∈ Finset.range 74, stT78 (i+1)) + stT78 75 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 74
    simpa using h
  have hprev := st78_p74
  have hstep := st78_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p76 : ((5899678195223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT78 (i+1))
      = (∑ i ∈ Finset.range 75, stT78 (i+1)) + stT78 76 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 75
    simpa using h
  have hprev := st78_p75
  have hstep := st78_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p77 : ((12860514401061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT78 (i+1))
      = (∑ i ∈ Finset.range 76, stT78 (i+1)) + stT78 77 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 76
    simpa using h
  have hprev := st78_p76
  have hstep := st78_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p78 : ((163446253101/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT78 (i+1))
      = (∑ i ∈ Finset.range 77, stT78 (i+1)) + stT78 78 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 77
    simpa using h
  have hprev := st78_p77
  have hstep := st78_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p79 : ((766668123153/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT78 (i+1))
      = (∑ i ∈ Finset.range 78, stT78 (i+1)) + stT78 79 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 78
    simpa using h
  have hprev := st78_p78
  have hstep := st78_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p80 : ((1396725348897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT78 (i+1))
      = (∑ i ∈ Finset.range 79, stT78 (i+1)) + stT78 80 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 79
    simpa using h
  have hprev := st78_p79
  have hstep := st78_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p81 : ((67201452837/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT78 (i+1))
      = (∑ i ∈ Finset.range 80, stT78 (i+1)) + stT78 81 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 80
    simpa using h
  have hprev := st78_p80
  have hstep := st78_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p82 : ((2269240526553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT78 (i+1))
      = (∑ i ∈ Finset.range 81, stT78 (i+1)) + stT78 82 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 81
    simpa using h
  have hprev := st78_p81
  have hstep := st78_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p83 : ((497679365183/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT78 (i+1))
      = (∑ i ∈ Finset.range 82, stT78 (i+1)) + stT78 83 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 82
    simpa using h
  have hprev := st78_p82
  have hstep := st78_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p84 : ((328495707191/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT78 (i+1))
      = (∑ i ∈ Finset.range 83, stT78 (i+1)) + stT78 84 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 83
    simpa using h
  have hprev := st78_p83
  have hstep := st78_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p85 : ((3223371559223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT78 (i+1))
      = (∑ i ∈ Finset.range 84, stT78 (i+1)) + stT78 85 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 84
    simpa using h
  have hprev := st78_p84
  have hstep := st78_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p86 : ((2978254664887/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT78 (i+1))
      = (∑ i ∈ Finset.range 85, stT78 (i+1)) + stT78 86 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 85
    simpa using h
  have hprev := st78_p85
  have hstep := st78_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p87 : ((10958223768799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT78 (i+1))
      = (∑ i ∈ Finset.range 86, stT78 (i+1)) + stT78 87 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 86
    simpa using h
  have hprev := st78_p86
  have hstep := st78_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p88 : ((10739022432283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT78 (i+1))
      = (∑ i ∈ Finset.range 87, stT78 (i+1)) + stT78 88 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 87
    simpa using h
  have hprev := st78_p87
  have hstep := st78_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p89 : ((11400787039359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT78 (i+1))
      = (∑ i ∈ Finset.range 88, stT78 (i+1)) + stT78 89 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 88
    simpa using h
  have hprev := st78_p88
  have hstep := st78_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p90 : ((2490899491611/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT78 (i+1))
      = (∑ i ∈ Finset.range 89, stT78 (i+1)) + stT78 90 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 89
    simpa using h
  have hprev := st78_p89
  have hstep := st78_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p91 : ((526261539771/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT78 (i+1))
      = (∑ i ∈ Finset.range 90, stT78 (i+1)) + stT78 91 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 90
    simpa using h
  have hprev := st78_p90
  have hstep := st78_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p92 : ((13033137468849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT78 (i+1))
      = (∑ i ∈ Finset.range 91, stT78 (i+1)) + stT78 92 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 91
    simpa using h
  have hprev := st78_p91
  have hstep := st78_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p93 : ((12182529891057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT78 (i+1))
      = (∑ i ∈ Finset.range 92, stT78 (i+1)) + stT78 93 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 92
    simpa using h
  have hprev := st78_p92
  have hstep := st78_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p94 : ((11177118291053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT78 (i+1))
      = (∑ i ∈ Finset.range 93, stT78 (i+1)) + stT78 94 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 93
    simpa using h
  have hprev := st78_p93
  have hstep := st78_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p95 : ((10667175948683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT78 (i+1))
      = (∑ i ∈ Finset.range 94, stT78 (i+1)) + stT78 95 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 94
    simpa using h
  have hprev := st78_p94
  have hstep := st78_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p96 : ((10965467452983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT78 (i+1))
      = (∑ i ∈ Finset.range 95, stT78 (i+1)) + stT78 96 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 95
    simpa using h
  have hprev := st78_p95
  have hstep := st78_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p97 : ((11872566400577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT78 (i+1))
      = (∑ i ∈ Finset.range 96, stT78 (i+1)) + stT78 97 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 96
    simpa using h
  have hprev := st78_p96
  have hstep := st78_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p98 : ((12826794365553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT78 (i+1))
      = (∑ i ∈ Finset.range 97, stT78 (i+1)) + stT78 98 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 97
    simpa using h
  have hprev := st78_p97
  have hstep := st78_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p99 : ((13259149222509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT78 (i+1))
      = (∑ i ∈ Finset.range 98, stT78 (i+1)) + stT78 99 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 98
    simpa using h
  have hprev := st78_p98
  have hstep := st78_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st78_p100 : ((12926395222509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT78 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT78 (i+1))
      = (∑ i ∈ Finset.range 99, stT78 (i+1)) + stT78 100 := by
    have h := Finset.sum_range_succ (fun i => stT78 (i+1)) 99
    simpa using h
  have hprev := st78_p99
  have hstep := st78_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 78`.** -/
theorem station_78_sign : hardyG (((78:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 78 100 (by norm_num) (by norm_num)
    ((-424127/500000 : ℚ) : ℝ)
  have hchain := st78_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT78 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((78:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-424127/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((78:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((78:ℕ)):ℝ)+1) * ((((78:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((277981/390000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((12926395222509/10000000000000 : ℚ) : ℝ) - ((277981/390000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-424127/500000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((78:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-424127/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((78:ℕ)):ℝ))).re
      - Real.sin ((-424127/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((78:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((78:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((78:ℕ)):ℝ)
      = ((((78:ℕ)):ℝ) * (Real.log (((78:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((78:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_78
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
  have hθwin : |(((-424127/500000 : ℚ) : ℝ) + ((10:ℤ)) * (2*Real.pi) - Real.pi) - theta (((78:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((78:ℕ)):ℝ))
    (φ := ((-424127/500000 : ℚ) : ℝ) + ((10:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-424127/500000 : ℚ) : ℝ) + ((10:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-424127/500000 : ℚ)) : ℝ) - Real.pi) + ((10:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-424127/500000 : ℚ)) : ℝ) - Real.pi) 10).1,
    (cos_sin_shift ((((-424127/500000 : ℚ)) : ℝ) - Real.pi) 10).2]
  exact cos_sin_flip ((-424127/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_78_sign
end AxiomAudit
